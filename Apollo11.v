From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.

Import ListNotations.

(**
  This file establishes the first shared vocabulary for the Apollo 11
  formalization.  The immediate goal is not to encode the entire AGC
  instruction set in one shot, but to carve out the stable semantic axes that
  recur across the referent source tree:

  - the two Apollo 11 mission builds, `Luminary099` and `Comanche055`
  - the vehicle split between Lunar Module and Command Module
  - executive scheduling concepts from files such as `EXECUTIVE.agc`,
    `WAITLIST.agc`, and `FRESH_START_AND_RESTART.agc`
  - alarm flow from `ALARM_AND_ABORT.agc`
  - guidance-phase structure for LM descent and CM entry paths

  The types below are intentionally small and heavily commented so that later
  semantic refinements can preserve names and proof structure while replacing
  coarse booleans with richer executable models.
*)

(** The Apollo 11 software is split across the two spacecraft. *)
Inductive vehicle : Type :=
| CommandModule
| LunarModule.

(**
  The referent repository exposes two top-level mission programs for Apollo 11.
  `Comanche055` is the CM build and `Luminary099` is the LM build.
*)
Inductive agc_program : Type :=
| Comanche055
| Luminary099.

(** This is the direct mission-program-to-vehicle assignment from the source. *)
Definition vehicle_of_program (program : agc_program) : vehicle :=
  match program with
  | Comanche055 => CommandModule
  | Luminary099 => LunarModule
  end.

(**
  Mission phases are chosen to align with the major operational partitions named
  by the Apollo 11 source comments.  The LM descent phases follow the landing
  stack around `P63`, `P64`, `P65`, `P66`, and `P67`.  The CM path includes
  entry and reentry control.
*)
Inductive mission_phase : Type :=
| EarthOrbit
| TranslunarCoast
| LunarOrbit
| PoweredDescentBraking
| PoweredDescentApproach
| PoweredDescentVertical
| LunarSurface
| Ascent
| Rendezvous
| TransearthCoast
| Entry
| SplashdownRecovery.

(**
  These subsystems are named after major source files or source clusters in the
  Apollo 11 repository.  The set is intentionally selective: it captures the
  execution and guidance surfaces that the first proofs will touch, without yet
  modeling every assembly file as its own semantic unit.
*)
Inductive subsystem : Type :=
| ExecutiveCore
| WaitlistScheduler
| FreshStartAndRestart
| AlarmAndAbort
| DisplayInterface
| InterpreterCore
| LunarLanding
| LunarLandingGuidance
| ThrottleControl
| AscentGuidance
| CmEntryDigitalAutopilot
| ReentryControl.

(**
  A subsystem may be shared between both builds, or owned by one mission build.
  This lets the first well-formedness predicate reject obviously impossible
  pairings, such as assigning the LM landing guidance equations to Comanche.
*)
Inductive subsystem_scope : Type :=
| SharedScope
| ComancheScope
| LuminaryScope.

(** Scope classification derived from the referent source layout. *)
Definition subsystem_scope_of (s : subsystem) : subsystem_scope :=
  match s with
  | ExecutiveCore => SharedScope
  | WaitlistScheduler => SharedScope
  | FreshStartAndRestart => SharedScope
  | AlarmAndAbort => SharedScope
  | DisplayInterface => SharedScope
  | InterpreterCore => SharedScope
  | LunarLanding => LuminaryScope
  | LunarLandingGuidance => LuminaryScope
  | ThrottleControl => LuminaryScope
  | AscentGuidance => LuminaryScope
  | CmEntryDigitalAutopilot => ComancheScope
  | ReentryControl => ComancheScope
  end.

(**
  Apollo source comments and later literature emphasize a handful of alarms.
  We begin with the best-known codes and leave room for extension.
*)
Inductive alarm_code : Type :=
| Alarm1201
| Alarm1202
| Alarm1406
| AlarmOther (code : nat).

(**
  Jobs are represented minimally for now.  The priority field is retained
  because the executive logic in the referent repository is explicitly phrased
  in terms of priority arbitration and job suspension.
*)
Record job : Type := {
  job_subsystem : subsystem;
  job_priority : nat
}.

(**
  The initial machine state is intentionally abstract.  Each field corresponds
  to a proof surface we expect to formalize next:

  - `state_program` and `state_phase` anchor mission-level invariants
  - `state_active` tracks the currently executing subsystem
  - `state_queue` approximates the executive job queue
  - `state_alarms` records pending alarms
  - `state_display_locked` approximates DSKY display ownership
  - `state_restart_pending` tracks restart flow
*)
Record agc_state : Type := {
  state_program : agc_program;
  state_phase : mission_phase;
  state_active : subsystem;
  state_queue : list job;
  state_alarms : list alarm_code;
  state_display_locked : bool;
  state_restart_pending : bool
}.

(**
  Not every mission phase is legal for every program.  This first filter keeps
  the program/phase relation aligned with the spacecraft split before we model
  any concrete state transitions.
*)
Definition program_supports_phase
    (program : agc_program) (phase : mission_phase) : bool :=
  match program with
  | Luminary099 =>
      match phase with
      | EarthOrbit
      | TranslunarCoast
      | LunarOrbit
      | PoweredDescentBraking
      | PoweredDescentApproach
      | PoweredDescentVertical
      | LunarSurface
      | Ascent
      | Rendezvous => true
      | TransearthCoast
      | Entry
      | SplashdownRecovery => false
      end
  | Comanche055 =>
      match phase with
      | EarthOrbit
      | TranslunarCoast
      | LunarOrbit
      | Rendezvous
      | TransearthCoast
      | Entry
      | SplashdownRecovery => true
      | PoweredDescentBraking
      | PoweredDescentApproach
      | PoweredDescentVertical
      | LunarSurface
      | Ascent => false
      end
  end.

(**
  Shared subsystems may appear under either build.  LM-only and CM-only
  subsystems are restricted to their owning mission program.
*)
Definition subsystem_allowed
    (program : agc_program) (s : subsystem) : bool :=
  match subsystem_scope_of s with
  | SharedScope => true
  | LuminaryScope =>
      match program with
      | Luminary099 => true
      | Comanche055 => false
      end
  | ComancheScope =>
      match program with
      | Luminary099 => false
      | Comanche055 => true
      end
  end.

(** A state is structurally well-formed when its phase and active subsystem fit. *)
Definition well_formed_state (st : agc_state) : Prop :=
  program_supports_phase (state_program st) (state_phase st) = true /\
  subsystem_allowed (state_program st) (state_active st) = true.

(**
  The queue discipline itself will be refined later.  For now, we expose a
  simple predicate that says whether the machine is currently alarm-free.
*)
Definition alarm_free (st : agc_state) : Prop :=
  state_alarms st = [].

(** Canonical initial LM state for the first landing-side development. *)
Definition luminary_boot_state : agc_state :=
  {|
    state_program := Luminary099;
    state_phase := LunarOrbit;
    state_active := ExecutiveCore;
    state_queue := [];
    state_alarms := [];
    state_display_locked := false;
    state_restart_pending := false
  |}.

(** Canonical initial CM state for entry-side and rendezvous-side development. *)
Definition comanche_boot_state : agc_state :=
  {|
    state_program := Comanche055;
    state_phase := TranslunarCoast;
    state_active := ExecutiveCore;
    state_queue := [];
    state_alarms := [];
    state_display_locked := false;
    state_restart_pending := false
  |}.

(**
  The first lemmas are deliberately small.  They pin down the coarse structure
  so that later semantic extensions can refactor internally without changing the
  public statements that describe what Apollo 11 software belongs where.
*)
Lemma vehicle_of_program_comanche :
  vehicle_of_program Comanche055 = CommandModule.
Proof.
  reflexivity.
Qed.

Lemma vehicle_of_program_luminary :
  vehicle_of_program Luminary099 = LunarModule.
Proof.
  reflexivity.
Qed.

Lemma luminary_boot_state_well_formed :
  well_formed_state luminary_boot_state.
Proof.
  split; reflexivity.
Qed.

Lemma comanche_boot_state_well_formed :
  well_formed_state comanche_boot_state.
Proof.
  split; reflexivity.
Qed.

Lemma luminary_boot_state_alarm_free :
  alarm_free luminary_boot_state.
Proof.
  reflexivity.
Qed.

Lemma comanche_boot_state_alarm_free :
  alarm_free comanche_boot_state.
Proof.
  reflexivity.
Qed.

(**
  The next milestone is a small-step relation over `agc_state` that can express
  scheduler progress, alarm injection, restart entry, and phase transitions.
  Once that relation exists, the subsystem and phase vocabularies defined here
  can support stronger theorems that reference concrete traces from the Apollo
  11 mission software.
*)
