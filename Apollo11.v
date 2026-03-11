From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Lia.

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
  job_ticket : nat;
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
  The next sections stop being mere scaffolding.  They carve out two concrete,
  source-driven semantics slices:

  - the executive priority discipline that appears in `EXECUTIVE.agc`
  - the LM vertical-mode controller around GUILDENSTERN in
    `LUNAR_LANDING_GUIDANCE_EQUATIONS.agc`
*)

(** * Executive Queue Model *)

(**
  The Apollo 11 executive comments revolve around priority comparisons,
  sleeping jobs, waking jobs, and dispatching the highest-priority runnable
  task.  We model the ready queue as a descending list by priority.  This
  abstracts away the AGC's concrete core-set registers while preserving the
  ordering property the executive actually reasons about.
*)
Definition priority_order (left right : job) : Prop :=
  job_priority left >= job_priority right.

(**
  `StronglySorted` is the right invariant here: every job in the tail must have
  priority no greater than the head, not just the next immediate element.
*)
Definition ready_queue_ok (queue : list job) : Prop :=
  StronglySorted priority_order queue.

(**
  The executive's `NOVAC`, `FINDVAC`, and `JOBWAKE` paths all converge on the
  same abstract effect at the queue level: a job becomes runnable and must be
  inserted into the ready queue at the position dictated by priority.
*)
Fixpoint insert_job_by_priority (new_job : job) (queue : list job) : list job :=
  match queue with
  | [] => [new_job]
  | head :: tail =>
      if Nat.leb (job_priority head) (job_priority new_job)
      then new_job :: head :: tail
      else head :: insert_job_by_priority new_job tail
  end.

(** Submitting a runnable job is just priority insertion. *)
Definition submit_job (new_job : job) (queue : list job) : list job :=
  insert_job_by_priority new_job queue.

(**
  Waking a sleeping job is the same abstract operation as submission.  The
  difference in the AGC source is where the job comes from, not where it lands.
*)
Definition wake_job (awakened_job : job) (queue : list job) : list job :=
  insert_job_by_priority awakened_job queue.

(** Dispatch selects the first runnable job in the sorted ready queue. *)
Definition dispatch (queue : list job) : option job :=
  hd_error queue.

(**
  Insertion preserves membership in the obvious way: the result contains the
  new job together with every old job, and nothing else.
*)
Lemma in_insert_job_by_priority :
  forall (new_job item : job) (queue : list job),
    In item (insert_job_by_priority new_job queue) <->
    item = new_job \/ In item queue.
Proof.
  intros new_job item queue.
  induction queue as [| head tail IH]; simpl.
  - split.
    + intros HIn.
      destruct HIn as [HIn | []].
      left; symmetry; exact HIn.
    + intros [Hnew | Hold].
      * subst item. left. reflexivity.
      * contradiction.
  - destruct (Nat.leb (job_priority head) (job_priority new_job)) eqn:Hcompare.
    + split.
      * intros HIn.
        destruct HIn as [HIn | [HIn | HIn]].
        -- left; symmetry; exact HIn.
        -- right. left. exact HIn.
        -- right. right. exact HIn.
      * intros [Hnew | [Hold | Hold]].
        -- subst item. left. reflexivity.
        -- right. left. exact Hold.
        -- right. right. exact Hold.
    + split.
      * intros HIn.
        destruct HIn as [HIn | HIn].
        -- right. left. exact HIn.
        -- rewrite IH in HIn.
           destruct HIn as [Hnew | Hold].
           ++ left. exact Hnew.
           ++ right. right. exact Hold.
      * intros [Hnew | [Hold | Hold]].
        -- subst item. right. rewrite IH. left. reflexivity.
        -- left. exact Hold.
        -- right. rewrite IH. right. exact Hold.
Qed.

(**
  If one job dominates another in priority, and the second job dominates every
  element of a list, then the first job also dominates every element of that
  list.  This is the monotonicity step used when a newly submitted high-priority
  job is inserted at the head of the queue.
*)
Lemma forall_priority_order_monotone :
  forall (upper lower : job) (queue : list job),
    priority_order upper lower ->
    Forall (priority_order lower) queue ->
    Forall (priority_order upper) queue.
Proof.
  intros upper lower queue Hupper Hforall.
  induction Hforall as [| item tail Hitem Htail IH].
  - constructor.
  - constructor.
    + unfold priority_order in *.
      lia.
    + exact IH.
Qed.

(**
  If a queue head already dominates the old queue and also dominates the new
  job, then it will dominate the queue after insertion as well.
*)
Lemma head_dominates_inserted_queue :
  forall (head new_job : job) (queue : list job),
    priority_order head new_job ->
    Forall (priority_order head) queue ->
    Forall (priority_order head) (insert_job_by_priority new_job queue).
Proof.
  intros head new_job queue Hhead_new Hforall.
  induction queue as [| item tail IH]; simpl.
  - constructor.
    + exact Hhead_new.
    + constructor.
  - inversion Hforall as [| dominated_item dominated_tail Hhead_item Hhead_tail];
      subst dominated_item dominated_tail.
    destruct (Nat.leb (job_priority item) (job_priority new_job)) eqn:Hcompare.
    + constructor.
      * exact Hhead_new.
      * constructor.
        -- exact Hhead_item.
        -- exact Hhead_tail.
    + constructor.
      * exact Hhead_item.
      * apply IH.
        exact Hhead_tail.
Qed.

(**
  This is the core executive theorem for the queue model: once the ready queue
  is strongly sorted by priority, `NOVAC`/`FINDVAC`/`JOBWAKE` insertion keeps it
  strongly sorted.  That makes the dispatch rule semantically stable.
*)
Lemma insert_job_by_priority_preserves_ready_queue :
  forall (new_job : job) (queue : list job),
    ready_queue_ok queue ->
    ready_queue_ok (insert_job_by_priority new_job queue).
Proof.
  intros new_job queue Hsorted.
  unfold ready_queue_ok in *.
  induction Hsorted as [| head tail Hsorted_tail IH Hhead_tail]; simpl.
  - apply SSorted_cons.
    + constructor.
    + constructor.
  - destruct (Nat.leb (job_priority head) (job_priority new_job)) eqn:Hcompare.
    + apply Nat.leb_le in Hcompare.
      apply SSorted_cons.
      * apply SSorted_cons.
        -- exact Hsorted_tail.
        -- exact Hhead_tail.
      * constructor.
        -- unfold priority_order.
           lia.
        -- apply forall_priority_order_monotone with (lower := head).
           ++ unfold priority_order.
              lia.
           ++ exact Hhead_tail.
    + apply Nat.leb_gt in Hcompare.
      apply SSorted_cons.
      * exact IH.
      * apply head_dominates_inserted_queue.
        -- unfold priority_order.
           lia.
        -- exact Hhead_tail.
Qed.

(** Submission preserves the executive ready-queue invariant. *)
Lemma submit_job_preserves_ready_queue :
  forall (new_job : job) (queue : list job),
    ready_queue_ok queue ->
    ready_queue_ok (submit_job new_job queue).
Proof.
  intros new_job queue Hready.
  exact (insert_job_by_priority_preserves_ready_queue new_job queue Hready).
Qed.

(** Waking a sleeping job preserves the same invariant for the same reason. *)
Lemma wake_job_preserves_ready_queue :
  forall (awakened_job : job) (queue : list job),
    ready_queue_ok queue ->
    ready_queue_ok (wake_job awakened_job queue).
Proof.
  intros awakened_job queue Hready.
  exact (insert_job_by_priority_preserves_ready_queue awakened_job queue Hready).
Qed.

(**
  A strongly sorted queue guarantees that every tail element has priority no
  greater than the head.  This is the formal payload behind the executive
  comment that scans for the highest-priority active job.
*)
Lemma ready_queue_head_has_highest_priority :
  forall (head : job) (tail : list job),
    ready_queue_ok (head :: tail) ->
    Forall (fun queued_job => job_priority queued_job <= job_priority head) tail.
Proof.
  intros head tail Hready.
  unfold ready_queue_ok in Hready.
  apply StronglySorted_inv in Hready.
  destruct Hready as [_ Hhead_tail].
  apply Forall_forall.
  intros queued_job HIn.
  apply Forall_forall with (x := queued_job) in Hhead_tail; [| exact HIn].
  unfold priority_order in Hhead_tail.
  lia.
Qed.

(**
  After a submission, dispatch returns a runnable job whose priority dominates
  the entire ready queue.  This is the first genuinely mission-relevant queue
  property, not just a structural lemma.
*)
Lemma dispatch_after_submit_returns_maximal_job :
  forall (new_job chosen_job : job) (queue : list job),
    ready_queue_ok queue ->
    dispatch (submit_job new_job queue) = Some chosen_job ->
    Forall
      (fun queued_job => job_priority queued_job <= job_priority chosen_job)
      (submit_job new_job queue).
Proof.
  intros new_job chosen_job queue Hready Hdispatch.
  unfold dispatch, submit_job in Hdispatch.
  remember (insert_job_by_priority new_job queue) as ready_after_submit.
  destruct ready_after_submit as [| head tail].
  - discriminate Hdispatch.
  - inversion Hdispatch; subst.
    unfold submit_job.
    rewrite <- Heqready_after_submit.
    constructor.
    + lia.
    + apply ready_queue_head_has_highest_priority.
      rewrite Heqready_after_submit.
      apply insert_job_by_priority_preserves_ready_queue.
      exact Hready.
Qed.

(** * Luminary Vertical-Mode Controller *)

(**
  The Luminary landing software distinguishes the three vertical-phase programs
  `P65`, `P66`, and `P67`.  The GUILDENSTERN comments describe precisely how
  manual throttle and attitude/rod inputs drive transitions among them.
*)
Inductive vertical_program : Type :=
| P65
| P66
| P67.

(**
  These booleans track the discrete signals named in the comments:

  - `manual_throttle_active` corresponds to the manual throttle discrete
  - `attitude_hold_active` corresponds to the attitude-hold discrete
  - `rod_switch_clicked` captures the rate-of-descent switch click
*)
Record guildenstern_inputs : Type := {
  manual_throttle_active : bool;
  attitude_hold_active : bool;
  rod_switch_clicked : bool
}.

(**
  This function is a direct semantic reading of the source comments around
  GUILDENSTERN:

  - manual throttle present selects `P67`
  - manual throttle released from `P67` selects `P66`
  - attitude-hold or a rod click while in `P65` selects `P66`
  - `P66` remains in rate-of-descent mode until some stronger override occurs
*)
Definition guildenstern_next_program
    (current : vertical_program) (inputs : guildenstern_inputs)
    : vertical_program :=
  if manual_throttle_active inputs then P67
  else
    match current with
    | P67 => P66
    | P66 => P66
    | P65 =>
        if orb (attitude_hold_active inputs) (rod_switch_clicked inputs)
        then P66
        else P65
    end.

(**
  The higher-level landing progression from `P63` to `P64` to `P65` is also
  explicit in the source's phase tables.  We model just that progression here,
  leaving the rest of the descent semantics to later files.
*)
Inductive landing_program : Type :=
| P63
| P64
| VerticalProgram (vertical_mode : vertical_program).

(** The source comments distinguish braking, approach, and vertical phases. *)
Definition landing_phase_of_program (program : landing_program) : mission_phase :=
  match program with
  | P63 => PoweredDescentBraking
  | P64 => PoweredDescentApproach
  | VerticalProgram _ => PoweredDescentVertical
  end.

(**
  `STARTP64` and `P65START` form the explicit phase-advance points from the
  Apollo 11 source.  Once the descent is already vertical, this simplified
  model leaves the phase unchanged.
*)
Definition advance_landing_program (program : landing_program) : landing_program :=
  match program with
  | P63 => P64
  | P64 => VerticalProgram P65
  | VerticalProgram current => VerticalProgram current
  end.

(**
  GUILDENSTERN only changes the vertical-mode subprogram.  Braking and approach
  remain untouched until the phase tables advance them.
*)
Definition apply_guildenstern
    (program : landing_program) (inputs : guildenstern_inputs)
    : landing_program :=
  match program with
  | P63 => P63
  | P64 => P64
  | VerticalProgram current =>
      VerticalProgram (guildenstern_next_program current inputs)
  end.

(**
  TTF alarm handling is phase-specific in the source tables: the `1406` alarm
  hook is attached to braking and approach, not to the vertical controller.
*)
Definition inject_ttf_alarm
    (program : landing_program) (alarms : list alarm_code)
    : list alarm_code :=
  match program with
  | P63 => Alarm1406 :: alarms
  | P64 => Alarm1406 :: alarms
  | VerticalProgram _ => alarms
  end.

(** Manual throttle immediately forces the manual-throttle program `P67`. *)
Lemma manual_throttle_forces_p67 :
  forall (current : vertical_program) (inputs : guildenstern_inputs),
    manual_throttle_active inputs = true ->
    guildenstern_next_program current inputs = P67.
Proof.
  intros current inputs Hmanual.
  unfold guildenstern_next_program.
  rewrite Hmanual.
  reflexivity.
Qed.

(**
  The source comment says that disappearance of the manual-throttle discrete
  selects `P66`.  We formalize that at the point where the current vertical mode
  is `P67` and manual throttle is no longer active.
*)
Lemma manual_throttle_release_from_p67_selects_p66 :
  forall (inputs : guildenstern_inputs),
    manual_throttle_active inputs = false ->
    guildenstern_next_program P67 inputs = P66.
Proof.
  intros inputs Hmanual.
  unfold guildenstern_next_program.
  rewrite Hmanual.
  reflexivity.
Qed.

(**
  A rod click or attitude-hold discrete while still in `P65` forces a switch
  into `P66`, the rate-of-descent mode.
*)
Lemma p65_override_selects_p66 :
  forall (inputs : guildenstern_inputs),
    manual_throttle_active inputs = false ->
    orb (attitude_hold_active inputs) (rod_switch_clicked inputs) = true ->
    guildenstern_next_program P65 inputs = P66.
Proof.
  intros inputs Hmanual Hoverride.
  unfold guildenstern_next_program.
  rewrite Hmanual.
  rewrite Hoverride.
  reflexivity.
Qed.

(**
  GUILDENSTERN is phase-preserving.  It changes only the vertical controller
  submode and never moves the landing software back into braking or approach.
*)
Lemma apply_guildenstern_preserves_landing_phase :
  forall (program : landing_program) (inputs : guildenstern_inputs),
    landing_phase_of_program (apply_guildenstern program inputs) =
    landing_phase_of_program program.
Proof.
  intros program inputs.
  destruct program as [| | current]; reflexivity.
Qed.

(**
  The phase-advance table is monotone: it can move braking to approach, or
  approach to vertical, but it cannot retreat to an earlier phase.
*)
Definition landing_phase_rank (phase : mission_phase) : nat :=
  match phase with
  | PoweredDescentBraking => 0
  | PoweredDescentApproach => 1
  | PoweredDescentVertical => 2
  | _ => 3
  end.

Lemma advance_landing_program_is_monotone :
  forall (program : landing_program),
    landing_phase_rank (landing_phase_of_program program) <=
    landing_phase_rank (landing_phase_of_program (advance_landing_program program)).
Proof.
  intros program.
  destruct program as [| | current]; simpl; lia.
Qed.

(**
  The source tables attach the `1406` TTF alarm only to braking and approach.
  Therefore once the landing software is already vertical, TTF alarm injection
  leaves the alarm list unchanged.
*)
Lemma inject_ttf_alarm_is_inactive_in_vertical_phase :
  forall (vertical_mode : vertical_program) (alarms : list alarm_code),
    inject_ttf_alarm (VerticalProgram vertical_mode) alarms = alarms.
Proof.
  intros vertical_mode alarms.
  reflexivity.
Qed.

(**
  Putting the two phase tables together yields a concrete descent fact: two
  explicit phase-advance steps from `P63` land exactly in the vertical controller
  at `P65`, matching the transition structure named by `STARTP64` and
  `P65START`.
*)
Lemma two_phase_advances_from_p63_enter_vertical_p65 :
  advance_landing_program (advance_landing_program P63) = VerticalProgram P65.
Proof.
  reflexivity.
Qed.

(** * Alarm Register Model *)

(**
  The Apollo 11 alarm handler does not maintain an unbounded list.  It probes
  `FAILREG`, then `FAILREG + 1`, then `FAILREG + 2`, and if all three are
  occupied it records overflow information in the final register while leaving
  the earlier slots intact.  We model that fixed-capacity structure directly.
*)
Record fail_registers : Type := {
  failreg_1 : option alarm_code;
  failreg_2 : option alarm_code;
  failreg_3 : option alarm_code;
  failreg_overflow : bool;
  program_alarm_light : bool
}.

(** Empty alarm state before any non-abortive alarm has been recorded. *)
Definition empty_fail_registers : fail_registers :=
  {|
    failreg_1 := None;
    failreg_2 := None;
    failreg_3 := None;
    failreg_overflow := false;
    program_alarm_light := false
  |}.

(** Count the number of occupied alarm slots. *)
Definition slot_count (slot : option alarm_code) : nat :=
  match slot with
  | None => 0
  | Some _ => 1
  end.

Definition occupied_fail_slots (registers : fail_registers) : nat :=
  slot_count (failreg_1 registers) +
  slot_count (failreg_2 registers) +
  slot_count (failreg_3 registers).

(** All three fixed alarm slots are in use. *)
Definition fail_registers_full (registers : fail_registers) : Prop :=
  occupied_fail_slots registers = 3.

(**
  This is the executable non-abortive alarm insertion policy from the source:

  - if `FAILREG` is empty, store there and turn on the program alarm light
  - else if `FAILREG + 1` is empty, store there
  - else if `FAILREG + 2` is empty, store there
  - else preserve the slots and set the overflow bit
*)
Definition record_alarm
    (code : alarm_code) (registers : fail_registers) : fail_registers :=
  match failreg_1 registers with
  | None =>
      {|
        failreg_1 := Some code;
        failreg_2 := failreg_2 registers;
        failreg_3 := failreg_3 registers;
        failreg_overflow := failreg_overflow registers;
        program_alarm_light := true
      |}
  | Some _ =>
      match failreg_2 registers with
      | None =>
          {|
            failreg_1 := failreg_1 registers;
            failreg_2 := Some code;
            failreg_3 := failreg_3 registers;
            failreg_overflow := failreg_overflow registers;
            program_alarm_light := true
          |}
      | Some _ =>
          match failreg_3 registers with
          | None =>
              {|
                failreg_1 := failreg_1 registers;
                failreg_2 := failreg_2 registers;
                failreg_3 := Some code;
                failreg_overflow := failreg_overflow registers;
                program_alarm_light := true
              |}
          | Some _ =>
              {|
                failreg_1 := failreg_1 registers;
                failreg_2 := failreg_2 registers;
                failreg_3 := failreg_3 registers;
                failreg_overflow := true;
                program_alarm_light := true
              |}
          end
      end
  end.

(** Once an alarm is recorded, the program alarm light is on. *)
Lemma record_alarm_turns_on_program_alarm_light :
  forall (code : alarm_code) (registers : fail_registers),
    program_alarm_light (record_alarm code registers) = true.
Proof.
  intros code registers.
  unfold record_alarm.
  destruct (failreg_1 registers) as [slot1 |];
    destruct (failreg_2 registers) as [slot2 |];
    destruct (failreg_3 registers) as [slot3 |];
    reflexivity.
Qed.

(**
  Recording an alarm can never create more than three occupied slots, because
  the underlying machine only has three fail registers.
*)
Lemma occupied_fail_slots_le_3 :
  forall (registers : fail_registers),
    occupied_fail_slots registers <= 3.
Proof.
  intros registers.
  unfold occupied_fail_slots, slot_count.
  destruct (failreg_1 registers), (failreg_2 registers), (failreg_3 registers);
    simpl; lia.
Qed.

(**
  Recording an alarm preserves the global capacity bound.  This is the first
  real safety property for the fail-register subsystem.
*)
Lemma record_alarm_preserves_capacity :
  forall (code : alarm_code) (registers : fail_registers),
    occupied_fail_slots (record_alarm code registers) <= 3.
Proof.
  intros code registers.
  apply occupied_fail_slots_le_3.
Qed.

(**
  If there is at least one free slot, recording an alarm consumes exactly one
  slot.  This matches the sequential search through `FAILREG`, `FAILREG+1`, and
  `FAILREG+2` in the source.
*)
Lemma record_alarm_increases_occupied_slots_when_not_full :
  forall (code : alarm_code) (registers : fail_registers),
    occupied_fail_slots registers < 3 ->
    occupied_fail_slots (record_alarm code registers) =
    S (occupied_fail_slots registers).
Proof.
  intros code registers Hnot_full.
  unfold occupied_fail_slots, slot_count in *.
  unfold record_alarm.
  destruct (failreg_1 registers) as [slot1 |];
    destruct (failreg_2 registers) as [slot2 |];
    destruct (failreg_3 registers) as [slot3 |];
    simpl in *; lia.
Qed.

(**
  If all fail registers are already occupied, a new alarm cannot consume a new
  slot.  The concrete handler instead sets overflow state in the third register.
*)
Lemma record_alarm_sets_overflow_when_full :
  forall (code : alarm_code) (registers : fail_registers),
    fail_registers_full registers ->
    failreg_overflow (record_alarm code registers) = true /\
    occupied_fail_slots (record_alarm code registers) =
    occupied_fail_slots registers.
Proof.
  intros code [slot1 slot2 slot3 overflow light] Hfull.
  unfold fail_registers_full in Hfull.
  unfold occupied_fail_slots, slot_count in Hfull.
  unfold record_alarm.
  simpl in *.
  destruct slot1 as [alarm1 |];
    destruct slot2 as [alarm2 |];
    destruct slot3 as [alarm3 |];
    simpl in *; try lia.
  split; reflexivity.
Qed.

(**
  Before the fail registers are full, overflow is not introduced by recording a
  new non-abortive alarm.  This matches the source's control flow, which only
  reaches `MULTFAIL` after all three slots are already occupied.
*)
Lemma record_alarm_preserves_non_overflow_when_not_full :
  forall (code : alarm_code) (registers : fail_registers),
    occupied_fail_slots registers < 3 ->
    failreg_overflow (record_alarm code registers) = failreg_overflow registers.
Proof.
  intros code registers Hnot_full.
  unfold occupied_fail_slots, slot_count in Hnot_full.
  unfold record_alarm.
  destruct (failreg_1 registers) as [slot1 |];
    destruct (failreg_2 registers) as [slot2 |];
    destruct (failreg_3 registers) as [slot3 |];
    simpl in *; try lia; reflexivity.
Qed.

(**
  The first alarm lands in `FAILREG`, just as the source takes the `PROGLARM`
  path immediately when the first register is empty.
*)
Lemma first_alarm_occupies_failreg_1 :
  forall (code : alarm_code),
    failreg_1 (record_alarm code empty_fail_registers) = Some code /\
    occupied_fail_slots (record_alarm code empty_fail_registers) = 1.
Proof.
  intros code.
  split; reflexivity.
Qed.

(** * Composed LM Descent Control State *)

(**
  To move beyond isolated subsystems, we compose the landing-mode controller,
  executive ready queue, and fail-register alarms into a single LM descent
  control state.  This is still far from the full AGC machine, but it is an
  honest operational interface between multiple source-grounded components.
*)
Record lm_descent_state : Type := {
  lm_landing_program : landing_program;
  lm_ready_queue : list job;
  lm_fail_registers : fail_registers
}.

(** The initial composed state starts in braking with empty queue and alarms. *)
Definition initial_lm_descent_state : lm_descent_state :=
  {|
    lm_landing_program := P63;
    lm_ready_queue := [];
    lm_fail_registers := empty_fail_registers
  |}.

(**
  The composed state invariant bundles the strongest proved safety facts we have
  so far for the participating subsystems.
*)
Definition lm_descent_state_ok (state : lm_descent_state) : Prop :=
  ready_queue_ok (lm_ready_queue state) /\
  occupied_fail_slots (lm_fail_registers state) <= 3.

(**
  Events for the composed state are deliberately sourced from the Apollo 11
  code organization:

  - executive queue events from `EXECUTIVE.agc`
  - landing phase advancement from the `NEWPHASE` table
  - vertical controller updates from GUILDENSTERN
  - alarm recording from `ALARM_AND_ABORT.agc`
*)
Inductive lm_event : Type :=
| SubmitReadyJob (job_to_submit : job)
| WakeSleepingJob (job_to_wake : job)
| AdvanceLandingPhase
| ApplyGuildensternInputs (inputs : guildenstern_inputs)
| RecordProgramAlarm (code : alarm_code).

(** Small-step event application for the composed LM descent controller. *)
Definition apply_lm_event (event : lm_event) (state : lm_descent_state)
    : lm_descent_state :=
  match event with
  | SubmitReadyJob job_to_submit =>
      {|
        lm_landing_program := lm_landing_program state;
        lm_ready_queue := submit_job job_to_submit (lm_ready_queue state);
        lm_fail_registers := lm_fail_registers state
      |}
  | WakeSleepingJob job_to_wake =>
      {|
        lm_landing_program := lm_landing_program state;
        lm_ready_queue := wake_job job_to_wake (lm_ready_queue state);
        lm_fail_registers := lm_fail_registers state
      |}
  | AdvanceLandingPhase =>
      {|
        lm_landing_program := advance_landing_program (lm_landing_program state);
        lm_ready_queue := lm_ready_queue state;
        lm_fail_registers := lm_fail_registers state
      |}
  | ApplyGuildensternInputs inputs =>
      {|
        lm_landing_program :=
          apply_guildenstern (lm_landing_program state) inputs;
        lm_ready_queue := lm_ready_queue state;
        lm_fail_registers := lm_fail_registers state
      |}
  | RecordProgramAlarm code =>
      {|
        lm_landing_program := lm_landing_program state;
        lm_ready_queue := lm_ready_queue state;
        lm_fail_registers := record_alarm code (lm_fail_registers state)
      |}
  end.

(** The initial composed state satisfies the invariant. *)
Lemma initial_lm_descent_state_ok :
  lm_descent_state_ok initial_lm_descent_state.
Proof.
  split.
  - unfold initial_lm_descent_state, ready_queue_ok.
    constructor.
  - unfold initial_lm_descent_state, occupied_fail_slots, slot_count.
    simpl.
    lia.
Qed.

(**
  Every event we currently model preserves the combined safety invariant.  This
  is the first theorem that actually links the subsystem semantics together.
*)
Lemma apply_lm_event_preserves_state_ok :
  forall (event : lm_event) (state : lm_descent_state),
    lm_descent_state_ok state ->
    lm_descent_state_ok (apply_lm_event event state).
Proof.
  intros event state [Hqueue Hfail].
  destruct event as [job_to_submit | job_to_wake | | inputs | code]; simpl.
  - split.
    + apply submit_job_preserves_ready_queue.
      exact Hqueue.
    + exact Hfail.
  - split.
    + apply wake_job_preserves_ready_queue.
      exact Hqueue.
    + exact Hfail.
  - split.
    + exact Hqueue.
    + exact Hfail.
  - split.
    + exact Hqueue.
    + exact Hfail.
  - split.
    + exact Hqueue.
    + apply record_alarm_preserves_capacity.
Qed.

(**
  GUILDENSTERN remains phase-preserving even after embedding it into the
  composed LM descent state.
*)
Lemma apply_guildenstern_event_preserves_phase :
  forall (state : lm_descent_state) (inputs : guildenstern_inputs),
    landing_phase_of_program
      (lm_landing_program (apply_lm_event (ApplyGuildensternInputs inputs) state)) =
    landing_phase_of_program (lm_landing_program state).
Proof.
  intros state inputs.
  simpl.
  apply apply_guildenstern_preserves_landing_phase.
Qed.

(**
  The explicit phase-advance event remains monotone after composition.
*)
Lemma advance_landing_phase_event_is_monotone :
  forall (state : lm_descent_state),
    landing_phase_rank (landing_phase_of_program (lm_landing_program state)) <=
    landing_phase_rank
      (landing_phase_of_program
         (lm_landing_program (apply_lm_event AdvanceLandingPhase state))).
Proof.
  intros state.
  simpl.
  apply advance_landing_program_is_monotone.
Qed.

(**
  A concrete composed-state trace: four program alarms from the empty state fill
  the three fail registers and force overflow on the fourth alarm.
*)
Lemma fourth_alarm_from_empty_sets_overflow :
  forall (code1 code2 code3 code4 : alarm_code),
    failreg_overflow
      (lm_fail_registers
         (apply_lm_event (RecordProgramAlarm code4)
            (apply_lm_event (RecordProgramAlarm code3)
               (apply_lm_event (RecordProgramAlarm code2)
                  (apply_lm_event (RecordProgramAlarm code1)
                     initial_lm_descent_state))))) = true.
Proof.
  intros code1 code2 code3 code4.
  reflexivity.
Qed.

(**
  The same four-alarm trace saturates, but does not exceed, the three concrete
  fail-register slots.
*)
Lemma fourth_alarm_from_empty_saturates_capacity :
  forall (code1 code2 code3 code4 : alarm_code),
    occupied_fail_slots
      (lm_fail_registers
         (apply_lm_event (RecordProgramAlarm code4)
            (apply_lm_event (RecordProgramAlarm code3)
               (apply_lm_event (RecordProgramAlarm code2)
                  (apply_lm_event (RecordProgramAlarm code1)
                     initial_lm_descent_state))))) = 3.
Proof.
  intros code1 code2 code3 code4.
  reflexivity.
Qed.

(** * Command Module Entry DAP Control *)

(**
  The Comanche entry DAP logic around `READGYMB` and `DOBRATE?` is governed by
  a small number of discrete conditions:

  - whether DAP standby/arming is enabled (`CM/DSTBY`)
  - whether this is the first pass after initialization (`GYMDIFSW`)
  - whether the CDU is in fine-align mode

  The source then branches between body-rate computation, first-pass
  initialization, and DAP termination.
*)
Record cm_dap_inputs : Type := {
  cm_dstby_enabled : bool;
  cm_gymdifsw_enabled : bool;
  cdu_in_fine_align : bool
}.

(**
  We expose the branch outcomes directly.  This matches the source comments more
  closely than a coarser boolean model would.
*)
Inductive cm_dap_outcome : Type :=
| ContinueWithBodyRate
| ContinueFirstPassInitialization
| TerminateDapAndFlushJets
| IdleDueToFineAlign.

(**
  This is the abstract control semantics of `READGYMB` and `DOBRATE?`:

  - fine align prevents normal gimbal-difference processing and idles the DAP
  - if DAP standby is disabled, the DAP flushes jets and terminates group 6
  - if standby is enabled but `GYMDIFSW` is not yet set, the first pass
    initializes state but does not compute body rate
  - otherwise body-rate computation proceeds
*)
Definition cm_entry_dap_step (inputs : cm_dap_inputs) : cm_dap_outcome :=
  if cdu_in_fine_align inputs then IdleDueToFineAlign
  else if cm_dstby_enabled inputs then
         if cm_gymdifsw_enabled inputs
         then ContinueWithBodyRate
         else ContinueFirstPassInitialization
       else TerminateDapAndFlushJets.

(**
  The DAP state records exactly the pieces of abstract control state needed for
  these branch conditions and their effects.
*)
Record cm_dap_state : Type := {
  cm_dap_armed : bool;
  cm_gymdifsw_state : bool;
  cm_jets_firing : bool;
  cm_group_6_active : bool;
  cm_body_rate_valid : bool
}.

(** A conservative initial state before the entry DAP is armed. *)
Definition initial_cm_dap_state : cm_dap_state :=
  {|
    cm_dap_armed := false;
    cm_gymdifsw_state := false;
    cm_jets_firing := false;
    cm_group_6_active := false;
    cm_body_rate_valid := false
  |}.

(**
  Applying one DAP control step updates the abstract state according to the
  control branch selected above.
*)
Definition apply_cm_dap_step
    (inputs : cm_dap_inputs) (state : cm_dap_state) : cm_dap_state :=
  match cm_entry_dap_step inputs with
  | IdleDueToFineAlign =>
      {|
        cm_dap_armed := cm_dap_armed state;
        cm_gymdifsw_state := false;
        cm_jets_firing := false;
        cm_group_6_active := cm_group_6_active state;
        cm_body_rate_valid := cm_body_rate_valid state
      |}
  | ContinueFirstPassInitialization =>
      {|
        cm_dap_armed := true;
        cm_gymdifsw_state := true;
        cm_jets_firing := cm_jets_firing state;
        cm_group_6_active := true;
        cm_body_rate_valid := false
      |}
  | ContinueWithBodyRate =>
      {|
        cm_dap_armed := true;
        cm_gymdifsw_state := true;
        cm_jets_firing := cm_jets_firing state;
        cm_group_6_active := true;
        cm_body_rate_valid := true
      |}
  | TerminateDapAndFlushJets =>
      {|
        cm_dap_armed := false;
        cm_gymdifsw_state := false;
        cm_jets_firing := false;
        cm_group_6_active := false;
        cm_body_rate_valid := false
      |}
  end.

(**
  Fine-align mode prevents the DAP from using the current gimbal pass for body
  rate.  This reflects the early `READGYMB` branch.
*)
Lemma fine_align_forces_idle :
  forall (inputs : cm_dap_inputs),
    cdu_in_fine_align inputs = true ->
    cm_entry_dap_step inputs = IdleDueToFineAlign.
Proof.
  intros inputs Hfine.
  unfold cm_entry_dap_step.
  rewrite Hfine.
  reflexivity.
Qed.

(**
  If standby is disabled and the CDU is not in fine-align mode, the DAP flushes
  jets and terminates the active group, exactly as the `DOBRATE?` path does.
*)
Lemma standby_disabled_terminates_dap :
  forall (inputs : cm_dap_inputs),
    cdu_in_fine_align inputs = false ->
    cm_dstby_enabled inputs = false ->
    cm_entry_dap_step inputs = TerminateDapAndFlushJets.
Proof.
  intros inputs Hfine Hdstby.
  unfold cm_entry_dap_step.
  rewrite Hfine.
  rewrite Hdstby.
  reflexivity.
Qed.

(**
  On the first armed pass, body rate is still not valid; the source explicitly
  skips `BODYRATE` and only initializes the tracking state.
*)
Lemma first_armed_pass_initializes_without_body_rate :
  forall (inputs : cm_dap_inputs),
    cdu_in_fine_align inputs = false ->
    cm_dstby_enabled inputs = true ->
    cm_gymdifsw_enabled inputs = false ->
    cm_entry_dap_step inputs = ContinueFirstPassInitialization.
Proof.
  intros inputs Hfine Hdstby Hgym.
  unfold cm_entry_dap_step.
  rewrite Hfine.
  rewrite Hdstby.
  rewrite Hgym.
  reflexivity.
Qed.

(**
  Once both standby and gimbal-difference state are enabled, the control path
  reaches body-rate computation.
*)
Lemma armed_operational_pass_computes_body_rate :
  forall (inputs : cm_dap_inputs),
    cdu_in_fine_align inputs = false ->
    cm_dstby_enabled inputs = true ->
    cm_gymdifsw_enabled inputs = true ->
    cm_entry_dap_step inputs = ContinueWithBodyRate.
Proof.
  intros inputs Hfine Hdstby Hgym.
  unfold cm_entry_dap_step.
  rewrite Hfine.
  rewrite Hdstby.
  rewrite Hgym.
  reflexivity.
Qed.

(**
  The termination branch really clears the operational DAP state.
*)
Lemma termination_step_clears_dap_activity :
  forall (inputs : cm_dap_inputs) (state : cm_dap_state),
    cm_entry_dap_step inputs = TerminateDapAndFlushJets ->
    cm_dap_armed (apply_cm_dap_step inputs state) = false /\
    cm_jets_firing (apply_cm_dap_step inputs state) = false /\
    cm_group_6_active (apply_cm_dap_step inputs state) = false /\
    cm_body_rate_valid (apply_cm_dap_step inputs state) = false.
Proof.
  intros inputs state Hstep.
  unfold apply_cm_dap_step.
  rewrite Hstep.
  repeat split; reflexivity.
Qed.

(**
  Fine-align idling clears gimbal-difference tracking and quenches jets without
  destroying the rest of the state.
*)
Lemma fine_align_step_clears_gimbal_tracking :
  forall (inputs : cm_dap_inputs) (state : cm_dap_state),
    cm_entry_dap_step inputs = IdleDueToFineAlign ->
    cm_gymdifsw_state (apply_cm_dap_step inputs state) = false /\
    cm_jets_firing (apply_cm_dap_step inputs state) = false.
Proof.
  intros inputs state Hstep.
  unfold apply_cm_dap_step.
  rewrite Hstep.
  split; reflexivity.
Qed.

(**
  A first operational pass arms the DAP and activates group 6, but still leaves
  body-rate validity false.
*)
Lemma first_pass_step_arms_without_rate_validity :
  forall (inputs : cm_dap_inputs) (state : cm_dap_state),
    cm_entry_dap_step inputs = ContinueFirstPassInitialization ->
    cm_dap_armed (apply_cm_dap_step inputs state) = true /\
    cm_group_6_active (apply_cm_dap_step inputs state) = true /\
    cm_body_rate_valid (apply_cm_dap_step inputs state) = false.
Proof.
  intros inputs state Hstep.
  unfold apply_cm_dap_step.
  rewrite Hstep.
  repeat split; reflexivity.
Qed.

(**
  Once the control path reaches the operational branch, body-rate validity is
  established and the DAP remains armed.
*)
Lemma operational_step_sets_body_rate_valid :
  forall (inputs : cm_dap_inputs) (state : cm_dap_state),
    cm_entry_dap_step inputs = ContinueWithBodyRate ->
    cm_dap_armed (apply_cm_dap_step inputs state) = true /\
    cm_group_6_active (apply_cm_dap_step inputs state) = true /\
    cm_body_rate_valid (apply_cm_dap_step inputs state) = true.
Proof.
  intros inputs state Hstep.
  unfold apply_cm_dap_step.
  rewrite Hstep.
  repeat split; reflexivity.
Qed.
