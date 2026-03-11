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
