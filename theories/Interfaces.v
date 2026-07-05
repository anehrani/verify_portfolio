(**
  Generic interfaces for building larger financial verification models.

  These records deliberately avoid choosing Q, R, Z, or nat.  A concrete
  model can select the numeric domain that matches its proof obligation.
*)

From Stdlib Require Import Lists.List.

Import ListNotations.

(** An executable boolean decision procedure with a proved soundness bridge. *)
Record SoundChecker (Input : Type) := {
  checker : Input -> bool;
  specification : Input -> Prop;
  checker_sound :
    forall input, checker input = true -> specification input
}.

(** A state transition system, suitable for trades, settlements, or events. *)
Record TransitionSystem := {
  system_state : Type;
  system_event : Type;
  transition : system_event -> system_state -> system_state
}.

Definition invariant (system : TransitionSystem) : Type :=
  system_state system -> Prop.

Definition preserves
    (system : TransitionSystem) (property : invariant system) : Prop :=
  forall event state,
    property state ->
    property (transition system event state).

Fixpoint run
    (system : TransitionSystem)
    (events : list (system_event system))
    (state : system_state system) : system_state system :=
  match events with
  | [] => state
  | event :: rest => run system rest (transition system event state)
  end.

Theorem run_preserves :
  forall (system : TransitionSystem)
         (property : invariant system)
         (events : list (system_event system))
         (state : system_state system),
    preserves system property ->
    property state ->
    property (run system events state).
Proof.
  intros system property events.
  induction events as [| event rest IH]; intros state Hpreserved Hstate.
  - exact Hstate.
  - simpl.
    apply IH.
    + exact Hpreserved.
    + apply Hpreserved.
      exact Hstate.
Qed.

(** A valuation interface shared by exact and analytic models. *)
Record ValuationModel (Scalar : Type) := {
  market_state : Type;
  position : Type;
  value : position -> market_state -> Scalar
}.

Arguments market_state {Scalar} _.
Arguments position {Scalar} _.
Arguments value {Scalar} _ _ _.

(** A generic pointwise comparison between two positions. *)
Definition dominates
    {Scalar : Type}
    (le : Scalar -> Scalar -> Prop)
    (model : ValuationModel Scalar)
    (left right : position model) : Prop :=
  forall state, le (value model left state) (value model right state).
