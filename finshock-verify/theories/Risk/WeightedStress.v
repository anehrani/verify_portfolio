(**
  Finite stress-scenario model for portfolio weights and discontinuous price
  jumps. This is the first useful layer for portfolio verification: no market
  prediction, just exact reasoning about explicitly specified shocks.
*)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lqa.
From Stdlib Require Import setoid_ring.Ring.

Import ListNotations.
Open Scope Q_scope.

Record WeightedShock := {
  weight : Q;
  asset_return : Q
}.

Fixpoint net_weight (scenario : list WeightedShock) : Q :=
  match scenario with
  | [] => 0
  | leg :: rest => weight leg + net_weight rest
  end.

Fixpoint gross_leverage (scenario : list WeightedShock) : Q :=
  match scenario with
  | [] => 0
  | leg :: rest => Qabs (weight leg) + gross_leverage rest
  end.

Fixpoint stress_return (scenario : list WeightedShock) : Q :=
  match scenario with
  | [] => 0
  | leg :: rest => weight leg * asset_return leg + stress_return rest
  end.

Definition long_only (scenario : list WeightedShock) : Prop :=
  Forall (fun leg => 0 <= weight leg) scenario.

Definition returns_floor (floor : Q) (scenario : list WeightedShock) : Prop :=
  Forall (fun leg => floor <= asset_return leg) scenario.

Definition fully_invested (scenario : list WeightedShock) : Prop :=
  net_weight scenario == 1.

Definition passes_loss_floor (floor : Q) (scenario : list WeightedShock) : bool :=
  Qle_bool floor (stress_return scenario).

Theorem passes_loss_floor_sound :
  forall floor scenario,
    passes_loss_floor floor scenario = true ->
    floor <= stress_return scenario.
Proof.
  intros floor scenario H.
  unfold passes_loss_floor in H.
  apply Qle_bool_iff.
  exact H.
Qed.

Lemma stress_return_floor_scaled :
  forall scenario eps,
    0 <= eps ->
    long_only scenario ->
    returns_floor (- eps) scenario ->
    - eps * net_weight scenario <= stress_return scenario.
Proof.
  induction scenario as [| leg rest IH]; intros eps Heps Hlong Hfloor.
  - simpl.
    lra.
  - unfold long_only in Hlong.
    unfold returns_floor in Hfloor.
    inversion Hlong as [| ? ? Hweight Hlong_tail]; subst.
    inversion Hfloor as [| ? ? Hreturn Hfloor_tail]; subst.
    simpl.
    assert (Hleg_scaled : (- eps) * weight leg <= asset_return leg * weight leg).
    {
      apply Qmult_le_compat_r.
      - exact Hreturn.
      - exact Hweight.
    }
    assert (Hleg : - eps * weight leg <= weight leg * asset_return leg) by lra.
    specialize (IH eps Heps Hlong_tail Hfloor_tail).
    lra.
Qed.

Theorem long_only_fully_invested_loss_floor :
  forall scenario eps,
    0 <= eps ->
    long_only scenario ->
    returns_floor (- eps) scenario ->
    fully_invested scenario ->
    - eps <= stress_return scenario.
Proof.
  intros scenario eps Heps Hlong Hfloor Hfull.
  unfold fully_invested in Hfull.
  pose proof
    (stress_return_floor_scaled scenario eps Heps Hlong Hfloor) as Hscaled.
  setoid_rewrite Hfull in Hscaled.
  lra.
Qed.
