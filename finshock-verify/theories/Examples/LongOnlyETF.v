(**
  A small checked example:

  70% equity with a -20% jump and 30% bonds with a +3% jump.
  The portfolio-level stress return is -13.1%, which passes a -15% floor.
*)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import setoid_ring.Ring.
From FinShockVerify.Risk Require Import WeightedStress.

Import ListNotations.
Open Scope Q_scope.

Definition equity_weight : Q := 70 # 100.
Definition bond_weight : Q := 30 # 100.
Definition equity_return_floor : Q := - (20 # 100).
Definition bond_return : Q := 3 # 100.
Definition portfolio_loss_floor : Q := - (15 # 100).

Definition equity_bond_shock : list WeightedShock :=
  [
    {| weight := equity_weight; asset_return := equity_return_floor |};
    {| weight := bond_weight; asset_return := bond_return |}
  ].

Example equity_bond_is_fully_invested :
  fully_invested equity_bond_shock.
Proof.
  unfold fully_invested, equity_bond_shock, equity_weight, bond_weight.
  simpl.
  ring.
Qed.

Example equity_bond_is_long_only :
  long_only equity_bond_shock.
Proof.
  unfold long_only, equity_bond_shock, equity_weight, bond_weight.
  repeat constructor; discriminate.
Qed.

Example equity_bond_has_twenty_percent_return_floor :
  returns_floor equity_return_floor equity_bond_shock.
Proof.
  unfold returns_floor, equity_bond_shock, equity_return_floor, bond_return.
  repeat constructor; discriminate.
Qed.

Example equity_bond_stress_return :
  stress_return equity_bond_shock == -131 # 1000.
Proof.
  unfold equity_bond_shock.
  unfold equity_weight, bond_weight, equity_return_floor, bond_return.
  simpl.
  ring.
Qed.

Example equity_bond_passes_fifteen_percent_loss_floor :
  passes_loss_floor portfolio_loss_floor equity_bond_shock = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem equity_bond_verified_loss_floor :
  equity_return_floor <= stress_return equity_bond_shock.
Proof.
  unfold equity_return_floor.
  apply long_only_fully_invested_loss_floor.
  - discriminate.
  - exact equity_bond_is_long_only.
  - exact equity_bond_has_twenty_percent_return_floor.
  - exact equity_bond_is_fully_invested.
Qed.
