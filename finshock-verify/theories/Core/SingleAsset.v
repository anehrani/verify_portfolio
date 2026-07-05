(**
  A minimal executable model of one risky asset, cash, price jumps, and
  self-financing trades with explicit fees.
*)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import setoid_ring.Ring.

Open Scope Q_scope.

Record State := {
  cash : Q;
  shares : Q;
  price : Q
}.

Definition portfolio_value (s : State) : Q :=
  cash s + shares s * price s.

Definition apply_price_return (r : Q) (s : State) : State :=
  {|
    cash := cash s;
    shares := shares s;
    price := price s * (1 + r)
  |}.

Definition trade (quantity fee : Q) (s : State) : State :=
  {|
    cash := cash s - quantity * price s - fee;
    shares := shares s + quantity;
    price := price s
  |}.

Theorem trade_self_financing :
  forall s quantity fee,
    portfolio_value (trade quantity fee s) == portfolio_value s - fee.
Proof.
  intros s quantity fee.
  unfold portfolio_value, trade.
  simpl.
  ring.
Qed.

Theorem price_jump_pnl :
  forall s r,
    portfolio_value (apply_price_return r s) - portfolio_value s
    == shares s * price s * r.
Proof.
  intros s r.
  unfold portfolio_value, apply_price_return.
  simpl.
  ring.
Qed.

Theorem zero_return_preserves_value :
  forall s,
    portfolio_value (apply_price_return 0 s) == portfolio_value s.
Proof.
  intros s.
  unfold portfolio_value, apply_price_return.
  simpl.
  ring.
Qed.
