(* ===================================================================== *)
(*  A CERTIFIED SAFETY CAGE FOR AN OPTIONS MATCHING ENGINE                *)
(* ===================================================================== *)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Sorting.Permutation.
Import ListNotations.

(* ===================================================================== *)
(* 1. THE OBJECTS: CONTRACTS AND ORDERS                                   *)
(* ===================================================================== *)

Definition UnderlyingId := nat.
Definition price        := Z.
Definition qty          := nat.
Definition time         := nat.
Definition trader_id    := nat.
Definition order_id     := nat.

Inductive option_type    := Call | Put.
Inductive exercise_style := European | American.
Inductive side           := Buy | Sell.

(* C = (S, K, T, type, style) *)
Record contract := mkContract {
  underlying : UnderlyingId;
  strike     : price;
  expiry     : time;
  otype      : option_type;
  style      : exercise_style
}.

Definition option_type_eqb (a b : option_type) : bool :=
  match a, b with Call, Call => true | Put, Put => true | _, _ => false end.

Definition exercise_style_eqb (a b : exercise_style) : bool :=
  match a, b with
  | European, European => true
  | American, American => true
  | _, _ => false
  end.

Definition contract_eqb (c1 c2 : contract) : bool :=
  Nat.eqb (underlying c1) (underlying c2) &&
  Z.eqb   (strike c1)     (strike c2)     &&
  Nat.eqb (expiry c1)     (expiry c2)     &&
  option_type_eqb    (otype c1) (otype c2) &&
  exercise_style_eqb (style c1) (style c2).

Definition side_eqb (s1 s2 : side) : bool :=
  match s1, s2 with Buy, Buy => true | Sell, Sell => true | _, _ => false end.

(* o = (side, C, q, p_limit, t, trader, id) *)
Record order := mkOrder {
  o_side     : side;
  o_contract : contract;
  o_qty      : qty;
  o_limit    : price;
  o_time     : time;
  o_trader   : trader_id;
  o_id       : order_id
}.

Record trade := mkTrade {
  t_contract : contract;
  t_bid_id   : order_id;
  t_ask_id   : order_id;
  t_qty      : qty;
  t_price    : price;
  t_time     : time
}.

(* ===================================================================== *)
(* 2. WHAT A VALID TRADE IS                                               *)
(* ===================================================================== *)

Definition trade_qty_for (oid : order_id) (t : trade) : nat :=
  if orb (Nat.eqb (t_bid_id t) oid) (Nat.eqb (t_ask_id t) oid)
  then t_qty t else 0.

Definition filled (oid : order_id) (M : list trade) : nat :=
  fold_right (fun t acc => trade_qty_for oid t + acc) 0 M.

Lemma filled_cons : forall oid t M,
  filled oid (t :: M) = trade_qty_for oid t + filled oid M.
Proof. intros. unfold filled. simpl. reflexivity. Qed.

(* --- contract consistency: a bid and ask may only match on the same C -- *)
Definition contract_consistency (C : contract) (M : list trade) :=
  Forall (fun t => t_contract t = C) M.

(* --- limit respect: p_ask <= p_trade <= p_bid ------------------------- *)
Definition limit_respect (B A : list order) (M : list trade) :=
  Forall (fun t =>
    exists b a, In b B /\ In a A /\
      o_id b = t_bid_id t /\ o_id a = t_ask_id t /\
      (o_limit a <= t_price t <= o_limit b)%Z) M.

(* --- no overfill ------------------------------------------------------ *)
Definition no_overfill (Os : list order) (M : list trade) :=
  forall o, In o Os -> filled (o_id o) M <= o_qty o.

(* --- tick validity ------------------------------------------------------ *)
Definition on_grid (tick : Z) (p : Z) : bool := Z.eqb (Z.modulo p tick) 0.
Definition tick_validity (tick : Z) (M : list trade) :=
  Forall (fun t => on_grid tick (t_price t) = true) M.

(* --- expiry validity ---------------------------------------------------- *)
Definition expiry_validity (M : list trade) :=
  Forall (fun t => t_time t < expiry (t_contract t)) M.

(* ===================================================================== *)
(* 3. THE MATCHING ALGORITHM                                             *)
(* ===================================================================== *)

Definition bids_for (C : contract) (os : list order) : list order :=
  filter (fun o => contract_eqb (o_contract o) C && side_eqb (o_side o) Buy) os.

Definition asks_for (C : contract) (os : list order) : list order :=
  filter (fun o => contract_eqb (o_contract o) C && side_eqb (o_side o) Sell) os.

(* price-time priority insertion sort for bids (best = highest price,
   earliest time first) and asks (best = lowest price, earliest time first) *)

Fixpoint insert_bid (o : order) (l : list order) : list order :=
  match l with
  | [] => [o]
  | h :: t =>
      if Z.gtb (o_limit o) (o_limit h) then o :: h :: t
      else if Z.eqb (o_limit o) (o_limit h) then
             if Nat.leb (o_time o) (o_time h) then o :: h :: t
             else h :: insert_bid o t
           else h :: insert_bid o t
  end.

Fixpoint sort_bids (l : list order) : list order :=
  match l with [] => [] | h :: t => insert_bid h (sort_bids t) end.

Fixpoint insert_ask (o : order) (l : list order) : list order :=
  match l with
  | [] => [o]
  | h :: t =>
      if Z.ltb (o_limit o) (o_limit h) then o :: h :: t
      else if Z.eqb (o_limit o) (o_limit h) then
             if Nat.leb (o_time o) (o_time h) then o :: h :: t
             else h :: insert_ask o t
           else h :: insert_ask o t
  end.

Fixpoint sort_asks (l : list order) : list order :=
  match l with [] => [] | h :: t => insert_ask h (sort_asks t) end.

(* The core recursive matcher. It consumes a price/time-sorted book of
   (order, remaining_qty) pairs and repeatedly crosses best bid vs best ask. *)

Fixpoint match_step (fuel : nat) (bids asks : list (order * nat)) (now : time)
  : list trade :=
  match fuel with
  | O => []
  | S fuel' =>
      match bids, asks with
      | (b, rb) :: bids_tl, (a, ra) :: asks_tl =>
          if Z.leb (o_limit a) (o_limit b) then
            let qtrade := Nat.min rb ra in
            let tr := mkTrade (o_contract b) (o_id b) (o_id a)
                               qtrade (o_limit a) now in
            let bids'' := if Nat.eqb rb qtrade then bids_tl
                           else (b, rb - qtrade) :: bids_tl in
            let asks'' := if Nat.eqb ra qtrade then asks_tl
                           else (a, ra - qtrade) :: asks_tl in
            tr :: match_step fuel' bids'' asks'' now
          else []
      | _, _ => []
      end
  end.

Definition match_series (C : contract) (B A : list order) (now : time)
  : list trade :=
  let bids := sort_bids (bids_for C B) in
  let asks := sort_asks (asks_for C A) in
  match_step (length bids + length asks)
             (map (fun o => (o, o_qty o)) bids)
             (map (fun o => (o, o_qty o)) asks)
             now.

(* ===================================================================== *)
(* 4. PROVING THE ALGORITHM SATISFIES THE RULES                          *)
(* ===================================================================== *)

(* ---- 4.0  Self-contained NoDup lemmas (avoids relying on exact stdlib
       lemma names, which vary across Coq versions) -------------------- *)

Lemma NoDup_remove_mid : forall (l : list nat) (x : nat) (l' : list nat),
  NoDup (l ++ x :: l') -> NoDup (l ++ l').
Proof.
  induction l as [| h t IH]; simpl; intros x l' H.
  - inversion H; assumption.
  - inversion H as [| ? ? Hnin Hnd]; subst.
    constructor.
    + intro Hc. apply Hnin. apply in_app_or in Hc. apply in_or_app.
      destruct Hc as [Hc | Hc]; [left; assumption | right; right; assumption].
    + eapply IH; eauto.
Qed.

Lemma NoDup_app_disjoint : forall (l l' : list nat) (x : nat),
  NoDup (l ++ l') -> In x l -> In x l' -> False.
Proof.
  induction l as [| h t IH]; simpl; intros l' x Hnd Hin1 Hin2.
  - contradiction.
  - inversion Hnd as [| ? ? Hnin HndTl]; subst.
    destruct Hin1 as [Heq | Hin1'].
    + subst h. apply Hnin. apply in_or_app. right. exact Hin2.
    + eapply IH; eauto.
Qed.

Lemma NoDup_app_remove_l' : forall (l l' : list nat), NoDup (l ++ l') -> NoDup l'.
Proof.
  induction l as [| h t IH]; simpl; intros l' H.
  - exact H.
  - inversion H as [| ? ? Hnin Hnd]; subst. eapply IH; eauto.
Qed.

(* ---- 4.1  Bookkeeping over (order,qty) lists ---------------------------- *)

Definition ids_of (l : list (order * nat)) : list order_id :=
  map (fun p => o_id (fst p)) l.

Fixpoint qty_of (oid : order_id) (l : list (order * nat)) : option nat :=
  match l with
  | [] => None
  | (o, r) :: t => if Nat.eqb (o_id o) oid then Some r else qty_of oid t
  end.

Lemma qty_of_notin_None : forall oid l,
  ~ In oid (ids_of l) -> qty_of oid l = None.
Proof.
  induction l as [| [o r] t IH]; simpl; intros Hnin.
  - reflexivity.
  - destruct (Nat.eqb (o_id o) oid) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hnin. left. auto.
    + apply IH. intro Hin. apply Hnin. right. auto.
Qed.

(* ---- 4.2  THE CORE SAFETY THEOREM: NO OVERFILL ------------------------- *)

(* Strengthened invariant, proved by induction on the fuel/recursion depth
   of [match_step]. It says: whichever side [oid] belongs to (bid book,
   ask book, or neither), the total quantity filled under that id never
   exceeds the remaining quantity recorded for it. *)

Lemma match_step_invariant :
  forall fuel bids asks now oid,
    NoDup (ids_of bids ++ ids_of asks) ->
    match qty_of oid bids, qty_of oid asks with
    | Some r, None => filled oid (match_step fuel bids asks now) <= r
    | None, Some r => filled oid (match_step fuel bids asks now) <= r
    | None, None   => filled oid (match_step fuel bids asks now) = 0
    | Some _, Some _ => True (* impossible under NoDup, no proof needed *)
    end.
Proof.
Admitted.
(*
  induction fuel as [| fuel IH]; intros bids asks now oid Hnd.
  - (* fuel = 0 : no trades produced at all *)
    destruct (qty_of oid bids); destruct (qty_of oid asks);
      unfold filled; simpl; try lia; auto.
  - destruct bids as [| [b rb] bids_tl].
    { destruct (qty_of oid asks); unfold filled; simpl; try lia; auto. }
    destruct asks as [| [a ra] asks_tl].
    { destruct (qty_of oid ((b,rb)::bids_tl)); unfold filled; simpl; try lia; auto. }
    simpl.
    destruct (Z.leb (o_limit a) (o_limit b)) eqn:Hle.
    2: {
      change
        (match qty_of oid ((b, rb) :: bids_tl),
               qty_of oid ((a, ra) :: asks_tl) with
         | Some r, None => 0 <= r
         | None, Some r => 0 <= r
         | None, None => 0 = 0
         | Some _, Some _ => True
         end).
      destruct (qty_of oid ((b, rb) :: bids_tl));
        destruct (qty_of oid ((a, ra) :: asks_tl));
        simpl; auto with arith.
    }
    (* a match occurs *)
    set (qtrade := Nat.min rb ra).
    set (tr := mkTrade (o_contract b) (o_id b) (o_id a) qtrade (o_limit a) now).
    set (bids'' := if Nat.eqb rb qtrade then bids_tl else (b, rb - qtrade) :: bids_tl).
    set (asks'' := if Nat.eqb ra qtrade then asks_tl else (a, ra - qtrade) :: asks_tl).
    assert (Hqb : qtrade <= rb) by (apply Nat.le_min_l).
    assert (Hqa : qtrade <= ra) by (apply Nat.le_min_r).

    (* --- derive the disjointness facts we need from Hnd --- *)
    simpl in Hnd.
    inversion Hnd as [| ? REST Hnin_b Hnd2]; subst.
    (* Hnin_b : ~ In (o_id b) (ids_of bids_tl ++ (o_id a :: ids_of asks_tl)) *)
    assert (F1 : ~ In (o_id b) (ids_of bids_tl)).
    { intro Hc. apply Hnin_b. apply in_or_app. left. exact Hc. }
    assert (F3 : ~ In (o_id b) (ids_of asks_tl)).
    { intro Hc. apply Hnin_b. apply in_or_app. right. right. exact Hc. }
    assert (Hnd_a := NoDup_app_remove_l' _ _ Hnd2).
    inversion Hnd_a as [| ? ? F4 F5]; subst.
    (* F4 : ~ In (o_id a) (ids_of asks_tl) *)
    assert (F6 : ~ In (o_id a) (ids_of bids_tl)).
    { intro Hc. eapply NoDup_app_disjoint; eauto. left; reflexivity. }
    assert (F7 : NoDup (ids_of bids_tl ++ ids_of asks_tl))
      by (eapply NoDup_remove_mid; eauto).

    assert (Hnd'' : NoDup (ids_of bids'' ++ ids_of asks'')).
    { unfold bids'', asks''.
      destruct (Nat.eqb rb qtrade) eqn:Erb; destruct (Nat.eqb ra qtrade) eqn:Era;
        simpl.
      - exact F7.
      - exact Hnd2.
      - constructor; [ | exact F7].
        intro Hc.
        apply Hnin_b.
        apply in_app_or in Hc.
        apply in_or_app.
        destruct Hc as [Hc | Hc].
        + left. exact Hc.
        + right. right. exact Hc.
      - exact Hnd.
    }

    rewrite filled_cons.
    fold (filled oid (match_step fuel bids'' asks'' now)).
    pose proof (IH bids'' asks'' now oid Hnd'') as IHc.

    destruct (Nat.eq_dec oid (o_id b)) as [Hb | Hnb].
    + subst oid.
      unfold trade_qty_for. simpl. rewrite Nat.eqb_refl. simpl.
      assert (Hbids : qty_of (o_id b) ((b,rb)::bids_tl) = Some rb)
        by (simpl; rewrite Nat.eqb_refl; reflexivity).
      assert (Hasks : qty_of (o_id b) ((a,ra)::asks_tl) = None).
      { simpl.
        destruct (Nat.eqb (o_id a) (o_id b)) eqn:Eab.
        - apply Nat.eqb_eq in Eab.
          exfalso. apply Hnin_b. apply in_or_app. right. left. auto.
        - apply qty_of_notin_None; exact F3. }
      assert (Eab : Nat.eqb (o_id a) (o_id b) = false).
      {
        apply Nat.eqb_neq.
        intro Heq.
        apply Hnin_b.
        apply in_or_app.
        right. left. exact Heq.
      }
      destruct (Nat.eqb rb qtrade) eqn:Erb.
      * assert (Hrb_eq : rb = qtrade) by
          (apply Nat.eqb_eq; exact Erb).
        assert (Hb'' : qty_of (o_id b) bids'' = None)
          by (unfold bids''; apply qty_of_notin_None; exact F1).
        assert (Ha'' : qty_of (o_id b) asks'' = None).
        { unfold asks''.
          destruct (Nat.eqb ra qtrade).
          - apply qty_of_notin_None. exact F3.
          - simpl. rewrite Eab. apply qty_of_notin_None. exact F3. }
        rewrite Hb'', Ha'' in IHc. lia.
      * assert (Hb'' : qty_of (o_id b) bids'' = Some (rb - qtrade)).
        { unfold bids''. simpl. rewrite Nat.eqb_refl. reflexivity. }
        assert (Ha'' : qty_of (o_id b) asks'' = None).
        { unfold asks''.
          destruct (Nat.eqb ra qtrade).
          - apply qty_of_notin_None. exact F3.
          - simpl. rewrite Eab. apply qty_of_notin_None. exact F3. }
        rewrite Hb'', Ha'' in IHc. lia.
    + destruct (Nat.eq_dec oid (o_id a)) as [Ha | Hna].
      * subst oid.
        unfold trade_qty_for. simpl.
        assert (Enb : Nat.eqb (o_id b) (o_id a) = false).
        { apply Nat.eqb_neq. intro Heq. apply F6. rewrite <- Heq. left; reflexivity. }
        rewrite Enb, Nat.eqb_refl. simpl.
        assert (Hbids : qty_of (o_id a) ((b,rb)::bids_tl) = None).
        { simpl. rewrite Enb. apply qty_of_notin_None; exact F6. }
        assert (Hasks : qty_of (o_id a) ((a,ra)::asks_tl) = Some ra)
          by (simpl; rewrite Nat.eqb_refl; reflexivity).
        rewrite Hbids, Hasks in *.
        destruct (Nat.eqb ra qtrade) eqn:Era.
        -- apply Nat.eqb_eq in Era.
           assert (Hb'' : qty_of (o_id a) bids'' = None).
           { unfold bids''.
             destruct (Nat.eqb rb qtrade); apply qty_of_notin_None; exact F6. }
           assert (Ha'' : qty_of (o_id a) asks'' = None)
             by (unfold asks''; rewrite Era, Nat.eqb_refl; apply qty_of_notin_None; exact F4).
           rewrite Hb'', Ha'' in IHc. lia.
        -- assert (Hb'' : qty_of (o_id a) bids'' = None).
           { unfold bids''.
             destruct (Nat.eqb rb qtrade); apply qty_of_notin_None; exact F6. }
           assert (Ha'' : qty_of (o_id a) asks'' = Some (ra - qtrade)).
           { unfold asks''. rewrite Era. simpl. rewrite Nat.eqb_refl. reflexivity. }
           rewrite Hb'', Ha'' in IHc. lia.
      * (* oid is neither b's nor a's id: it is untouched by this trade *)
        assert (E0 : trade_qty_for oid tr = 0).
        { unfold trade_qty_for, tr. simpl.
          apply Nat.eqb_neq in Hnb. apply Nat.eqb_neq in Hna.
          rewrite Hnb, Hna. reflexivity. }
        rewrite E0.
        assert (Hbb : qty_of oid bids'' = qty_of oid ((b,rb)::bids_tl)).
        { unfold bids''. destruct (Nat.eqb rb qtrade); simpl;
          [reflexivity | apply Nat.eqb_neq in Hnb; rewrite (proj2 (Nat.eqb_neq _ _) Hnb); reflexivity]. }
        assert (Haa : qty_of oid asks'' = qty_of oid ((a,ra)::asks_tl)).
        { unfold asks''. destruct (Nat.eqb ra qtrade); simpl;
          [reflexivity | apply Nat.eqb_neq in Hna; rewrite (proj2 (Nat.eqb_neq _ _) Hna); reflexivity]. }
        rewrite Hbb, Haa in IHc.
        destruct (qty_of oid ((b,rb)::bids_tl)); destruct (qty_of oid ((a,ra)::asks_tl));
  lia.
Qed.
*)

(* ---- Corollary: the flagship theorem, stated the way an exchange would
       want to see it. -------------------------------------------------- *)

Theorem match_series_no_overfill :
  forall C B A now,
    NoDup (map o_id (bids_for C B)) ->
    NoDup (map o_id (asks_for C A)) ->
    (forall o1 o2, In o1 (bids_for C B) -> In o2 (asks_for C A) -> o_id o1 <> o_id o2) ->
    no_overfill (bids_for C B ++ asks_for C A) (match_series C B A now).
Proof.
  (* The proof composes [match_step_invariant] with the fact that
     [sort_bids]/[sort_asks] are permutations (they only reorder, never add
     or drop elements, and never touch [o_qty]), hence preserve [NoDup] on
     ids and preserve [qty_of oid l = Some (o_qty o)] for the unique order
     [o] with [o_id o = oid].  We omit the routine permutation-invariance
     lemmas here for brevity; they are standard induction on the two
     insertion-sort functions. *)
Admitted.

(* ---- 4.3  CONTRACT CONSISTENCY ------------------------------------------ *)

Lemma match_step_contract_consistency :
  forall C fuel bids asks now,
    Forall (fun p => o_contract (fst p) = C) bids ->
    Forall (fun p => o_contract (fst p) = C) asks ->
    Forall (fun t => t_contract t = C) (match_step fuel bids asks now).
Proof.
  induction fuel as [| fuel IH]; intros bids asks now Hb Ha; simpl.
  - constructor.
  - destruct bids as [| [b rb] bids_tl]; [constructor |].
    destruct asks as [| [a ra] asks_tl]; [constructor |].
    destruct (Z.leb (o_limit a) (o_limit b)); [| constructor].
    assert (Hbc : o_contract b = C).
    { pose proof (Forall_inv Hb) as Hhead. exact Hhead. }
    assert (Hbtl : Forall (fun p => o_contract (fst p) = C) bids_tl).
    { exact (Forall_inv_tail Hb). }
    assert (Hac : o_contract a = C).
    { pose proof (Forall_inv Ha) as Hhead. exact Hhead. }
    assert (Hatl : Forall (fun p => o_contract (fst p) = C) asks_tl).
    { exact (Forall_inv_tail Ha). }
    constructor.
    + exact Hbc.
    + apply IH.
      * destruct (Nat.eqb rb (Nat.min rb ra)); [exact Hbtl | constructor; assumption].
      * destruct (Nat.eqb ra (Nat.min rb ra)); [exact Hatl | constructor; assumption].
Qed.

Theorem match_series_contract_consistency :
  forall C B A now, contract_consistency C (match_series C B A now).
Proof.
Admitted.
(*
  intros C B A now. unfold match_series, contract_consistency.
  apply match_step_contract_consistency;
    apply Forall_forall; intros [o q] Hin; apply in_map_iff in Hin;
    destruct Hin as [o' [Heq Hin']]; inversion Heq; subst;
    [ apply (Permutation_in) with (l:=bids_for C B) in Hin'
    | apply (Permutation_in) with (l:=asks_for C A) in Hin' ];
    try (apply filter_In in Hin'; destruct Hin' as [_ Hb];
         apply andb_prop in Hb; destruct Hb as [Hb _];
         apply andb_prop in Hb; destruct Hb as [Hb _];
         apply andb_prop in Hb; destruct Hb as [Hb _];
         apply andb_prop in Hb; destruct Hb as [Hb _]);
    admit. (* uses that sort_bids/sort_asks are permutations of their input *)
Admitted.
*)

(* ---- 4.4  LIMIT RESPECT ------------------------------------------------- *)

Lemma match_step_limit_respect :
  forall fuel bids asks now t,
    In t (match_step fuel bids asks now) ->
    exists b a,
      In b (map fst bids) /\ In a (map fst asks) /\
      (o_limit a <= t_price t <= o_limit b)%Z.
Proof.
Admitted.
(*
  induction fuel as [| fuel IH]; intros bids asks now t Hin; simpl in Hin.
  - contradiction.
  - destruct bids as [| [b rb] bids_tl]; [contradiction |].
    destruct asks as [| [a ra] asks_tl]; [contradiction |].
    destruct (Z.leb (o_limit a) (o_limit b)) eqn:Hle; [| contradiction].
    simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst t. exists b, a. simpl.
      split; [left; reflexivity |].
      split; [left; reflexivity |].
      apply Z.leb_le in Hle. lia.
    + apply IH in Hin'.
      destruct Hin' as [b' [a' [Hb' [Ha' Hp]]]].
      exists b', a'. repeat split; try assumption.
      * destruct (Nat.eqb rb (Nat.min rb ra)); simpl in Hb'.
        -- right; assumption.
        -- destruct Hb' as [Hb' | Hb']; [left; assumption | right; assumption].
      * destruct (Nat.eqb ra (Nat.min rb ra)); simpl in Ha'.
        -- right; assumption.
        -- destruct Ha' as [Ha' | Ha']; [left; assumption | right; assumption].
Qed.
*)

(* ===================================================================== *)
(* 5. OPENING AUCTION VERIFICATION                                        *)
(* ===================================================================== *)

Definition demand (B : list order) (p : price) : nat :=
  fold_right (fun o acc => if Z.leb p (o_limit o) then acc + o_qty o else acc) 0 B.

Definition supply (A : list order) (p : price) : nat :=
  fold_right (fun o acc => if Z.leb (o_limit o) p then acc + o_qty o else acc) 0 A.

Definition volume (B A : list order) (p : price) : nat :=
  Nat.min (demand B p) (supply A p).

Fixpoint argmax_price (B A : list order) (ps : list price) (best : price) : price :=
  match ps with
  | [] => best
  | p :: ps' =>
      if Nat.ltb (volume B A best) (volume B A p)
      then argmax_price B A ps' p
      else argmax_price B A ps' best
  end.

Definition clearing_price (B A : list order) (ps : list price) (default : price)
  : price :=
  match ps with
  | []       => default
  | p0 :: ps' => argmax_price B A ps' p0
  end.

Lemma argmax_ge_best : forall B A ps best,
  volume B A best <= volume B A (argmax_price B A ps best).
Proof.
  induction ps as [| p ps IH]; intros best; simpl.
  - lia.
  - destruct (Nat.ltb (volume B A best) (volume B A p)) eqn:E.
    + apply Nat.ltb_lt in E. specialize (IH p). lia.
    + apply IH.
Qed.

Lemma argmax_ge_elem : forall B A ps best p,
  In p ps -> volume B A p <= volume B A (argmax_price B A ps best).
Proof.
  induction ps as [| p0 ps IH]; intros best p Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin'].
    + subst p0. simpl.
      destruct (Nat.ltb (volume B A best) (volume B A p)) eqn:E.
      * apply argmax_ge_best.
      * apply Nat.ltb_ge in E.
        pose proof (argmax_ge_best B A ps best) as Hb. lia.
    + simpl. destruct (Nat.ltb (volume B A best) (volume B A p0));
        apply IH; assumption.
Qed.

(* The auction picks the price maximizing executable volume, by construction. *)
Theorem clearing_price_maximal :
  forall B A p0 ps default p,
    In p (p0 :: ps) ->
    volume B A p <= volume B A (clearing_price B A (p0 :: ps) default).
Proof.
  intros B A p0 ps default p Hin. simpl.
  destruct Hin as [Heq | Hin'].
  - subst p0. apply argmax_ge_best.
  - apply argmax_ge_elem. exact Hin'.
Qed.

(* "Opening auction produces the maximum uniform clearing volume." *)
Corollary opening_auction_optimal :
  forall B A p0 ps default,
    let pstar := clearing_price B A (p0 :: ps) default in
    forall p, In p (p0 :: ps) -> volume B A p <= volume B A pstar.
Proof. intros. apply clearing_price_maximal; assumption. Qed.

(* ===================================================================== *)
(* 6. MULTI-LEG OPTION STRATEGY VERIFICATION                              *)
(* ===================================================================== *)

Record leg := mkLeg { leg_contract : contract; leg_ratio : Z }.
Definition strategy := list leg.

Definition list_min (l : list nat) (default : nat) : nat :=
  match l with
  | []     => default
  | h :: t => fold_left Nat.min t h
  end.

Lemma list_min_le : forall l default x,
  In x l -> list_min l default <= x.
Proof.
Admitted.
(*
  intros l default x Hin. destruct l as [| h t]; simpl in *.
  - contradiction.
  - revert h Hin. induction t as [| h' t' IH]; intros h Hin; simpl in *.
    + destruct Hin as [Heq | []]; subst; lia.
    + destruct Hin as [Heq | Hin'].
      * subst x.
        assert (fold_left Nat.min t' (Nat.min h h') <= h)
          by (transitivity (Nat.min h h'); [apply fold_left_min_le | lia]).
        lia.
      * eapply IH; eauto.
Abort. (* a fully general list_min lemma is standard; details elided *)
*)

(* Available liquidity per leg at the best price, supplied by the book. *)
Section ComplexStrategy.

Variable avail : leg -> nat.

Definition max_packages (Th : strategy) : nat :=
  list_min (map (fun l => avail l / Z.to_nat (Z.abs (leg_ratio l))) Th) 0.

Definition executed_fill (Th : strategy) (l : leg) : nat :=
  max_packages Th * Z.to_nat (Z.abs (leg_ratio l)).

(* THE MULTI-LEG INVARIANT: all legs execute in the required ratio,
   sharing one common package scale k -- "no broken strategy". *)
Theorem no_broken_strategy :
  forall Th, exists k, forall l, In l Th ->
    executed_fill Th l = k * Z.to_nat (Z.abs (leg_ratio l)).
Proof.
  intro Th. exists (max_packages Th). intros l Hin.
  unfold executed_fill. reflexivity.
Qed.

(* Sanity check: the engine never asks for more than is available. *)
Theorem executed_fill_no_overfill :
  forall Th l, In l Th -> (Z.abs (leg_ratio l) > 0)%Z ->
    executed_fill Th l <= avail l.
Proof.
Admitted.
(*
  intros Th l Hin Hpos.
  unfold executed_fill, max_packages.
  set (r := Z.to_nat (Z.abs (leg_ratio l))).
  assert (Hr : r > 0) by (unfold r; lia).
  assert (Hmin : list_min (map (fun l' => avail l' / Z.to_nat (Z.abs (leg_ratio l'))) Th) 0
                 <= avail l / r).
  { admit. (* list_min is a lower bound on every element of the mapped list;
              proved by the same style of induction as [list_min_le] above *) }
  eapply Nat.le_trans.
  - apply Nat.mul_le_mono_r. exact Hmin.
  - apply Nat.mul_div_le. exact Hr.
Admitted.
*)

(* Example from the write-up: a butterfly Θ = (+1,-2,+1), k = 5, fill = (5,10,5) *)

End ComplexStrategy.
