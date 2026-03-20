Require Import Stdlib.ZArith.ZArith.
Require Import ActLib.ActLib.
Require Stdlib.Strings.String.
From Stdlib Require Import Lia.


Require Import ERC20.ERC20.

Import Token.

(* Address should be Z or N? Or int20? *)

Ltac destructAnds :=
  repeat match goal with
    [ H : _ /\ _ |- _ ] => destruct H
  end.

Ltac rewrite_eqbs :=
  repeat match goal with
  | [ H : ?a = ?b |- context [?a =? ?b] ] =>
    rewrite (proj2 (Z.eqb_eq a b) H)
  | [ H : ?a = ?b |- context [?b =? ?a] ] =>
    rewrite (proj2 (Z.eqb_eq b a) (eq_sym H))
  | [ H : ?a <> ?b |- context [?a =? ?b] ] =>
    rewrite (proj2 (Z.eqb_neq a b) H)
  | [ H : ?a <> ?b |- context [?b =? ?a] ] =>
    rewrite (proj2 (Z.eqb_neq b a) (not_eq_sym H))
  end.

Definition MAX_ADDRESS := UINT_MAX 160.

Fixpoint balanceOf_sum' (balanceOf : address -> Z) (n : nat) (acc : Z) : Z :=
    match n with
    | O => balanceOf 0 + acc
    | S n => balanceOf_sum' balanceOf n (acc + balanceOf (Z.of_nat (S n)))
    end.

Definition balanceOf_sum (STATE : State) :=
  balanceOf_sum' (balanceOf STATE) (Z.to_nat MAX_ADDRESS) 0.


Definition transfer_from map (from : address) (amt : Z) :=
  fun b => if b =? from then map from - amt else map b.

Definition transfer_to map (from : address) (amt : Z) :=
  fun b => if b =? from then map from + amt else map b.

Definition transfer map from to amt := transfer_to (transfer_from map from amt) to amt.

Definition transfer' map from to amt := transfer_from (transfer_to map to amt) from amt.

Lemma balanceOf_sum_f_eq f f' addr acc :
  (forall x, x <= Z.of_nat addr -> f x = f' x) ->
  balanceOf_sum' f addr acc = balanceOf_sum' f' addr acc.
Proof.
  revert acc. induction addr; intros acc Hyp.
  - simpl. rewrite Hyp. reflexivity. lia.
  - simpl. rewrite IHaddr. rewrite Hyp. reflexivity.
    lia. intros. eapply Hyp. lia.
Qed.

Lemma balanceOf_sum_acc f  addr acc z :
  balanceOf_sum' f addr (acc + z) = balanceOf_sum' f addr acc + z.
Proof.
  revert z acc. induction addr; intros z acc.
  - simpl. lia.
  - simpl. rewrite !IHaddr. lia.
Qed.

Opaque Z.sub Z.add Z.of_nat.

Lemma balanceOf_sum_thm x f f' addr acc :
  (forall y, x <> y -> f y = f' y) ->
  0 <= x ->
  balanceOf_sum' f addr acc =
  if (Z.to_nat x <=? addr)%nat then balanceOf_sum' f' addr acc - f' x + f x else balanceOf_sum' f' addr acc.
Proof.
  revert acc. induction addr; intros acc Hyp Hleq1.
  - simpl. destruct (0 =? x) eqn:Heq.
    + eapply Z.eqb_eq in Heq. subst.
      simpl. lia.
    + eapply Z.eqb_neq in Heq.
      assert (Hbeq : (Z.to_nat x <=? 0)%nat = false).
      { eapply leb_correct_conv. lia. }
      rewrite Hbeq. rewrite Hyp. reflexivity. eauto.

  - destruct (Z.to_nat x <=? S addr0)%nat eqn:Hleq.
    + eapply Nat.leb_le in Hleq.
      destruct (Z.of_nat (S addr0) =? x) eqn:Heqb.
      * eapply Z.eqb_eq in Heqb. simpl. rewrite Heqb.
        erewrite balanceOf_sum_f_eq with (f' := f').
        rewrite !balanceOf_sum_acc. lia.

        intros. eapply Hyp. lia.

      * simpl.
        destruct ((Z.to_nat x <=? addr0)%nat) eqn:Hleq'.
        -- rewrite IHaddr; eauto. rewrite Hyp. reflexivity.
           intros Heq; subst. lia.
        -- eapply Z.eqb_neq in Heqb.
           eapply Nat.leb_gt in Hleq'. lia.

    + simpl. eapply leb_complete_conv in Hleq.
      erewrite balanceOf_sum_f_eq with (f' := f').
      rewrite Hyp. reflexivity.
      * intros Heq; subst. lia.
      * intros. rewrite Hyp. reflexivity.
        intros Heq; subst. lia.
Qed.

Lemma balanceOf_sum_thm' x f f' acc :
  (forall y, x <> y -> f y = f' y) ->
  0 <= x <= MAX_ADDRESS->
  balanceOf_sum' f (Z.to_nat MAX_ADDRESS) acc = balanceOf_sum' f' (Z.to_nat MAX_ADDRESS) acc - f' x + f x.
Proof.
  intros H_f [H_x_0 H_x_max].
  rewrite balanceOf_sum_thm with (x := x) (f' := f').
  - apply Z2Nat.inj_le in H_x_max; try lia.
    rewrite <- Nat.leb_le in H_x_max.
    rewrite H_x_max.
    reflexivity.
  - assumption.
  - assumption.
Qed.

Lemma balanceOf_sum_transfer_thm x1 x2 f f' acc :
  (forall y, x1 <> y -> x2 <> y -> f y = f' y) ->
  f x1 + f x2 = f' x1 + f' x2 ->
  0 <= x1 <= MAX_ADDRESS ->
  0 <= x2 <= MAX_ADDRESS ->
  balanceOf_sum' f (Z.to_nat MAX_ADDRESS) acc = balanceOf_sum' f' (Z.to_nat MAX_ADDRESS) acc.
Proof.
  intros H_f1 H_f2 [H_x1_0 H_x1_max] [H_x2_0 H_x2_max].
  rewrite balanceOf_sum_thm with (x := x1) (f' := fun _b => if _b =? x1 then f' _b else f _b).
  - apply Z2Nat.inj_le in H_x1_max; try lia.
    rewrite <- Nat.leb_le in H_x1_max.
    rewrite H_x1_max, Z.eqb_refl.
    rewrite balanceOf_sum_thm with (x := x2) (f' := f').
    + apply Z2Nat.inj_le in H_x2_max; try lia.
      rewrite <- Nat.leb_le in H_x2_max.
      rewrite H_x2_max.
      destruct (x2 =? x1) eqn:Hx2x1.
      * apply Z.eqb_eq in Hx2x1. subst. lia.
      * lia.
    + intros. destruct (y =? x1) eqn:Hyx1.
      * lia.
      * apply H_f1; [lia | assumption].
    + lia.
  - intros. destruct (y =? x1) eqn:Hyx1.
    * apply H_f1; [assumption | lia].
    * reflexivity.
  - lia.
Qed.

Theorem initialSupply': forall ENV _totalSupply (n : nat), forall NA NA' STATE,
    0 <= Caller ENV ->
    constructor ENV _totalSupply NA STATE NA' ->
    balanceOf_sum' (balanceOf STATE) n 0 =
    if (Z.of_nat n <? (Caller ENV)) then 0 else totalSupply STATE.
Proof.
  intros ENV ? ? ? ? ? ? Hcnstr.
  destruct Hcnstr as [? Hinitprecs _ HnextNA]; simpl.

  assert (forall n : nat, Z.of_nat n < Caller ENV ->
      balanceOf_sum' (fun _binding_0 : address => if _binding_0 =? Caller ENV then _totalSupply else 0) n 0 = 0) as H0.
  { intros. induction n0.
    - simpl. destruct (Caller ENV); [discriminate | |]; reflexivity.
    - simpl. rewrite -> balanceOf_sum_acc.
      destruct (Z.of_nat (S n0) =? Caller ENV) eqn:Heq.
      + apply Z.eqb_eq in Heq. apply Z.lt_neq in H0. contradiction.
      + rewrite IHn0.
        * reflexivity.
        * lia.
  }

  induction n.
  - simpl.
    destruct (Caller ENV) eqn:Hcaller.
      + assert ( Z.of_nat 0 <? Caller ENV = false).
        * apply Z.ltb_ge. lia.
        * rewrite <- Hcaller at 2. rewrite H1. lia.
      + reflexivity.
      + contradiction.
  - simpl. rewrite balanceOf_sum_acc.
    destruct (Z.of_nat (S n) <? Caller ENV) eqn:Hlt.
    + destruct (Z.of_nat (S n) =? Caller ENV) eqn:Heq. * lia.
      * rewrite H0.
        reflexivity.
        apply Zlt_is_lt_bool in Hlt. lia.

    + destruct (Z.of_nat (S n) =? Caller ENV) eqn:Heq.
      * rewrite H0.
        -- lia.
        -- apply Z.eqb_eq in Heq. lia.
      * rewrite IHn.
        assert ( Z.of_nat n <? Caller ENV = false).
        { apply Z.ltb_ge in Hlt. apply Z.eqb_neq in Heq. lia. }
        rewrite H1. lia.
Qed.

Theorem initialSupply: forall NA ENV _totalSupply STATE NA',
    0 <= Caller ENV <= MAX_ADDRESS ->
    constructor ENV _totalSupply NA STATE NA' ->
    balanceOf_sum STATE =
    totalSupply STATE.
Proof.
  intros.
  unfold balanceOf_sum.
  erewrite -> initialSupply'.
  - rewrite Z2Nat.id.
    + destruct (MAX_ADDRESS <? Caller ENV) eqn:Hineq.
      * destruct H0 as [? Hinit _ _].
        apply Z.ltb_lt in Hineq. lia.
      * rewrite Hineq. reflexivity.
    + unfold MAX_ADDRESS. unfold UINT_MAX. lia.
  - destruct H0 as [? Hinit _ _], Hinit. lia.
  - eassumption.
Qed.

Theorem deltas: forall x1 x2 y1 y2,
  x1 = y1 -> x1 - x2 = y1 - y2 -> x2 = y2.
Proof.
  intros. lia.
Qed.

Theorem sum_balanceOf_eq_totalSupply : forall STATE,
    reachable STATE ->
    balanceOf_sum STATE = totalSupply STATE.
Proof.
  intros STATE Hreach.
  destruct Hreach as [ BASE Hreach ], Hreach as [ Hinit Hmulti ].

  induction Hmulti as [ | STATE STATE' Hstep ].
  - destruct Hinit as [ENV ? ? ? Hcnstr].
    eapply initialSupply.
    2: eassumption.
    destruct Hcnstr as [? Hinit _ ?], Hinit, H_envNextAddrConsistent.
    unfold MAX_ADDRESS.
    split; lia.

  - assert ( forall a b, a - (a - b) = b) as Ha1. lia.
    assert ( forall a b c,
      a - b =  c <-> a - c = b) as Ha2. lia.
    assert ( forall a b, a - (a + b) = - b) as Ha3. lia.
    assert ( forall a b c,
      a - b = -c <-> a + c = b) as Ha4. lia.

    destruct Hstep as [ENV [NA [NA' Htransition]]].
    destruct Htransition as [Hstep].
    destruct Hstep.
    + (* transfer *)
      apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [assumption|].
      unfold balanceOf_sum.
      rewrite balanceOf_sum_transfer_thm with (x1 := Caller ENV) (x2 := to) (f' := balanceOf STATE').
      * destruct H; simpl; lia.
      * destruct H; simpl; intros; rewrite_eqbs; reflexivity.
      * destruct H; simpl; rewrite_eqbs; repeat rewrite Z.eqb_refl; lia.
      * destruct H; simpl; unfold MAX_ADDRESS; destruct H_conds, H_envNextAddrConsistent; lia.
      * destruct H; simpl; unfold MAX_ADDRESS; destruct H_conds; lia.
    + (* transferFrom *)
      apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [assumption|].
      unfold balanceOf_sum. simpl.
      rewrite balanceOf_sum_transfer_thm with (x1 := src) (x2 := dst) (f' := balanceOf STATE').
      * destruct H; simpl; lia.
      * destruct H; simpl; intros; rewrite_eqbs; reflexivity.
      * destruct H; simpl; destructAnds; rewrite_eqbs; repeat rewrite Z.eqb_refl; lia.
      * destruct H; simpl; unfold MAX_ADDRESS; destruct H_conds; lia.
      * destruct H; simpl; unfold MAX_ADDRESS; destruct H_conds; lia.
    + (* approve *)
      destruct H; simpl; auto.
    + (* burn *)
      apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [assumption|].
      unfold balanceOf_sum. simpl.
      rewrite balanceOf_sum_thm' with (x := Caller ENV) (f' := balanceOf STATE').
      * destruct H; simpl; rewrite Z.eqb_refl; lia.
      * destruct H; simpl; intros; rewrite_eqbs; reflexivity.
      * destruct H; simpl; unfold MAX_ADDRESS; destruct H_conds, H_envNextAddrConsistent; lia.
    + (* burnFrom *)
      apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [assumption|].
      unfold balanceOf_sum. simpl.
      rewrite balanceOf_sum_thm' with (x := src) (f' := balanceOf STATE').
      * destruct H; simpl; rewrite Z.eqb_refl; lia.
      * destruct H; simpl; intros; rewrite_eqbs; reflexivity.
      * destruct H; simpl; unfold MAX_ADDRESS; destruct H_conds; lia.
    + (* mint *)
      apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [assumption|].
      unfold balanceOf_sum. simpl.
      rewrite balanceOf_sum_thm' with (x := dst) (f' := balanceOf STATE').
      * destruct H; simpl; rewrite Z.eqb_refl; lia.
      * destruct H; simpl; intros; rewrite_eqbs; reflexivity.
      * destruct H; simpl; unfold MAX_ADDRESS; destruct H_conds; lia.
    + (* totalSupply *)
      destruct H; simpl; auto.
    + (* balanceOf *)
      destruct H; simpl; auto.
    + (* allowance *)
      destruct H; simpl; auto.
Qed.
