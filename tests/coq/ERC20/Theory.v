Require Import Stdlib.ZArith.ZArith.
Require Import ActLib.ActLib.
Require Stdlib.Strings.String.
From Stdlib Require Import Lia.


Require Import ERC20.ERC20.

Import Token.

(* Address should be Z or N? Or int20? *)

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

Inductive transferRelation from to amt (map : address -> Z) (map' : address -> Z) : Prop:= 
  | transferEqC:
      from <> to
  -> (forall p, p <> from -> p <> to -> map p = map' p)
  -> map from = map' from + amt 
  -> map to + amt= map' to
  -> transferRelation from to amt map map'
  | transferNeqC:
      from = to
  -> (forall p, map p = map' p)
  -> transferRelation from to amt map map'.

Inductive transferStateRelation from to amt s s' : Prop:= 
  | transferStateC: 
    transferRelation from to amt (balanceOf s) (balanceOf s')
    -> transferStateRelation from to amt s s'.

Inductive mintRelation to amt map (map' : address -> Z) : Prop:= 
  | mintC: 
  map to + amt= map' to
  -> (forall p, p <> to -> map p = map' p)
  ->  mintRelation to amt map map'.

Inductive mintStateRelation to amt s s' : Prop:= 
  | mintStateC: 
    mintRelation to amt (balanceOf s) (balanceOf s')
    -> mintStateRelation to amt s s'.

Inductive burnRelation from amt map (map' : address -> Z) : Prop:= 
  | burnC: 
      map from = map' from + amt
  -> (forall p, p <> from -> map p = map' p)
  ->  burnRelation from amt map map'.

Inductive burnStateRelation from amt s s' : Prop:= 
  | burnStateC: 
    burnRelation from amt (balanceOf s) (balanceOf s')
    -> burnStateRelation from amt s s'.


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


Lemma balanceOf_sum_transfer_from map from amt addr acc :
  0 <= from ->
  balanceOf_sum' (transfer_from map from amt) addr acc =
  if (Z.to_nat from <=? addr)%nat then balanceOf_sum' map addr acc - amt else balanceOf_sum' map addr acc.
Proof.
  intros Hleq1.
  erewrite balanceOf_sum_thm with (f := transfer_from map from amt) (f' := map) (x := from); eauto.

  - destruct (Z.to_nat from <=? addr)%nat eqn:Hleq.

    unfold transfer_from. rewrite Z.eqb_refl. lia.

    reflexivity.

  - intros. unfold transfer_from. eapply Z.eqb_neq in H.
    rewrite Z.eqb_sym, H. reflexivity.
Qed.

Lemma balanceOf_sum_burnFrom map from amt addr acc map' :
  0 <= from ->
  burnRelation from amt map map' ->
  balanceOf_sum' map' addr acc =
  if (Z.to_nat from <=? addr)%nat then balanceOf_sum' map addr acc - amt else balanceOf_sum' map addr acc.
Proof.
  intros Hleq1 Hburn.
  destruct Hburn as [HburnFrom HburnElse].
  erewrite balanceOf_sum_thm with (f := map') (f' := map) (x := from); eauto.

  - destruct (Z.to_nat from <=? addr)%nat eqn:Hleq.
    lia. lia.

  - intros. rewrite Z.eq_sym_iff. apply HburnElse. lia.
Qed.

Lemma balanceOf_sum_mintTo map to amt addr acc map':
  0 <= to ->
  mintRelation to amt map map' ->
  balanceOf_sum' map' addr acc =
  if (Z.to_nat to <=? addr)%nat then balanceOf_sum' map addr acc + amt else balanceOf_sum' map addr acc.
Proof.
  intros Hleq1 Hmint.
  destruct Hmint as [HmintFrom HmintElse].
  erewrite balanceOf_sum_thm with (f := map') (f' := map) (x := to); eauto.

  - destruct (Z.to_nat to <=? addr)%nat eqn:Hleq.
    lia. lia.

  - intros. rewrite Z.eq_sym_iff. apply HmintElse. lia.
Qed.

Ltac convert_neq :=
  repeat match goal with
    [ H : _ <> _ |- _ ] => let H_og := fresh H "'" in eapply not_eq_sym in H as H_og; eapply Z.eqb_neq in H; eapply Z.eqb_neq in H_og
  end.

Ltac convert_eq :=
  repeat match goal with
    [ H : _ = _ |- _ ] => let H_og := fresh H "'" in eapply eq_sym in H as H_og; eapply Z.eqb_eq in H; eapply Z.eqb_eq in H_og
  end.

Ltac destructAnds :=
  repeat match goal with
    [ H : _ /\ _ |- _ ] => destruct H
  end.

Ltac rewrite_eqs :=
  repeat match goal with
    [ H : _ =? _ = _ |- _ ] => rewrite H
  end.

Theorem transfer_burn_mint from to amt map imap map':
  0 <= from ->
  0 <= to ->
  transferRelation from to amt map map' ->
  imap = (fun p => if p =? from then map p - amt else map p) ->
  (burnRelation from amt map imap
  /\ mintRelation to amt imap map').
Proof.
  intros Hleq1 Hleq2 Htransfer Himap.
  rewrite Himap in *.
  split.
  - constructor.
    + rewrite Z.eqb_refl. lia.
    + destruct Htransfer; intros p Hpleq; convert_neq; rewrite_eqs; reflexivity.
  - constructor.
    + destruct Htransfer.
      * convert_neq. rewrite_eqs. assumption.
      * convert_eq. rewrite_eqs. rewrite H0. lia.
    + destruct Htransfer; intros p Hpneq.
      * destruct (p =? from) eqn:HpFrom.
        -- apply Z.eqb_eq in HpFrom. rewrite HpFrom. lia.
        -- apply H0; [apply Z.eqb_neq| ]; assumption.
      * convert_neq. rewrite H. rewrite_eqs. rewrite H0. lia.
Qed.


Theorem transfer_thm map from to amt addr acc: forall map',
  to <> from ->
  0 <= from <= Z.of_nat addr ->
  0 <= to <= Z.of_nat addr ->
  transferRelation from to amt map map' ->
  balanceOf_sum' map' addr acc  = balanceOf_sum' map addr acc.
Proof.
  intros map' Hneq Hleq1 Hleq2 Htransfer.
  eapply transfer_burn_mint in Htransfer.
  4: constructor.
  remember (fun p : Z => if p =? from then map p - amt else map p) as imap.
  destruct Htransfer.
  - rewrite balanceOf_sum_mintTo with (map' := map') (map := imap) (to := to) (amt := amt); [ | lia | assumption ].
    + rewrite leb_correct; [ | lia];
      rewrite balanceOf_sum_burnFrom with (map' := imap) (map := map) (from := from) (amt := amt).
        -- rewrite leb_correct; lia.
        -- lia.
        -- assumption.
  - lia.
  - lia.
Qed.

Lemma balances_after_transfer STATE src dst amount STATE' :
  0 <= src <= MAX_ADDRESS ->
  0 <= dst <= MAX_ADDRESS ->
  src <> dst ->
  transferStateRelation src dst amount STATE STATE' ->
  balanceOf_sum STATE = balanceOf_sum STATE' .
Proof.
  intros. unfold balanceOf_sum; simpl.
  apply Z.eq_sym_iff.
  apply transfer_thm with (from := src) (to := dst) (amt := amount).

  + lia.
  + lia.
  + lia.
  + destruct H2.
    assumption.
Qed.

Lemma balances_after_burn STATE src  amount STATE' :
  0 <= src <= MAX_ADDRESS ->
  burnStateRelation src amount STATE STATE' ->
  balanceOf_sum STATE - amount =
  balanceOf_sum STATE'.
Proof.
  intros. unfold balanceOf_sum; simpl.

  assert (forall map amt addr acc map', src <= addr ->
    burnRelation src amt map map' ->
    balanceOf_sum' map' (Z.to_nat addr) acc =
    balanceOf_sum' map (Z.to_nat addr) acc - amt) as HburnFrom.
  { intros. rewrite balanceOf_sum_burnFrom with (map := map) (from := src) (amt := amt); [ | lia | assumption ].

    destruct (Z.to_nat src <=? Z.to_nat addr0)%nat eqn:Hleq.
    + reflexivity.
    + apply Nat.leb_nle in Hleq. lia.
  }

  rewrite Z.eq_sym_iff.
  apply HburnFrom; [lia | ].
  destruct H0.
  assumption.
Qed.

Lemma balances_after_mint STATE dst amount STATE':
  0 <= dst <= MAX_ADDRESS ->
  mintStateRelation dst amount STATE STATE' ->
  balanceOf_sum STATE + amount =
  balanceOf_sum STATE'.
Proof.
  intros. unfold balanceOf_sum; simpl.

  assert (forall map amt addr acc map', dst <= addr ->
  mintRelation dst amt map map' ->
  balanceOf_sum' map' (Z.to_nat addr) acc =
  balanceOf_sum' map (Z.to_nat addr) acc + amt) as HmintTo.
  { intros. rewrite balanceOf_sum_mintTo with (map := map) (to := dst) (amt := amt); [ | lia | assumption ].

    destruct (Z.to_nat dst <=? Z.to_nat addr0)%nat eqn:Hleq.
    + reflexivity.
    + apply Nat.leb_nle in Hleq. lia.
  }

  rewrite Z.eq_sym_iff.
  apply HmintTo; [lia | ].
  destruct H0.
  assumption.
Qed.

Theorem initialSupply': forall ENV _totalSupply (n : nat), forall NA NA' STATE,
    0 <= Caller ENV ->
    constructor NA ENV _totalSupply STATE NA' ->
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
    constructor NA ENV _totalSupply STATE NA' ->
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

Theorem constant_balanceOf : forall STATE,
    reachable STATE ->
    balanceOf_sum STATE = totalSupply STATE.
Proof.
  intros STATE Hreach.
  destruct Hreach as [ BASE Hreach ], Hreach as [ Hinit Hmulti ].

  induction Hmulti as [ | STATE NEXT Hstep ].
  - destruct Hinit as [ENV ? ? ? Hcnstr].
    eapply initialSupply.
    2: eassumption.
    destruct Hcnstr as [? Hinit _ _], Hinit.
    unfold MAX_ADDRESS.
    split; lia.

  - assert ( forall a b, a - (a - b) = b) as Ha1. lia.
    assert ( forall a b c,
      a - b =  c <-> a - c = b) as Ha2. lia.
    assert ( forall a b, a - (a + b) = - b) as Ha3. lia.
    assert ( forall a b c,
      a - b = -c <-> a + c = b) as Ha4. lia.

    destruct Hstep as [NA [NA' [ENV Hextstep]]].
    destruct Hextstep as [NA NA'  ENV STATE STATE' Hstep].
    destruct Hstep.
    + remember STATE' eqn:Hstate'.
      destruct H.
      * apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [ assumption | simpl; destruct H ].
        simpl.
        rewrite Hstate'. unfold MAX_ADDRESS in *.
        rewrite Z.sub_diag with (n := totalSupply STATE);
        apply Zeq_minus;
        eapply (balances_after_transfer) with (src := Caller ENV) (dst := to) (amount := _value); [ | |simpl |]. try split; unfold MAX_ADDRESS; try split; try lia. unfold MAX_ADDRESS. lia. lia.
        constructor.
        {
          constructor.
          - lia.
          - intros p Hneq1 Hneq2.
            rewrite <- Hstate'.
            simpl. convert_neq. rewrite_eqs. reflexivity.
          - rewrite <- Hstate'.
            simpl. convert_neq. rewrite_eqs. rewrite Z.eqb_refl. lia.
          - rewrite <- Hstate'.
            simpl. convert_neq. rewrite_eqs. rewrite Z.eqb_refl. lia.
            }
      * simpl. rewrite <- IHHmulti. reflexivity.
    + remember STATE' eqn:Hstate'.
      destruct H.
      * apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [ assumption | simpl; destruct H ].
        simpl.
        rewrite Hstate'. unfold MAX_ADDRESS in *.
        rewrite Z.sub_diag with (n := totalSupply STATE);
        apply Zeq_minus;
        eapply (balances_after_transfer) with (src := src) (dst := dst) (amount := amount); [ | |simpl |]. try split; unfold MAX_ADDRESS; try split; try lia. unfold MAX_ADDRESS. lia. lia.
        constructor.
        {
          constructor.
          - lia.
          - intros p Hneq1 Hneq2.
            rewrite <- Hstate'.
            simpl. convert_neq. rewrite_eqs. reflexivity.
          - rewrite <- Hstate'.
            simpl. convert_neq. rewrite_eqs. rewrite Z.eqb_refl. lia.
          - rewrite <- Hstate'. destruct H0.
            simpl. convert_neq. rewrite_eqs. rewrite Z.eqb_refl. lia.
            }
      * apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [ assumption | simpl; destruct H ].
        simpl.
        rewrite Hstate'. unfold MAX_ADDRESS in *.
        rewrite Z.sub_diag with (n := totalSupply STATE);
        apply Zeq_minus;
        eapply (balances_after_transfer) with (src := src) (dst := dst) (amount := amount); [ | |simpl |]. try split; unfold MAX_ADDRESS; try split; try lia. unfold MAX_ADDRESS. lia. lia.
        constructor.
        {
          constructor.
          - lia.
          - intros p Hneq1 Hneq2.
            rewrite <- Hstate'.
            simpl. convert_neq. rewrite_eqs. reflexivity.
          - rewrite <- Hstate'.
            simpl. convert_neq. rewrite_eqs. rewrite Z.eqb_refl. lia.
          - rewrite <- Hstate'. destruct H0. destruct H0.
            simpl. convert_neq. rewrite_eqs. rewrite Z.eqb_refl. lia.
            }
      * apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [ assumption | simpl; destruct H ].
        simpl.
        rewrite Hstate'. unfold MAX_ADDRESS in *.
        rewrite Z.sub_diag with (n := totalSupply STATE);
        apply Zeq_minus;
        eapply (balances_after_transfer) with (src := src) (dst := dst) (amount := amount); [ | |simpl |]. try split; unfold MAX_ADDRESS; try split; try lia. unfold MAX_ADDRESS. lia. lia.
        constructor.
        {
          constructor.
          - lia.
          - intros p Hneq1 Hneq2.
            rewrite <- Hstate'.
            simpl. convert_neq. rewrite_eqs. reflexivity.
          - rewrite <- Hstate'.
            simpl. convert_neq. rewrite_eqs. rewrite Z.eqb_refl. lia.
          - rewrite <- Hstate'. destruct H0. destruct H0.
            simpl. convert_neq. rewrite_eqs. rewrite Z.eqb_refl. lia.
            }
      * simpl. rewrite <- IHHmulti at 2. reflexivity.
      * simpl. rewrite <- IHHmulti at 2. reflexivity.
    + destruct H; simpl; rewrite <- IHHmulti; unfold balanceOf_sum;  simpl; reflexivity.
    + remember STATE' eqn:Hstate'.
      destruct H.
      * apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [ assumption | simpl; destruct H ].
        simpl.
        rewrite Hstate'. unfold MAX_ADDRESS in *.
        rewrite Ha1. rewrite Ha2.
        eapply (balances_after_burn) with (src := Caller ENV) (amount := amount); [ unfold MAX_ADDRESS; split; lia | simpl ].
        constructor.
        constructor.
        -- rewrite <- Hstate'; simpl. rewrite Z.eqb_refl. lia.
        -- intros p Hneq.
           rewrite <- Hstate'; simpl. convert_neq. rewrite_eqs. lia.
    + remember STATE' eqn:Hstate'.
      destruct H.
      * apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [ assumption | simpl; destruct H ].
        rewrite Hstate'.
        rewrite Ha1. rewrite Ha2.
        eapply (balances_after_burn) with (src := src) (amount := amount); [ unfold MAX_ADDRESS; split; lia | simpl ].
        constructor.
        constructor.
        -- rewrite <- Hstate'; simpl. rewrite Z.eqb_refl. lia.
        -- intros p Hneq.
           rewrite <- Hstate'; simpl. convert_neq. rewrite_eqs. lia.
      * apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [ assumption | simpl; destruct H ].
        rewrite Hstate'.
        rewrite Ha1. rewrite Ha2.
        eapply (balances_after_burn) with (src := src) (amount := amount); [ unfold MAX_ADDRESS; split; lia | simpl ].
        constructor.
        constructor.
        -- rewrite <- Hstate'; simpl. rewrite Z.eqb_refl. lia.
        -- intros p Hneq.
           rewrite <- Hstate'; simpl. convert_neq. rewrite_eqs. lia.
      * apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [ assumption | simpl; destruct H ].
        rewrite Hstate'.
        rewrite Ha1. rewrite Ha2.
        eapply (balances_after_burn) with (src := src) (amount := amount); [ unfold MAX_ADDRESS; split; lia | simpl ].
        constructor.
        constructor.
        -- rewrite <- Hstate'; simpl. rewrite Z.eqb_refl. lia.
        -- intros p Hneq.
           rewrite <- Hstate'; simpl. convert_neq. rewrite_eqs. lia.
    + remember STATE' eqn:Hstate'.
      destruct H.
      * apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [ assumption | simpl; destruct H ].
        rewrite Hstate'.
        rewrite Ha3. rewrite Ha4.
        eapply (balances_after_mint) with (dst := dst) (amount := amount); [ unfold MAX_ADDRESS; split; lia | simpl ].
        constructor.
        constructor.
        -- rewrite <- Hstate'; simpl. rewrite Z.eqb_refl. lia.
        -- intros p Hneq.
           rewrite <- Hstate'; simpl. convert_neq. rewrite_eqs. lia.
    + remember STATE' eqn:Hstate'.
      destruct H.
      * apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [ assumption | simpl; destruct H ].
        rewrite Hstate'. rewrite Z.sub_diag with (n := totalSupply STATE).
        apply Zeq_minus.
        rewrite <- Hstate'; simpl. unfold balanceOf_sum;  simpl; reflexivity.
    + destruct H. simpl. unfold balanceOf_sum. rewrite <- IHHmulti.  simpl; reflexivity.
    + destruct H. simpl. unfold balanceOf_sum. rewrite <- IHHmulti.  simpl; reflexivity.
Qed.
