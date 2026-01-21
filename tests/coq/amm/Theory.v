Require Import Stdlib.ZArith.ZArith.
Require Import ActLib.ActLib.
Require Stdlib.Strings.String.
From Stdlib Require Import Lia.


Require Import AMM.AMM.

Import Amm.

Definition MAX_ADDRESS := UINT_MAX 160.

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

Lemma le_neq_lt : forall n : Z, 0 <= n -> n <> 0 -> 0 < n.
Proof.
  lia.
Qed.

Lemma div_prop:
     forall a b c,
     0 <= b
  -> 0 <= c
  -> 0 < a + c
  -> a * b <= (a + c) * (b - b * c / (a + c)).
Proof.
  intros a b c HbNonneg HcNonneg HacPos.
  rewrite Z.mul_sub_distr_l.
  rewrite Z.mul_comm with (n := a + c) (m := b).
  rewrite Z.mul_add_distr_l.
  rewrite Z.mul_comm with (n := a) (m := b).
  rewrite Zplus_0_r_reverse with (n := b*a) at 1.
  rewrite <- Z.add_sub_assoc.
  apply -> Z.add_le_mono_l.
  apply Z.le_0_sub.
  rewrite <- Z.div_mul with (a := b*c) (b := a + c) at 2.
  - rewrite Z.mul_comm with (n := b*c) (m:= a+c).
    apply Z.div_mul_le; lia.
  - lia.
Qed.

Lemma div_prop2:
     forall a b c,
     0 <= b
  -> 0 <= c
  -> 0 < b + c
  -> (a - a * c / (b + c)) * (b + c) <= a * b + b + c.
Proof.
  intros a b c HbNonneg HcNonneg HacPos.
  rewrite Z.mul_sub_distr_r.
  rewrite Z.mul_add_distr_l.
  rewrite <- Z.add_sub_assoc.
  rewrite <- Z.add_assoc.
  apply -> Z.add_le_mono_l.
  rewrite <- Z.mul_comm with (m := a * c / (b + c)).
  rewrite <- Z.mod_eq.
  - apply Z.lt_le_incl.
    apply Z.mod_pos_bound.
    lia.
  - lia.
Qed.

Lemma mod_prop:
     forall a b c,
     0 < a + c
  -> (a + c) * (b - b * c / (a + c)) <= a * b + a + c.
Proof.
  intros a b c  HacPos.
  rewrite Z.mul_sub_distr_l.
  rewrite Z.mul_add_distr_r.
  rewrite <- Z.add_sub_assoc.
  rewrite <- Z.add_assoc.
  apply -> Z.add_le_mono_l.
  rewrite Z.mul_comm at 1.
  rewrite <- Z.mod_eq.
  - apply Z.lt_le_incl.
    apply Z.mod_pos_bound; lia.
  - lia.
Qed.

Lemma mod_prop2:
     forall a b c,
     0 < b + c
  -> (a * b) <= (a - a * c / (b + c)) * (b + c).
Proof.
  intros a b c  HacPos.
  rewrite Z.mul_sub_distr_r.
  rewrite Z.mul_add_distr_l.
  rewrite <- Z.add_sub_assoc.
  rewrite Zplus_0_r_reverse with (n := a*b) at 1.
  apply -> Z.add_le_mono_l.
  rewrite <- Z.mul_comm with (m := a * c / (b + c)).
  rewrite <- Z.mod_eq.
  - apply Z.mod_pos_bound.
    lia.
  - lia.
Qed.

Lemma swap0_post0_witness : swap0_post0.
Proof.
  intros NA NA' ENV STATE STATE' amt HConds Hreach Htransition.
  destruct HConds.
  destruct Htransition; simpl.
  - destructAnds. convert_neq. rewrite_eqs.
    rewrite Z.eqb_refl.
    apply div_prop; lia.
  - destructAnds. convert_neq. rewrite_eqs.
    rewrite Z.eqb_refl.
    apply div_prop; lia.
  - reflexivity.
Qed.

Lemma swap0_post1_witness : swap0_post1.
Proof.
  intros NA NA' ENV STATE STATE' amt HConds Hreach Htransition.
  destruct HConds.
  destruct Htransition; simpl.
  - destructAnds. convert_neq. rewrite_eqs.
    rewrite Z.eqb_refl.
    apply mod_prop. lia.
  - destructAnds. convert_neq. rewrite_eqs.
    rewrite Z.eqb_refl.
    apply mod_prop; lia.
  - lia.
Qed.

Lemma swap1_post0_witness : swap1_post0.
Proof.
  intros NA NA' ENV STATE STATE' amt HConds Hreach Htransition.
  destruct HConds.
  destruct Htransition; simpl.
  - destructAnds. convert_neq. rewrite_eqs.
    rewrite Z.eqb_refl.
    apply mod_prop2; lia.
  - destructAnds. convert_neq. rewrite_eqs.
    rewrite Z.eqb_refl.
    apply mod_prop2; lia.
  - reflexivity.
Qed.

Lemma swap1_post1_witness : swap1_post1.
Proof.
  intros NA NA' ENV STATE STATE' amt HConds Hreach Htransition.
  destruct HConds.
  destruct Htransition; simpl.
  - destructAnds. convert_neq. rewrite_eqs.
    rewrite Z.eqb_refl.
    apply div_prop2; lia.
  - destructAnds. convert_neq. rewrite_eqs.
    rewrite Z.eqb_refl.
    apply div_prop2; lia.
  - lia.
Qed.

