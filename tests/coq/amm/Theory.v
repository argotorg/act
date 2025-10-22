Require Import Stdlib.ZArith.ZArith.
Require Import ActLib.ActLib.
Require Stdlib.Strings.String.
From Stdlib Require Import Lia.


Require Import AMM.AMM.

Import Amm.

Definition MAX_ADDRESS := UINT_MAX 160.

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

Lemma swap00_post0_witness : swap00_post0.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((This ENV =? Caller ENV) = false) as HifCond. lia.
  rewrite HifCond.
  apply div_prop; lia.
Qed.

Lemma swap00_post1_witness : swap00_post1.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((This ENV =? Caller ENV) = false) as HifCond. lia.
  rewrite HifCond.
  apply mod_prop; lia.
Qed.

Lemma swap00_post2_witness : swap00_post2.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((Caller ENV =? This ENV) = false) as HifCond. lia.
  rewrite HifCond.
  lia.
Qed.

Lemma swap00_post3_witness : swap00_post3.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  lia.
Qed.

Lemma swap00_post4_witness : swap00_post4.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((This ENV =? Caller ENV) = false) as HifCond. lia.
  rewrite HifCond.
  lia.
Qed.

Lemma swap00_post5_witness : swap00_post5.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  split.
  - apply Z.add_nonneg_nonneg; lia. 
  - lia.
Qed.

Lemma swap01_post0_witness : swap01_post0.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((This ENV =? Caller ENV) = false) as HifCond. lia.
  rewrite HifCond.
  apply div_prop; lia.
Qed.

Lemma swap01_post1_witness : swap01_post1.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((This ENV =? Caller ENV) = false) as HifCond. lia.
  rewrite HifCond.
  apply mod_prop; lia.
Qed.

Lemma swap01_post2_witness : swap01_post2.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((Caller ENV =? This ENV) = false) as HifCond. lia.
  rewrite HifCond.
  lia.
Qed.

Lemma swap01_post3_witness : swap01_post3.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  lia.
Qed.

Lemma swap01_post4_witness : swap01_post4.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  repeat rewrite Z.eqb_refl.
  simpl.
  destruct HConds.
  lia.
Qed.

Lemma swap01_post5_witness : swap01_post5.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((This ENV =? Caller ENV) = false) as HifCond. lia.
  rewrite HifCond.
  lia.
Qed.

Lemma swap10_post0_witness : swap10_post0.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((This ENV =? Caller ENV) = false) as HifCond. lia.
  rewrite HifCond.
  apply mod_prop2; lia.
Qed.

Lemma swap10_post1_witness : swap10_post1.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((This ENV =? Caller ENV) = false) as HifCond. lia.
  rewrite HifCond.
  apply div_prop2; lia.
Qed.

Lemma swap10_post2_witness : swap10_post2.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((Caller ENV =? This ENV) = false) as HifCond. lia.
  rewrite HifCond.
  lia.
Qed.

Lemma swap10_post3_witness : swap10_post3.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  lia.
Qed.

Lemma swap10_post4_witness : swap10_post4.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((This ENV =? Caller ENV) = false) as HifCond. lia.
  rewrite HifCond.
  lia.
Qed.

Lemma swap10_post5_witness : swap10_post5.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  lia.
Qed.

Lemma swap11_post0_witness : swap11_post0.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((This ENV =? Caller ENV) = false) as HifCond. lia.
  rewrite HifCond.
  apply mod_prop2; lia.
Qed.

Lemma swap11_post1_witness : swap11_post1.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((This ENV =? Caller ENV) = false) as HifCond. lia.
  rewrite HifCond.
  apply div_prop2; lia.
Qed.

Lemma swap11_post2_witness : swap11_post2.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((Caller ENV =? This ENV) = false) as HifCond. lia.
  rewrite HifCond.
  lia.
Qed.

Lemma swap11_post3_witness : swap11_post3.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  lia.
Qed.

Lemma swap11_post4_witness : swap11_post4.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  repeat rewrite Z.eqb_refl.
  simpl.
  destruct HConds.
  lia.
Qed.

Lemma swap11_post5_witness : swap11_post5.
Proof.
  intros ENV STATE STATE' amt HConds Hreach Hstep.
  rewrite Hstep.
  simpl.
  rewrite Z.eqb_refl.
  destruct HConds.
  assert ((This ENV =? Caller ENV) = false) as HifCond. lia.
  rewrite HifCond.
  lia.
Qed.
