Require Import Exponent.Exponent.
Require Import ActLib.ActLib.
Require Import Stdlib.ZArith.ZArith.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Import Exponent.

Lemma pow_pred : forall a e, 0 < e -> a * a ^ (Z.pred e) = a ^ e.
Proof.
  intros a e Hlt.
  apply eq_sym.
  replace (a ^ e) with (a ^ (Z.succ (Z.pred e))).
  - apply Z.pow_succ_r.
    apply Zlt_0_le_0_pred.
    assumption.
  - rewrite (Z.succ_pred e).
    reflexivity.
Qed.

Definition invariantProp (ENV : Env) (b0 : Z) (e0 : Z) (STATE : State) :=
  (r STATE) * (b STATE) ^ ((e STATE) - 1) = b0 ^ e0.

Lemma invInitProof : invariantInit invariantProp.
Proof.
  unfold invariantProp.
  intros env _b _e Hinit .
  simpl.
  rewrite Z.sub_1_r.
  rewrite pow_pred.
  - reflexivity.
  - destruct Hinit.
    apply Z.gt_lt.
    assumption.
Qed.

Lemma invStepProof : invariantStep invariantProp.
Proof.
  unfold invariantProp.
  intros env _b _e s s' Hinit Hstep HinvPre.
  destruct Hstep as [ENV STATE HstepConds].
  simpl.
  rewrite Z.sub_1_r.
  rewrite <- Z.mul_assoc.
  rewrite pow_pred with (a := b STATE) (e := e STATE - 1).
  - assumption.
  - destruct HstepConds.
    lia.
Qed.

Lemma invariant : forall env b0 e0 s,
  reachableFromInit env b0 e0 s -> (r s) * (b s) ^ ((e s) - 1) = b0 ^ e0.
Proof.
  intros env b0 e0 s Hreach.
  apply invariantReachable with (IP := invariantProp) (ENV := env).
  - exact invInitProof.
  - exact invStepProof.
  - assumption.
Qed.

Theorem exp_correct : forall env b0 e0 s,
  reachableFromInit env b0 e0 s -> e s = 1 -> r s = b0 ^ e0.
Proof.
  intros env b0 e0 s H He.
  apply invariant in H.
  rewrite He in H. simpl in H.
  rewrite (Z.mul_1_r (r s)) in H.
  assumption.
Qed.
