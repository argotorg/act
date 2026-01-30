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

Definition invariantProp (ENV : Env) (b0 : Z) (e0 : Z) (NextAddr : address) (STATE : State) :=
  (r STATE) * (b STATE) ^ ((e STATE) - 1) = b0 ^ e0.

Lemma invInitProof : invariantInit invariantProp.
Proof.
  unfold invariantProp.
  intros env _b _e na s na' Hinit .
  simpl.
  destruct Hinit; simpl.
  rewrite Z.sub_1_r.
  rewrite pow_pred.
  - reflexivity.
  - destruct H_conds.
    apply Z.gt_lt.
    assumption.
Qed.

Lemma invStepProof : invariantStep invariantProp.
Proof.
  unfold invariantProp.
  intros env _b _e na s s' Hinit Hstep HinvPre.
  destruct Hstep as [e Hestep].
  destruct Hestep as [NA [NA' Hestep]].
  destruct Hestep.
  induction H.
  destruct H.
  destruct H_conds.
  simpl.
  rewrite Z.sub_1_r.
  rewrite <- Z.mul_assoc.
  rewrite pow_pred with (a := b s) (e := Exponent.e s - 1).
  - assumption.
  - lia.
Qed.

Lemma invariant : forall na env b0 e0 s,
  reachableFromInit env b0 e0 na s -> (r s) * (b s) ^ ((e s) - 1) = b0 ^ e0.
Proof.
  intros na env b0 e0 s Hreach.
  eapply invariantReachable with (IP := invariantProp) (ENV := env).
  - exact invInitProof.
  - exact invStepProof.
  - eassumption.
Qed.

Theorem exp_correct : forall na env b0 e0 s,
  reachableFromInit env b0 e0 na s -> e s = 1 -> r s = b0 ^ e0.
Proof.
  intros na env b0 e0 s H He.
  eapply invariant in H.
  rewrite He in H. simpl in H.
  rewrite (Z.mul_1_r (r s)) in H.
  assumption.
Qed.
