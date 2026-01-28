Require Import SafeMath.SafeMath.
Require Import ActLib.ActLib.
Require Import Stdlib.ZArith.ZArith.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Import SafeMath.

(* trivial observation that there is only one possible state *)
Lemma state_constant : forall s, exists addr a, s = state addr a.
Proof.
  intros.
  destruct s.
  exists addr0, BALANCE0.
  reflexivity.
Qed.

Theorem mul_correct : forall na e s x y,
  mul_conds e x y s na ->
  range256 x /\ range256 y /\ range256 (x * y) <-> mul_ret e x y s na (x * y).
Proof.
  intros.
  split. {
    intros.
    destruct H.
    destruct H0 as [Hx [Hy Hxy]].
    unfold range256 in *.
    apply mul0_ret.
    - constructor;
      repeat split; try lia. assumption.
    - trivial.
  } {
    intros Hmul_ret. destruct Hmul_ret. destruct H0.
    split; unfold range256;  lia.
  }
Qed.


Theorem mul_is_mul :
  forall na e s x y z,
    mul_ret e x y s na z ->
    z = x * y.
Proof.
  intros. inversion H.
  reflexivity.
Qed.
