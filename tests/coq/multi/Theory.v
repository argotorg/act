Require Import Multi.Multi.
Require Import Stdlib.ZArith.ZArith.
Require Import ActLib.ActLib.


Import C.


Theorem reachable_value_f S:
  reachable S ->
  forall p, A.f (B.a (b S)) p = 0 \/ A.f (B.a (b S)) p = 2 \/ A.f (B.a (b S)) p = 1.
Proof.
  intros HR p. destruct HR as [S0 Hreach], Hreach as [ Hinit Hmulti ].
  induction Hmulti as [ | S' S'' Hstep ].
  - destruct Hinit. simpl; eauto.

  - destruct Hstep as [ENV Hextstep].
    destruct Hextstep as [ ENV s s' HCstep
                         | ENV s s' _ HBstep].
    + destruct HCstep as [ENV i s| ENV i s]; simpl.
      * destruct (p =? i).
        -- right. left. reflexivity.
        -- assumption.
      * assumption.
    + destruct HBstep as [ ENV sb sb' HBstep
                         | ENV sb sb' _ HAextstep].
      * destruct HBstep; simpl.
        -- assumption.
        -- destruct (p =? i).
           ++ right; right; reflexivity.
           ++ assumption.
      * destruct HAextstep as [ENV sa sa' HAstep].
        destruct HAstep.
Qed.

Theorem reachable_value_x S:
  reachable S ->
  w S = 0 \/ w S = 1.
Proof.
  intros HR. destruct HR as [ S0 Hreach], Hreach as [ Hinit Hmulti ].
  induction Hmulti as [ | S' S'' Hstep ]. 
  - destruct Hinit; auto.
  - destruct Hstep as [ENV Hextstep].
    destruct Hextstep as [ENV s s' HCstep | ENV s s' _ HBstep _ Hw_const].
    + destruct HCstep; simpl.
      * assumption.
      * auto.
    + destruct HBstep; rewrite <- Hw_const; assumption.
Qed.
