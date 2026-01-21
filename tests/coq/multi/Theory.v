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
  - destruct Hinit, H, H, H5, H2, H8. simpl; eauto.

  - destruct Hstep as [NA [NA' [ENV Hextstep]]].
    destruct Hextstep as [ NA NA' ENV s s' HCstep
                         | NA NA' ENV s s' _ _ _ HBstep].
    + destruct HCstep as [ENV i s| ENV i s]; simpl.
      destruct H; simpl.
      * destruct (p =? i0).
        -- right. left. reflexivity.
        -- assumption.
      * destruct H; simpl. assumption.
    + destruct HBstep as [ NA NA' ENV sb sb' HBstep
                         | NA NA' ENV sb sb' _ _ _ HAextstep].
      * destruct HBstep; simpl.
        -- destruct H3; simpl. assumption.
        -- destruct H3; simpl. destruct (p =? i).
           ++ right; right; reflexivity.
           ++ assumption.
      * destruct HAextstep as [NA NA' ENV sa sa' HAstep].
        destruct HAstep.
Qed.

Theorem reachable_value_x S:
  reachable S ->
  w S = 0 \/ w S = 1.
Proof.
  intros HR. destruct HR as [ S0 Hreach], Hreach as [ Hinit Hmulti ].
  induction Hmulti as [ | S' S'' Hstep ]. 
  - destruct Hinit; destruct H; auto.
  - destruct Hstep as [NA [NA' [ENV Hextstep]]].
    destruct Hextstep as [NA NA' ENV s s' HCstep | NA NA' ENV s s' _ _ _ HBstep _ _ Hw_const].
    + destruct HCstep, H; simpl.
      * assumption.
      * auto.
    + edestruct HBstep, HBstep; rewrite <- Hw_const; assumption.
Qed.
