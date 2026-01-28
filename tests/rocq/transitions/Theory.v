(* depends on StateMachine.v *)

Require Import StateMachine.StateMachine.
Require Import ActLib.ActLib.
Require Import Stdlib.ZArith.ZArith.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Import StateMachine.

Theorem invariant : forall s, reachable s -> (x s) >= 0 /\ (x s) <= 2.
Proof.
  intros. destruct H as [s0 Hreach].
  destruct Hreach as [ Hinit Hmulti ].
  destruct Hmulti as [ | s s' Hstep];
      [destruct Hinit | destruct Hstep as [e Hextstep];
                        destruct Hextstep as [e' s'' s''' HSMstep]
                        ].
  {
    destruct H.
    simpl. split.
    - intros contra. discriminate.
    - intros contra. discriminate.
  } {
    destruct s''.
    destruct H.
    destruct H.
    destruct H.
    simpl. split.
    - intros contra. discriminate.
    - intros contra. discriminate.
    - destruct H. destruct H; simpl. lia.
    - destruct H. destruct H; simpl. lia.
  }
Qed.

