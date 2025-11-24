(* depends on StateMachine.v *)

Require Import StateMachine.StateMachine.
Require Import ActLib.ActLib.
Require Import Stdlib.ZArith.ZArith.
Open Scope Z_scope.

Import StateMachine.

Theorem invariant : forall s, reachable s -> (x s) >= 0 /\ (x s) <= 2.
Proof.
  intros. destruct H as [s0 Hreach].
  destruct Hreach as [ Hinit Hmulti ].
  destruct Hmulti as [ | s s' Hstep];
      [destruct Hinit | destruct Hstep as [e Hextstep];
                        destruct Hextstep as [e s s' HSMstep];
                        destruct HSMstep as [e s Hconds | e s Hconds | e s Hconds]].
  {
    simpl. split.
    - intros contra. discriminate.
    - intros contra. discriminate.
  } {
    simpl. split.
    - intros contra. discriminate.
    - intros contra. discriminate.
  } {
    simpl. split.
    - intros contra. discriminate.
    - intros contra. discriminate.
  } {
    simpl. split.
    - intros contra. discriminate.
    - intros contra. discriminate.
  }
Qed. Check invariant.

