Require Import Stdlib.ZArith.ZArith.
Require Import ActLib.ActLib.
Require Stdlib.Strings.String.
From Stdlib Require Import Lia.

Require Import POINTERS.POINTERS.

Import C.

Ltac destructAnds :=
  repeat match goal with
    [ H : _ /\ _ |- _ ] => destruct H
  end.

Lemma unique_after_step : forall STATE STATE',
     step STATE STATE'
  -> noAliasing STATE
  -> noAliasing STATE' .
Proof.
  intros s s' Hstep Hnoalias.
  destruct Hnoalias as [Hna_a1_addr Hna_b1_addr Hna_a1_b1 Hna_a1 Hna_b1].
  destruct Hstep as [ENV Hestep].
  destruct Hestep as [ na [ e Hestep ]].
  destruct Hestep as [ ENV na s s' na' Hstep
                     | ENV na s s' HenvConstr Hstep
                     | ENV na s s' HenvConstr Hstep Haddr_const Ha1_const].
  - destruct Hstep as [ENV na pa1 pa2 s s'' na' Hstep]. 
    * destruct Hstep.
      constructor.
      + simpl.
        intros p HaddrIn.
        apply Z.neq_sym.
        apply Z.lt_neq.
        apply Z.lt_trans with (n := p) (m := NextAddr ENV).
        * apply Z.gt_lt.
          destruct Hconds.
          apply H11.
          apply address_subcontract.
          apply addressOf_a1.
          assumption.
        * lia.
      + simpl.
        intros p HaddrIn.
        remember ({|
          B.addr := NextAddr ENV + 1 + 1;
          B.bu1 := A.addr pa2;
          B.bu2 := NextAddr ENV + 1;
          B.a := {| A.addr := NextAddr ENV + 1 + 1 + 1; A.x := 17 |};
          B.y := 42
        |}) as s_b1' eqn:Histate_b1.
        destruct HaddrIn as [s_b1| p s_b1 HaddrIn_a];
        try (rewrite Histate_b1); simpl.
        * lia.
        * remember (B.a s_b1) eqn:Histate_b1_a.
          destruct HaddrIn_a.
          rewrite Histate_b1_a, Histate_b1; simpl.
          lia.
    + simpl.
      intros p p' HaddrIn_a1 HaddrIn_b1.
      remember ({|
        B.addr := NextAddr ENV + 1 + 1;
        B.bu1 := A.addr pa2;
        B.bu2 := NextAddr ENV + 1;
        B.a := {| A.addr := NextAddr ENV + 1 + 1 + 1; A.x := 17 |};
        B.y := 42
      |}) eqn:Histate_b1.
      destruct HaddrIn_b1 as [| p' s' HaddrIn_b1_a ].
      * rewrite Histate_b1; simpl.
        apply Z.lt_neq.
        apply Z.lt_trans with (n := p) (m := NextAddr ENV).
        --  apply Z.gt_lt.
            destruct Hconds.
            apply H11.
            apply address_subcontract.
            apply addressOf_a1.
            assumption.
        -- lia.
      * rewrite Histate_b1 in HaddrIn_b1_a; simpl in HaddrIn_b1_a.
        remember ({| A.addr := NextAddr ENV + 1 + 1 + 1; A.x := 17 |}) eqn:Histate_a.
        destruct HaddrIn_b1_a.
        rewrite Histate_a; simpl.
        apply Z.lt_neq.
        apply Z.lt_trans with (n := p) (m := NextAddr ENV).
        --  apply Z.gt_lt.
            destruct Hconds.
            apply H11.
            apply address_subcontract.
            apply addressOf_a1.
            assumption.
        -- lia.
    + simpl. assumption.
    + simpl.
      remember (
        {|
          B.addr := NextAddr ENV + 1 + 1;
          B.bu1 := A.addr pa2;
          B.bu2 := NextAddr ENV + 1;
          B.a := {| A.addr := NextAddr ENV + 1 + 1 + 1; A.x := 17 |};
          B.y := 42
        |}
      ) as s_b1' eqn:Histate_b1.
      constructor.
      * rewrite Histate_b1; simpl.
        intros p HaddrIn_a.
        remember ({| A.addr := NextAddr ENV + 1 + 1 + 1; A.x := 17 |}) as s_b1_a eqn:HaddrIn_b1_a.
        destruct HaddrIn_a.
        rewrite HaddrIn_b1_a; simpl. lia.
      * rewrite Histate_b1; simpl.
        constructor.
  - destruct Hstep as [? ? ? Hstep].
    destruct Hstep.
  - remember (b1 s) as s_b eqn:Hs_b1.
    remember (b1 s') as s_b1' eqn:Hs_b1'.
    destruct Hstep as [? s_b1 s_b1' HBstep | ? s_b1 s_b1' ? HAstep].
    + destruct HBstep as [ENV pa s_b1 Hg0_conds].
      constructor.
      * rewrite <- Haddr_const.
        rewrite <- Ha1_const.
        apply Hna_a1_addr.
      * intros p HaddrIn_b1.
        rewrite <- Haddr_const.
        simpl in Hs_b1'.
        destruct HaddrIn_b1 as [s_b1_ | p s_b1'_ HaddrIn_b1_a].
        -- rewrite <- Hs_b1'; simpl.
          apply Z.lt_neq.
          apply Z.lt_trans with (n := addr s) (m := NextAddr ENV).
          ++  apply Z.gt_lt.
              apply HenvConstr.
              constructor.
          ++ lia.
        -- rewrite <- Hs_b1' in HaddrIn_b1_a; simpl in HaddrIn_b1_a.
           remember ({| A.addr := NextAddr ENV; A.x := 0 |}) as s_b1_a eqn:Hs_b1_a.
           destruct HaddrIn_b1_a as [s_b1_a].
              ** rewrite Hs_b1_a.
                 simpl.
                 apply Z.lt_neq.
                 apply Z.gt_lt.
                 apply HenvConstr.
                 constructor.
      * intros p p' HaddrIn_a1 HaddrIn_b1.
        rewrite <- Ha1_const in HaddrIn_a1.
        simpl in Hs_b1'.
        destruct HaddrIn_b1 as [| p' s_b1' HaddrIn_b1_a]; rewrite <- Hs_b1' in *; simpl.
        -- apply Z.lt_neq.
           apply Z.lt_trans with (n := p) (m := NextAddr ENV).
           ** apply Z.gt_lt.
              apply HenvConstr.
              apply address_subcontract.
              apply addressOf_a1.
              assumption.
           ** lia.
        -- simpl in HaddrIn_b1_a.
           remember ({| A.addr := NextAddr ENV; A.x := 0 |}) as s_b1_a eqn:Hs_b1_a.
           destruct HaddrIn_b1_a; rewrite Hs_b1_a; simpl.
           apply Z.lt_neq.
              apply Z.gt_lt.
              apply HenvConstr.
              apply address_subcontract.
              apply addressOf_a1.
              assumption.
      * rewrite <- Ha1_const.
        assumption.
      * simpl in Hs_b1'.
        constructor;
        rewrite <- Hs_b1'; simpl.
        -- intros p HaddrIn_b1_a.
           remember ({| A.addr := NextAddr ENV; A.x := 0 |}) as s_b1_a eqn:Hs_b1_a.
           destruct HaddrIn_b1_a.
           rewrite Hs_b1_a; simpl.
           lia.
        -- constructor.
    + destruct HAstep as [? s_a1 s_a1' Hastep].
      destruct Hastep.
Qed.


Lemma unique_at_reachable : forall ENV pa1 pa2 STATE,
     reachableFromInit ENV pa1 pa2 STATE
  -> noAliasing (snd (C ENV pa1 pa2))
  -> noAliasing STATE.
Proof.
  intros ENV pa1 pa2 STATE Hreach.
  destruct Hreach as [HinitPrecs Hmulti].
  apply step_multi_step
    with (P := fun s s' => (noAliasing s -> noAliasing s')) in Hmulti.
    - assumption.
    - apply unique_after_step.
    - unfold Relation_Definitions.reflexive; auto.
    - unfold Relation_Definitions.transitive; auto.
Qed.

*)
