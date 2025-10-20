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

Lemma unique_pointers : forall STATE STATE',
     step STATE STATE'
  -> noAliasing STATE
  -> noAliasing STATE' . Proof.
  intros s s' Hstep Hnoalias.
  unfold noAliasing in Hnoalias.
  unfold step in Hstep.
  destruct Hstep as [ENV Hestep].
  destruct Hestep as [ENV s s' Hstep | ENV s s' Hstep | ENV s s' Hstep].
  - destruct Hstep. 
    unfold noAliasing.
    unfold f0_conds, envStateConstraint in H.
    repeat split; simpl.
    + lia.
    + apply Z.neq_sym.
      apply Z.lt_neq.
      apply Z.lt_trans with (n := cu1 STATE) (m := NextAddr ENV0) (p := NextAddr ENV0 + 1 +1 +1).
      * destructAnds.
        apply Z.gt_lt.
        apply H29 with (p := cu1 STATE).
        apply address_cu1.
      * lia.
    + apply Z.neq_sym.
      apply Z.lt_neq.
      apply Z.lt_trans with (n := cu2 STATE) (m := NextAddr ENV0) (p := NextAddr ENV0 + 1 +1 +1).
      * destructAnds.
        apply Z.gt_lt.
        apply H29 with (p := cu2 STATE).
        apply address_cu2.
      * lia.
    + intros p HaddrIn.
      apply Z.neq_sym.
      apply Z.lt_neq.
      apply Z.lt_trans with (n := p) (m := NextAddr ENV0) (p := NextAddr ENV0 + 1 +1 +1).
      * destructAnds.
        apply Z.gt_lt.
        apply H29.
        apply address_a1; assumption.
      * lia.
    + intros p HaddrIn.
      apply Z.neq_sym.
      * destruct Hnoalias. destruct H1. destruct H2. destruct H3. destruct H4.
        apply Z.neq_sym.
        apply H4 ; assumption.
    + intros p HaddrIn.
      apply Z.neq_sym.
      * destruct Hnoalias. destruct H1. destruct H2. destruct H3. destruct H4. destruct H5.
        apply Z.neq_sym.
        apply H5 ; assumption.
    + intros p HaddrIn.
      remember ({|
        B.addr := NextAddr ENV0 + 1 + 1;
        B.bu1 := A.addr pa2;
        B.bu2 := NextAddr ENV0 + 1;
        B.pba := pa1;
        B.y := 0
      |}) eqn:Histate.
      destruct HaddrIn;
      try (rewrite Histate);
      simpl.
      * lia.
      * unfold A.envStateConstraint in H.
        apply Z.neq_sym.
        apply Z.lt_neq.
        apply Z.lt_trans with (n := A.addr pa2) (m := NextAddr ENV0).
        -- destruct H. destruct H0. destruct H1. destruct H2. destruct H3. destruct H4. destruct H5.
          apply Z.gt_lt.
           apply H6.
           apply A.address_addr.
        -- lia.
      * lia.
      * unfold A.envStateConstraint in H.
        apply Z.neq_sym.
        apply Z.lt_neq.
        apply Z.lt_trans with (n := p) (m := NextAddr ENV0).
        apply Z.gt_lt.
        -- destructAnds.
           rewrite Histate in H0.
           simpl in H0.
           apply H31; assumption.
        -- lia.
    + intros p HaddrIn.
      remember ({|
        B.addr := NextAddr ENV0 + 1 + 1;
        B.bu1 := A.addr pa2;
        B.bu2 := NextAddr ENV0 + 1;
        B.pba := pa1;
        B.y := 0
      |}) eqn:Histate.
      destruct HaddrIn;
      try (rewrite Histate);
      simpl.
      * apply Z.lt_neq.
        apply Z.lt_trans with (n := cu1 STATE) (m := NextAddr ENV0).
        -- destructAnds.
           apply Z.gt_lt.
           apply H29.
           apply address_cu1.
        -- lia.
      * destructAnds. auto.
      * apply Z.lt_neq.
        apply Z.lt_trans with (n := cu1 STATE) (m := NextAddr ENV0).
        -- destructAnds.
           apply Z.gt_lt.
           apply H29.
           apply address_cu1.
        -- lia.
      *
        -- destructAnds.
           rewrite Histate in H0.
           simpl in H0.
           destruct H0.
           apply Z.neq_sym. assumption.
    + intros p HaddrIn.
      remember ({|
        B.addr := NextAddr ENV0 + 1 + 1;
        B.bu1 := A.addr pa2;
        B.bu2 := NextAddr ENV0 + 1;
        B.pba := pa1;
        B.y := 0
      |}) eqn:Histate.
      destruct HaddrIn;
      try (rewrite Histate);
      simpl.
      * apply Z.lt_neq.
        apply Z.lt_trans with (n := cu2 STATE) (m := NextAddr ENV0).
        -- destructAnds.
           apply Z.gt_lt.
           apply H29.
           apply address_cu2.
        -- lia.
      * destructAnds. auto.
      * apply Z.lt_neq.
        apply Z.lt_trans with (n := cu2 STATE) (m := NextAddr ENV0).
        -- destructAnds.
           apply Z.gt_lt.
           apply H29.
           apply address_cu2.
        -- lia.
      *
        -- destructAnds.
           rewrite Histate in H0.
           simpl in H0.
           destruct H0.
           apply Z.neq_sym. assumption.
    + intros p p' HaddrInA1 HaddrInBi.
      remember (a1 STATE) eqn:Ha1State.
      destruct HaddrInA1.
      remember ({|
        B.addr := NextAddr ENV0 + 1 + 1;
        B.bu1 := A.addr pa2;
        B.bu2 := NextAddr ENV0 + 1;
        B.pba := pa1;
        B.y := 0
      |}) eqn:Histate.
      destruct HaddrInBi;
      try (rewrite Histate);
      simpl.
      * destructAnds.
        apply Z.lt_neq.
        apply Z.lt_trans with (n := A.addr STATE0) (m := NextAddr ENV0).
        -- apply Z.gt_lt.
           apply H29.
           rewrite Ha1State.
           apply address_a1.
           apply A.address_addr.
        -- lia.
      * destructAnds.
        auto.
      * destructAnds.
        apply Z.lt_neq.
        apply Z.lt_trans with (n := A.addr STATE0) (m := NextAddr ENV0).
        -- apply Z.gt_lt.
           apply H29.
           rewrite Ha1State.
           apply address_a1.
           apply A.address_addr.
        -- lia.
      * rewrite Histate in H0. simpl in H0. destruct H0. destructAnds.
        apply Z.neq_sym.
        assumption.
    +
      apply Z.lt_neq.
      apply Z.lt_trans with (n := A.addr pa2) (m := NextAddr ENV0).
      * unfold A.envStateConstraint in H.
        apply Z.gt_lt.
        destructAnds. 
        apply H31.
        apply A.address_addr.
      * lia.
    + apply Z.neq_sym.
      apply Z.lt_neq.
      apply Z.lt_trans with (m := NextAddr ENV0).
      * apply Z.gt_lt.
        unfold A.envStateConstraint in H.
        destructAnds. 
        apply H31.
        apply A.address_addr.
      * lia.
    + lia.
    + intros p HaddrInPa1.
      apply Z.neq_sym.
      apply Z.lt_neq.
      apply Z.lt_trans with (m := NextAddr ENV0).
      * apply Z.gt_lt.
        unfold A.envStateConstraint in H.
        destructAnds.
        apply H30.
        assumption.
      * lia.
    + intros p HaddrInPa1.
      destruct HaddrInPa1.
      destructAnds.
      apply Z.neq_sym.
      assumption.
    + intros p HaddrInPa1.
      apply Z.neq_sym.
      apply Z.lt_neq.
      apply Z.lt_trans with (m := NextAddr ENV0).
      * apply Z.gt_lt.
        unfold A.envStateConstraint in H.
        destructAnds.
        apply H30.
        assumption.
      * lia.
  - destruct H.
    destruct H.
  - destruct H.
    destruct H.
    destruct H3.
    destruct H3.
  Qed.
