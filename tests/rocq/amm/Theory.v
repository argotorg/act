Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.ZArith.Zmin.
Require Import ActLib.ActLib.
Require Stdlib.Strings.String.
From Stdlib Require Import Lia.


Require Import AMM.AMM.

Import Amm.

Definition MAX_ADDRESS := UINT_MAX 160.

Ltac destructAnds :=
  repeat match goal with
    [ H : _ /\ _ |- _ ] => destruct H
  end.

Ltac convert_neq :=
  repeat match goal with
    [ H : _ <> _ |- _ ] => eapply not_eq_sym in H; eapply Z.eqb_neq in H
  end.

Ltac rewrite_eqs :=
  repeat match goal with
    [ H : _ =? _ = _ |- _ ] => rewrite H
  end.


  Ltac rewrite_eqbs :=
  repeat match goal with
  | [ H : ?a = ?b |- context [?a =? ?b] ] =>
    rewrite (proj2 (Z.eqb_eq a b) H)
  | [ H : ?a = ?b |- context [?b =? ?a] ] =>
    rewrite (proj2 (Z.eqb_eq b a) (eq_sym H))
  | [ H : ?a <> ?b |- context [?a =? ?b] ] =>
    rewrite (proj2 (Z.eqb_neq a b) H)
  | [ H : ?a <> ?b |- context [?b =? ?a] ] =>
    rewrite (proj2 (Z.eqb_neq b a) (not_eq_sym H))
  end.

Ltac rewrite_b_right H :=
  match goal with
  | [ H : _ =? _ = true |- _ ] => apply Z.eqb_eq in H as H'; rewrite <- H' in *

    end.

Ltac rewrite_b_left H :=
  match goal with
  | [ H : _ =? _ = true |- _ ] => apply Z.eqb_eq in H as H'; rewrite H' in *
    end.

Ltac bool_to_prop :=
  repeat match goal with
  | [ H : (_ =? _)%Z = true  |- _ ] => apply Z.eqb_eq in H
  | [ H : (_ =? _)%Z = false |- _ ] => apply Z.eqb_neq in H
  | [ H : (_ <? _)%Z = true  |- _ ] => apply Z.ltb_lt in H
  | [ H : (_ <? _)%Z = false |- _ ] => apply Z.ltb_ge in H
  | [ H : (_ <=? _)%Z = true  |- _ ] => apply Z.leb_le in H
  | [ H : (_ <=? _)%Z = false |- _ ] => apply Z.leb_gt in H
  | [ H : (_ >? _)%Z = true  |- _ ] => apply Z.gtb_lt in H
  | [ H : (_ >? _)%Z = false |- _ ] => apply Z.gtb_ltb in H
  | [ H : (_ >=? _)%Z = true  |- _ ] => apply Z.geb_le in H
  | [ H : (_ >=? _)%Z = false |- _ ] => apply Z.geb_leb in H
  end.

Ltac prop_to_bool :=
  repeat match goal with
  | [ H : @eq Z _ _        |- _ ] => apply Z.eqb_eq in H
  | [ H : _ <> _           |- _ ] => apply Z.eqb_neq in H
  | [ H : Z.lt _ _         |- _ ] => apply Z.ltb_lt in H
  | [ H : _ > _            |- _ ] => apply Z.le_antisymm
  | [ H : Z.le _ _         |- _ ] => apply Z.leb_le in H
  | [ H : Z.gt _ _         |- _ ] => apply Z.gtb_lt in H
  | [ H : Z.ge _ _         |- _ ] => apply Z.geb_le in H
  end.

Ltac destruct_ifs :=
  repeat match goal with
  | [ |- context [if ?a =? ?b then _ else _] ] =>
    destruct (a =? b) eqn:?; bool_to_prop
  | [ H : context [if ?a =? ?b then _ else _] |- _ ] =>
    destruct (a =? b) eqn:?; bool_to_prop
  end.




Lemma le_neq_lt : forall n : Z, 0 <= n -> n <> 0 -> 0 < n.
Proof.
  lia.
Qed.

Lemma div_prop:
     forall (a b c : Z),
     0 <= b
  -> 0 <= c
  -> 0 < a + c
  -> a * b <= (a + c) * (b - b * c / (a + c)).
Proof.
  intros a b c HbNonneg HcNonneg HacPos.
  rewrite Z.mul_sub_distr_l with (n :=a + c) (m := b).
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


Lemma ERC20_allowance_zero :
  forall (Before : address) (ENV : Env) (T : Token.State) (a : address),
    Token.reachableBefore Before T
  -> Before <= a
  -> forall i, Token.allowance T a i = 0.
Proof.
  intros Before ENV T a HreachBefore.
  destruct HreachBefore as [T_Init [HinitBefore HmultiBefore]].
  apply step_multi_step

  with (P := fun s s' => (Before <= a -> forall i : address, Token.allowance s a i = 0) ->

                         Before <= a -> forall i : address, Token.allowance s' a i = 0) in HmultiBefore.
    - destruct HinitBefore as [? ? ? ? Hinit H_leq_before].
      apply HmultiBefore.
      destruct Hinit. destruct H_conds; simpl; reflexivity.
    - intros s s' HstepBefore HzeroS.
      destruct HstepBefore as [ENV' [NextAddr [NextAddr' [H_transition H_NextAddr_leq_before]]]].
      destruct H_transition; destruct H;
        try (destruct H; assumption).
      + (* transferFrom *)
        destruct H; simpl; try assumption.
        * destruct (a =? src) eqn:H_a_eq_src.
          -- apply Z.eqb_eq in H_a_eq_src. rewrite <- H_a_eq_src. intros.
            assert (Token.allowance s a (Caller ENV') = 0). auto.
            assert (Caller ENV' <> src) as H_caller_neq_src. { destructAnds. assumption. }
            destruct H_conds. apply H_iff3 in H_caller_neq_src.

            assert (amount = 0). { apply Z.le_antisymm; try lia.
              rewrite <- H_a_eq_src in H_caller_neq_src. rewrite H0 in H_caller_neq_src. lia.
            }
            destruct (i =? Caller ENV'); try lia; auto.
          -- assumption.
        * destruct (a =? src) eqn:H_a_eq_src.
          -- apply Z.eqb_eq in H_a_eq_src. rewrite <- H_a_eq_src. intros.
            assert (Token.allowance s a (Caller ENV') = 0); auto.
            assert (Caller ENV' <> src) as H_caller_neq_src. { destructAnds. assumption. }
            destruct H_conds. apply H_iff3 in H_caller_neq_src.

            assert (amount = 0). { apply Z.le_antisymm; try lia.
              rewrite <- H_a_eq_src in H_caller_neq_src. rewrite H0 in H_caller_neq_src. lia.
            }
            destruct (i =? Caller ENV'); try lia; auto.
          -- assumption.
      + (* approve *)
        destruct H; simpl; try assumption.
        * destruct H_conds; auto.
          intro H_NA_leq_x.
          assert (Caller ENV' < a). {
            apply Z.lt_le_trans with (m := NextAddr).
            * destruct H_envNextAddrConsistent; assumption.
            * lia.
          }
          assert (a =? Caller ENV' = false). simpl. lia.
          rewrite_eqs.
          apply HzeroS. assumption.
      + (* burnFrom *)
        destruct H; simpl; try assumption.
        * destruct (a =? src) eqn:H_a_eq_src.
          -- apply Z.eqb_eq in H_a_eq_src. rewrite <- H_a_eq_src. intros.
            assert (Token.allowance s a (Caller ENV') = 0). auto.
            assert (Caller ENV' <> src) as H_caller_neq_src. { destructAnds. assumption. }
            destruct H_conds. apply H_iff3 in H_caller_neq_src.

            assert (amount = 0). { apply Z.le_antisymm; try lia.
              rewrite <- H_a_eq_src in H_caller_neq_src. rewrite H0 in H_caller_neq_src. lia.
            }
            destruct (i =? Caller ENV'); try lia; auto.
          -- assumption.
    - unfold Relation_Definitions.reflexive. auto.
    - unfold Relation_Definitions.transitive. auto.
Qed.


Definition Amm_allowance_zero_Prop (ENV : Env) (T0 T1 : Token.State) (L : Z) (NextAddr : address) (STATE : State) : Prop :=
  forall i, i <> Amm.addr STATE
  -> Token.allowance (Amm.token0 STATE) (Amm.addr STATE) i = 0 /\
    Token.allowance (Amm.token1 STATE) (Amm.addr STATE) i = 0.

Definition Amm_liq_incr_Prop  (ENV : Env) (T0 T1 : Token.State) (L : Z) (NextAddr : address) (STATE : State) : Prop :=
  ((((Token.balanceOf T0) (addr STATE)) * ((Token.balanceOf T1) (addr STATE))) <= (((Token.balanceOf (Amm.token0 STATE)) (addr STATE)) * ((Token.balanceOf (Amm.token1 STATE)) (addr STATE)))).

Definition Amm_balance_ge_reserve_0_Prop (ENV: Env) (T0 T1 : Token.State) (L : Z) (NextAddr : address) (STATE : State) : Prop :=
  reserve0 STATE <= Token.balanceOf (token0 STATE) (addr STATE).

Definition Amm_balance_ge_reserve_1_Prop (ENV: Env) (T0 T1 : Token.State) (L : Z) (NextAddr : address) (STATE : State) : Prop :=
  reserve1 STATE <= Token.balanceOf (token1 STATE) (addr STATE).

Definition IP (ENV : Env) (T0 T1 : Token.State) (L : Z) (NextAddr : address) (STATE : State) : Prop :=
  Amm_allowance_zero_Prop ENV T0 T1 L NextAddr STATE
  /\ Amm_liq_incr_Prop ENV T0 T1 L NextAddr STATE.

Lemma Amm_allowance_zero_init : invariantInit Amm_allowance_zero_Prop.
Proof.
  intros ENV T0 T1 L NextAddr A NextAddr' Hconstr i Hi_neq.
  simpl in *.
  split.
  - apply ERC20_allowance_zero with (Before := addr A).
    + assumption.
    + destruct Hconstr; destruct H_conds. assumption.
    + reflexivity.
  - apply ERC20_allowance_zero with (Before := addr A).
    + assumption.
    + destruct Hconstr; destruct H_conds. assumption.
    + reflexivity.
Qed.


Ltac rewrite_eqb H :=
  match H with
  | _ =? _ = true => apply Z.eqb_eq in H as H'; rewrite H'
  | _ =? _ = false => apply Z.eqb_neq in H as H'; rewrite H'
  end.

Lemma Amm_allowance_zero_step : invariantStep Amm_allowance_zero_Prop.
Proof.
  unfold invariantStep, Amm_allowance_zero_Prop.
  intros ENV0 T0 T1 L NextAddr0 STATE0 STATE0' HinitPrecs Hstep Hyp i Hi_neq.
  destruct Hstep as [ENV0' [NextAddr [NextAddr' Htransition]]].
  destruct Htransition
    as [

       | H_stateConsistent HTokenTransition Haddr_const _ _ _ _ _ Htk1_const
       | H_stateConsistent HTokenTransition Haddr_const _ _ _ _ _ Htk0_const].
  - destruct H; destruct H; simpl; auto.
  - destruct HTokenTransition; destruct H0; rewrite <- Haddr_const in *; rewrite <- Htk1_const.
    + destruct H0; simpl; auto.
    + (* transferFrom *)
      destruct H0; simpl; auto.
      * destruct (addr STATE0 =? src) eqn:Hif_cond1, (i =? Caller ENV0')%bool eqn:Hif_cond2; auto.
        -- (* true, true *)
        assert (Caller ENV0' <> src) as H_caller_neq_src; [lia|].
        assert (addr STATE0 = src) as HstateCallerEq; [lia|].
        assert (i = Caller ENV0') as HiCallerEq; [lia|].
        destruct H_conds.
        rewrite <- HstateCallerEq in *.
        rewrite <- HiCallerEq in *.
        apply Hyp in Hi_neq as Hyp'.
        apply H_iff3 in H_caller_neq_src as Hamt_prec.
        assert (amount = 0). lia.
        simpl.
        split; lia.
        -- (* true, false*)
        apply Z.eqb_eq in Hif_cond1 as Hif_cond1'; rewrite <- Hif_cond1'; auto.
      * destruct (addr STATE0 =? src) eqn:Hif_cond1, (i =? Caller ENV0')%bool eqn:Hif_cond2; auto.
        -- (* true, true *)
        assert (Caller ENV0' <> src) as H_caller_neq_src; [lia|].
        assert (addr STATE0 = src) as HstateCallerEq; [lia|].
        assert (i = Caller ENV0') as HiCallerEq; [lia|].
        destruct H_conds.
        rewrite <- HstateCallerEq in *.
        rewrite <- HiCallerEq in *.
        apply Hyp in Hi_neq as Hyp'.
        apply H_iff3 in H_caller_neq_src as Hamt_prec.
        assert (amount = 0). lia.
        simpl.
        split; lia.
        -- (* true, false*)
        apply Z.eqb_eq in Hif_cond1 as Hif_cond1'; rewrite <- Hif_cond1'; auto.
    + (* approve *)
      destruct H0; simpl.
      * assert (Caller ENV0' =? addr STATE0 = false). {
          rewrite Z.eqb_neq.
          destruct H_conds, H_stateConsistent.
          apply H_no_self_call.
          constructor. }
        rewrite Z.eqb_sym in H0; rewrite H0.
        apply Hyp; auto.
      * apply Hyp; auto.
    + destruct H0; simpl; auto.
    + destruct H0; simpl; auto.
      * destruct (addr STATE0 =? src) eqn:Hif_cond1, (i =? Caller ENV0')%bool eqn:Hif_cond2; auto.
        -- (* true, true *)
        assert (Caller ENV0' <> src) as H_caller_neq_src; [lia|].
        assert (addr STATE0 = src) as HstateCallerEq; [lia|].
        assert (i = Caller ENV0') as HiCallerEq; [lia|].
        destruct H_conds.
        rewrite <- HstateCallerEq in *.
        rewrite <- HiCallerEq in *.
        apply Hyp in Hi_neq as Hyp'.
        apply H_iff3 in H_caller_neq_src as Hamt_prec.
        assert (amount = 0). lia.
        simpl.
        split; lia.
        -- (* true, false*)
        apply Z.eqb_eq in Hif_cond1 as Hif_cond1'; rewrite <- Hif_cond1'; auto.
    + (* mint *)
      destruct H0; simpl; auto.
    + destruct H0; simpl; auto.
    + destruct H0; simpl; auto.
    + destruct H0; simpl; auto.
  - destruct HTokenTransition; destruct H0; rewrite <- Haddr_const in *; rewrite <- Htk0_const.
    + destruct H0; simpl; auto.
    + (* transferFrom *)
      destruct H0; simpl; auto.
      * destruct (addr STATE0 =? src) eqn:Hif_cond1, (i =? Caller ENV0')%bool eqn:Hif_cond2; auto.
        -- (* true, true *)
        assert (Caller ENV0' <> src) as H_caller_neq_src; [lia|].
        assert (addr STATE0 = src) as HstateCallerEq; [lia|].
        assert (i = Caller ENV0') as HiCallerEq; [lia|].
        destruct H_conds.
        rewrite <- HstateCallerEq in *.
        rewrite <- HiCallerEq in *.
        apply Hyp in Hi_neq as Hyp'.
        apply H_iff3 in H_caller_neq_src as Hamt_prec.
        assert (amount = 0). lia.
        simpl.
        split; lia.
        -- (* true, false*)
        apply Z.eqb_eq in Hif_cond1 as Hif_cond1'; rewrite <- Hif_cond1'; auto.
      * destruct (addr STATE0 =? src) eqn:Hif_cond1, (i =? Caller ENV0')%bool eqn:Hif_cond2; auto.
        -- (* true, true *)
        assert (Caller ENV0' <> src) as H_caller_neq_src; [lia|].
        assert (addr STATE0 = src) as HstateCallerEq; [lia|].
        assert (i = Caller ENV0') as HiCallerEq; [lia|].
        destruct H_conds.
        rewrite <- HstateCallerEq in *.
        rewrite <- HiCallerEq in *.
        apply Hyp in Hi_neq as Hyp'.
        apply H_iff3 in H_caller_neq_src as Hamt_prec.
        assert (amount = 0). lia.
        simpl.
        split; lia.
        -- (* true, false*)
        apply Z.eqb_eq in Hif_cond1 as Hif_cond1'; rewrite <- Hif_cond1'; auto.
    + (* approve *)
      destruct H0; simpl.
      * assert (Caller ENV0' =? addr STATE0 = false). {
          rewrite Z.eqb_neq.
          destruct H_conds, H_stateConsistent.
          apply H_no_self_call.
          constructor. }
        rewrite Z.eqb_sym in H0; rewrite H0.
        apply Hyp; auto.
      * apply Hyp; auto.
    + destruct H0; simpl; auto.
    + destruct H0; simpl; auto.
      * destruct (addr STATE0 =? src) eqn:Hif_cond1, (i =? Caller ENV0')%bool eqn:Hif_cond2; auto.
        -- (* true, true *)
        assert (Caller ENV0' <> src) as H_caller_neq_src; [lia|].
        assert (addr STATE0 = src) as HstateCallerEq; [lia|].
        assert (i = Caller ENV0') as HiCallerEq; [lia|].
        destruct H_conds.
        rewrite <- HstateCallerEq in *.
        rewrite <- HiCallerEq in *.
        apply Hyp in Hi_neq as Hyp'.
        apply H_iff3 in H_caller_neq_src as Hamt_prec.
        assert (amount = 0). lia.
        simpl.
        split; lia.
        -- (* true, false*)
        apply Z.eqb_eq in Hif_cond1 as Hif_cond1'; rewrite <- Hif_cond1'; auto.
    + destruct H0; simpl; auto.
    + destruct H0; simpl; auto.
    + destruct H0; simpl; auto.
    + destruct H0; simpl; auto.
Qed.


Definition Amm_balance_ge_reserve_0_AssistedProp (ENV: Env) (T0 T1 : Token.State) (L : Z) (NextAddr : address) (STATE : State) : Prop :=
  Amm_allowance_zero_Prop ENV T0 T1 L NextAddr STATE /\
  Amm_balance_ge_reserve_0_Prop ENV T0 T1 L NextAddr STATE.

Lemma Amm_balance_ge_reserve_0_init : invariantInit Amm_balance_ge_reserve_0_AssistedProp.
Proof.
  intros ENV t0 t1 L NextAddr STATE NextAddr' Hconstr.
  unfold Amm_balance_ge_reserve_0_AssistedProp, Amm_balance_ge_reserve_0_Prop.
  split. assert (invariantInit Amm_allowance_zero_Prop); eapply Amm_allowance_zero_init; eassumption.
  destruct Hconstr, H_conds, H_envNextAddrConsistent; simpl.
  reflexivity.
Qed.

Lemma Amm_balance_ge_reserve_0_step : invariantStep Amm_balance_ge_reserve_0_AssistedProp.
Proof.
  intros ENV0 t0 t1 L NextAddr0 STATE STATE' H_conds0 Hstep [Hyp1 Hyp2].
  unfold Amm_balance_ge_reserve_0_AssistedProp, Amm_balance_ge_reserve_0_Prop.
  split. assert (invariantStep Amm_allowance_zero_Prop); eapply Amm_allowance_zero_step; eassumption.
  simpl.
  destruct Hstep as [ENV [NextAddr [NextAddr' Htransition]]].
  destruct Htransition
    as [ HAmmStep
       | HstateConsistent HTokenTransition Haddr_const _ _ _ Hres0_const _ Htk1_const
       | HstateConsistent HTokenTransition Haddr_const _ _ _ Hres0_const _ Htk0_const ].
  - destruct HAmmStep; auto; try now (destruct H; simpl; auto).
    + (* swap1 *)
      destruct H; destruct H_conds, H_stateConsistent; simpl; rewrite_eqbs. rewrite Z.eqb_refl. reflexivity. reflexivity.
    + (* burn *)
      destruct H; destruct H_conds, H_stateConsistent; simpl; rewrite_eqbs. rewrite Z.eqb_refl. reflexivity. reflexivity.
  - assert (addr STATE <> Caller ENV) as H_addrState_neq_caller;
      [apply Z.neq_sym; destruct HstateConsistent; apply H_no_self_call; constructor|].
    rewrite <- Haddr_const, <- Hres0_const.
    destruct HTokenTransition as [HTokenTransition]; destruct HTokenTransition; try now (destruct H0; simpl; auto).
    + (* transfer *)
      destruct H0; simpl; auto.
      * rewrite_eqbs.
        destruct (addr STATE =? to) eqn:Hifcond0; simpl; auto.
        -- eapply Z.le_trans. apply Hyp2. apply Z.eqb_eq in Hifcond0; rewrite Hifcond0. destruct H_conds; lia.

    +  (* transferFrom *)
      destruct H0; simpl; auto.
      * destruct (addr STATE =? src) eqn:Hifcond0, (addr STATE =? dst) eqn:Hifcond1.
        -- assert (amount = 0); lia.
        -- assert (amount = 0); lia.
        -- eapply Z.le_trans. apply Hyp2. rewrite_b_right Hifcond1. destruct H_conds; lia.

        -- apply Hyp2.
      * destruct (addr STATE =? src) eqn:Hifcond0, (addr STATE =? dst) eqn:Hifcond1.
        -- assert (amount = 0); lia.
        -- destruct H_conds.

          rewrite_b_right Hif_cond0.
          assert (amount = 0). {
            assert (Token.allowance (token0 STATE) (addr STATE) (Caller ENV) = 0). {
              apply Hyp1. auto.
            }
            rewrite H0 in H_iff3. lia.
          }

          rewrite H0. unfold Amm_balance_ge_reserve_0_Prop in *. rewrite Hyp2; lia.
        -- eapply Z.le_trans. apply Hyp2. rewrite_b_right Hifcond1. destruct H_conds; lia.

        -- apply Hyp2.
      * destruct (addr STATE =? src) eqn:Hifcond0, (addr STATE =? dst) eqn:Hifcond1.
        -- assert (amount = 0); lia.
        -- destruct H_conds.

          rewrite_b_right Hif_cond0.
          assert (amount = 0). {
            assert (Token.allowance (token0 STATE) (addr STATE) (Caller ENV) = 0); [apply Hyp1; auto|].
            rewrite H0 in H_iff3. lia.
          }

          rewrite H0. unfold Amm_balance_ge_reserve_0_Prop in *. rewrite Hyp2; lia.
        -- eapply Z.le_trans. apply Hyp2. apply Z.eqb_eq in Hifcond1; rewrite Hifcond1. destruct H_conds; lia.

        -- apply Hyp2.
    +  (* burn *)
      destruct H0; simpl; auto.
      * rewrite_eqbs. auto.
    +  (* burnFrom *)
      destruct H0; simpl; auto.
      * destruct (addr STATE =? src) eqn:Hifcond.
        -- assert (amount = 0). { destruct H_conds.
            bool_to_prop. rewrite <- Hifcond in H_iff3. unfold Amm_allowance_zero_Prop in Hyp1. specialize Hyp1 with (i := Caller ENV) as Hyp2'. lia. }
            rewrite H0. rewrite_b_right Hifcond. unfold Amm_balance_ge_reserve_0_Prop in Hyp2. lia.
        -- destruct H; simpl; auto.
      * destruct (addr STATE =? src) eqn:Hifcond.
        -- assert (amount = 0). { destruct H_conds.
            bool_to_prop. rewrite <- Hifcond in H_iff3. unfold Amm_allowance_zero_Prop in Hyp1. specialize Hyp1 with (i := Caller ENV) as Hyp2'. lia. }
            rewrite H0. rewrite_b_right Hifcond. unfold Amm_balance_ge_reserve_0_Prop in Hyp2. lia.
        -- destruct H; simpl; auto.
      * destruct (addr STATE =? src) eqn:Hifcond.
        -- assert (amount = 0); lia.
        -- destruct H; simpl; auto.
    +  (* mint *)
      destruct H0; simpl; auto.
      * rewrite_eqbs.
        destruct (addr STATE =? dst) eqn:Hifcond0; simpl; auto.
        -- eapply Z.le_trans. apply Hyp2. apply Z.eqb_eq in Hifcond0; rewrite Hifcond0. destruct H_conds; lia.

  - destruct HTokenTransition;

    simpl; rewrite <- Haddr_const, <- Hres0_const, <- Htk0_const; assumption.
Qed.


Definition Amm_balance_ge_reserve_1_AssistedProp (ENV: Env) (T0 T1 : Token.State) (L : Z) (NextAddr : address) (STATE : State) : Prop :=
  Amm_allowance_zero_Prop ENV T0 T1 L NextAddr STATE /\
  Amm_balance_ge_reserve_1_Prop ENV T0 T1 L NextAddr STATE.

Lemma Amm_balance_ge_reserve_1_init : invariantInit Amm_balance_ge_reserve_1_AssistedProp.
Proof.
  intros ENV t0 t1 L NextAddr0 STATE NextAddr0' Hconstr.
  unfold Amm_balance_ge_reserve_1_AssistedProp, Amm_balance_ge_reserve_1_Prop.
  split. assert (invariantInit Amm_allowance_zero_Prop); eapply Amm_allowance_zero_init; eassumption.
  destruct Hconstr, H_conds, H_envNextAddrConsistent; simpl.
  reflexivity.
Qed.

Lemma Amm_balance_ge_reserve_1_step : invariantStep Amm_balance_ge_reserve_1_AssistedProp.
Proof.
  intros ENV0 t0 t1 L NextAddr0 STATE STATE' H_conds0 Hstep [Hyp1 Hyp2].
  unfold Amm_balance_ge_reserve_1_AssistedProp, Amm_balance_ge_reserve_1_Prop.
  split. assert (invariantStep Amm_allowance_zero_Prop); eapply Amm_allowance_zero_step; eassumption.
  simpl.
  destruct Hstep as [ENV [NextAddr [NextAddr' Htransition]]].
  destruct Htransition
    as [ HAmmStep
       | HstateConsistent HTokenTransition Haddr_const _ _ _ _ Hres1_const Htk1_const
       | HstateConsistent HTokenTransition Haddr_const _ _ _ _ Hres1_const Htk0_const ].
  - destruct HAmmStep; auto; try now (destruct H; simpl; auto).
    + (* swap0 *)
      destruct H; destruct H_conds, H_stateConsistent; simpl; rewrite_eqbs. rewrite Z.eqb_refl. reflexivity. reflexivity.
    + (* burn *)
      destruct H; destruct H_conds, H_stateConsistent; simpl; rewrite_eqbs. rewrite Z.eqb_refl. reflexivity. reflexivity.
  - destruct HTokenTransition;

    simpl; rewrite <- Haddr_const, <- Hres1_const, <- Htk1_const; assumption.
  - assert (addr STATE <> Caller ENV) as H_addrState_neq_caller;
      [apply Z.neq_sym; destruct HstateConsistent; apply H_no_self_call; constructor|].
    rewrite <- Haddr_const, <- Hres1_const.
    destruct HTokenTransition as [HTokenTransition]; destruct HTokenTransition; try now (destruct H0; simpl; auto).
    + (* transfer *)
      destruct H0; simpl; auto.
      * rewrite_eqbs.
        destruct (addr STATE =? to) eqn:Hifcond0; simpl; auto.
        -- eapply Z.le_trans. apply Hyp2. apply Z.eqb_eq in Hifcond0; rewrite Hifcond0. destruct H_conds; lia.

    +  (* transferFrom *)
      destruct H0; simpl; auto.
      * destruct (addr STATE =? src) eqn:Hifcond0, (addr STATE =? dst) eqn:Hifcond1.
        -- assert (amount = 0); lia.
        -- assert (amount = 0); lia.
        -- eapply Z.le_trans. apply Hyp2. rewrite_b_right Hifcond1. destruct H_conds; lia.

        -- apply Hyp2.
      * destruct (addr STATE =? src) eqn:Hifcond0, (addr STATE =? dst) eqn:Hifcond1.
        -- assert (amount = 0); lia.
        -- destruct H_conds.

          rewrite_b_right Hif_cond0.
          assert (amount = 0). {
            assert (Token.allowance (token1 STATE) (addr STATE) (Caller ENV) = 0); [apply Hyp1; auto|].
            rewrite H0 in H_iff3. lia.
          }

          rewrite H0. unfold Amm_balance_ge_reserve_1_Prop in *. rewrite Hyp2; lia.
        -- eapply Z.le_trans. apply Hyp2. rewrite_b_right Hifcond1. destruct H_conds; lia.

        -- apply Hyp2.
      * destruct (addr STATE =? src) eqn:Hifcond0, (addr STATE =? dst) eqn:Hifcond1.
        -- assert (amount = 0); lia.
        -- destruct H_conds.

          rewrite_b_right Hif_cond0.
          assert (amount = 0). {
            assert (Token.allowance (token1 STATE) (addr STATE) (Caller ENV) = 0); [apply Hyp1; auto|].
            rewrite H0 in H_iff3. lia.
          }

          rewrite H0. unfold Amm_balance_ge_reserve_1_Prop in *. rewrite Hyp2; lia.
        -- eapply Z.le_trans. apply Hyp2. apply Z.eqb_eq in Hifcond1; rewrite Hifcond1. destruct H_conds; lia.

        -- apply Hyp2.
    + (* burn *)
      destruct H0; simpl; auto.
      * rewrite_eqbs. apply Hyp2.
    + (* burnFrom *)
      destruct H0; simpl; auto.
      * destruct (addr STATE =? src) eqn:Hifcond.
        -- assert (amount = 0). { destruct H_conds.
            bool_to_prop. rewrite <- Hifcond in H_iff3. unfold Amm_allowance_zero_Prop in Hyp1. specialize Hyp1 with (i := Caller ENV) as Hyp2'. lia. }
            rewrite H0. rewrite_b_right Hifcond. unfold Amm_balance_ge_reserve_1_Prop in Hyp2. lia.
        -- apply Hyp2.
      * destruct (addr STATE =? src) eqn:Hifcond.
        -- assert (amount = 0). { destruct H_conds.
            bool_to_prop. rewrite <- Hifcond in H_iff3. unfold Amm_allowance_zero_Prop in Hyp1. specialize Hyp1 with (i := Caller ENV) as Hyp2'. lia. }
            rewrite H0. rewrite_b_right Hifcond. unfold Amm_balance_ge_reserve_1_Prop in Hyp2. lia.
        -- apply Hyp2.
      * destruct (addr STATE =? src) eqn:Hifcond.
        -- assert (amount = 0); lia.
        -- apply Hyp2.
    + (* mint *)
      destruct H0; simpl; auto.
      * destruct (addr STATE =? dst) eqn:Hifcond.
        -- eapply Z.le_trans. apply Hyp2. rewrite_b_right Hifcond1. destruct H_conds; lia.

        -- apply Hyp2.
Qed.




Fixpoint balanceOf_sum' (balanceOf : address -> Z) (n : nat) (acc : Z) : Z :=
    match n with
    | O => balanceOf 0 + acc
    | S n => balanceOf_sum' balanceOf n (acc + balanceOf (Z.of_nat (S n)))
    end.

Definition balanceOf_sum (STATE : State) :=
  balanceOf_sum' (balanceOf STATE) (Z.to_nat MAX_ADDRESS) 0.


Definition transfer_from map (from : address) (amt : Z) :=
  fun b => if b =? from then map from - amt else map b.

Definition transfer_to map (from : address) (amt : Z) :=
  fun b => if b =? from then map from + amt else map b.

Definition transfer map from to amt := transfer_to (transfer_from map from amt) to amt.

Definition transfer' map from to amt := transfer_from (transfer_to map to amt) from amt.

Lemma balanceOf_sum_f_eq f f' addr acc :
  (forall x, x <= Z.of_nat addr -> f x = f' x) ->
  balanceOf_sum' f addr acc = balanceOf_sum' f' addr acc.
Proof.
  revert acc. induction addr; intros acc Hyp.
  - simpl. rewrite Hyp. reflexivity. lia.
  - simpl. rewrite IHaddr. rewrite Hyp. reflexivity.
    lia. intros. eapply Hyp. lia.
Qed.

Lemma balanceOf_sum_acc f  addr acc z :
  balanceOf_sum' f addr (acc + z) = balanceOf_sum' f addr acc + z.
Proof.
  revert z acc. induction addr; intros z acc.
  - simpl. lia.
  - simpl. rewrite !IHaddr. lia.
Qed.

Opaque Z.sub Z.add Z.of_nat.

Lemma balanceOf_sum_thm x f f' addr acc :
  (forall y, x <> y -> f y = f' y) ->
  0 <= x ->
  balanceOf_sum' f addr acc =
  if (Z.to_nat x <=? addr)%nat then balanceOf_sum' f' addr acc - f' x + f x else balanceOf_sum' f' addr acc.
Proof.
  revert acc. induction addr; intros acc Hyp Hleq1.
  - simpl. destruct (0 =? x) eqn:Heq.
    + eapply Z.eqb_eq in Heq. subst.
      simpl. lia.
    + eapply Z.eqb_neq in Heq.
      assert (Hbeq : (Z.to_nat x <=? 0)%nat = false).
      { eapply leb_correct_conv. lia. }
      rewrite Hbeq. rewrite Hyp. reflexivity. eauto.

  - destruct (Z.to_nat x <=? S addr0)%nat eqn:Hleq.
    + eapply Nat.leb_le in Hleq.
      destruct (Z.of_nat (S addr0) =? x) eqn:Heqb.
      * eapply Z.eqb_eq in Heqb. simpl. rewrite Heqb.
        erewrite balanceOf_sum_f_eq with (f' := f').
        rewrite !balanceOf_sum_acc. lia.

        intros. eapply Hyp. lia.

      * simpl.
        destruct ((Z.to_nat x <=? addr0)%nat) eqn:Hleq'.
        -- rewrite IHaddr; eauto. rewrite Hyp. reflexivity.
           intros Heq; subst. lia.
        -- eapply Z.eqb_neq in Heqb.
           eapply Nat.leb_gt in Hleq'. lia.

    + simpl. eapply leb_complete_conv in Hleq.
      erewrite balanceOf_sum_f_eq with (f' := f').
      rewrite Hyp. reflexivity.
      * intros Heq; subst. lia.
      * intros. rewrite Hyp. reflexivity.
        intros Heq; subst. lia.
Qed.

Lemma balanceOf_sum_thm' x f f' acc :
  (forall y, x <> y -> f y = f' y) ->
  0 <= x <= MAX_ADDRESS->
  balanceOf_sum' f (Z.to_nat MAX_ADDRESS) acc = balanceOf_sum' f' (Z.to_nat MAX_ADDRESS) acc - f' x + f x.
Proof.
  intros H_f [H_x_0 H_x_max].
  rewrite balanceOf_sum_thm with (x := x) (f' := f').
  - apply Z2Nat.inj_le in H_x_max; try lia.
    rewrite <- Nat.leb_le in H_x_max.
    rewrite H_x_max.
    reflexivity.
  - assumption.
  - assumption.
Qed.

Lemma balanceOf_sum_transfer_thm x1 x2 f f' acc :
  (forall y, x1 <> y -> x2 <> y -> f y = f' y) ->
  f x1 + f x2 = f' x1 + f' x2 ->
  0 <= x1 <= MAX_ADDRESS ->
  0 <= x2 <= MAX_ADDRESS ->
  balanceOf_sum' f (Z.to_nat MAX_ADDRESS) acc = balanceOf_sum' f' (Z.to_nat MAX_ADDRESS) acc.
Proof.
  intros H_f1 H_f2 [H_x1_0 H_x1_max] [H_x2_0 H_x2_max].
  rewrite balanceOf_sum_thm with (x := x1) (f' := fun _b => if _b =? x1 then f' _b else f _b).
  - apply Z2Nat.inj_le in H_x1_max; try lia.
    rewrite <- Nat.leb_le in H_x1_max.
    rewrite H_x1_max, Z.eqb_refl.
    rewrite balanceOf_sum_thm with (x := x2) (f' := f').
    + apply Z2Nat.inj_le in H_x2_max; try lia.
      rewrite <- Nat.leb_le in H_x2_max.
      rewrite H_x2_max.
      destruct (x2 =? x1) eqn:Hx2x1.
      * apply Z.eqb_eq in Hx2x1. subst. lia.
      * lia.
    + intros. destruct (y =? x1) eqn:Hyx1.
      * lia.
      * apply H_f1; [lia | assumption].
    + lia.
  - intros. destruct (y =? x1) eqn:Hyx1.
    * apply H_f1; [assumption | lia].
    * reflexivity.
  - lia.
Qed.


Theorem initialSupply': forall ENV _totalSupply t0 t1 NextAddr State NextAddr' (n : nat),
    0 <= Caller ENV ->
    Caller ENV < NextAddr ->
    constructor ENV t0 t1 _totalSupply NextAddr State NextAddr' ->
    balanceOf_sum' (balanceOf (State)) n 0 =
    if (Z.of_nat n <? (Caller ENV)) then 0 else
    if (Z.of_nat n <? (NextAddr)) then totalSupply State - 1000 else
    totalSupply State.
Proof.
  intros ENV ? ? ? ? ? ? ? _ _ Hcnstr.
  destruct Hcnstr as [? H_conds _ ? _]; simpl.

  assert (forall n : nat, Z.of_nat n < Caller ENV ->
      balanceOf_sum' (fun _binding_0 : address => if _binding_0 =? NextAddr then 1000 else if _binding_0 =? Caller ENV then _totalSupply - 1000 else 0) n 0 = 0) as H0.
  { intros. induction n0.
    - simpl. destruct H_conds, H_envNextAddrConsistent. destruct (Caller ENV), (NextAddr); lia; discriminate.
    - simpl. rewrite -> balanceOf_sum_acc. destruct H_conds, H_envNextAddrConsistent.
      destruct (Z.of_nat (S n0) =? Caller ENV) eqn:Heq.
      + apply Z.eqb_eq in Heq. apply Z.lt_neq in H. contradiction.
      + rewrite IHn0.
        * destruct (Z.of_nat (S n0) =? NextAddr) eqn:Heq'; try lia.
          -- apply Z.eqb_eq in Heq'. lia.
        * lia.
  }

  induction n.
  - destruct H_conds, H_envNextAddrConsistent; simpl.
    assert (forall p, Z.of_nat 0 <? Z.pos p = true) as Hmy; [auto|].
    destruct (Caller ENV) eqn:Hcaller, (NextAddr) eqn:Hthis; try lia.
    + rewrite Z.ltb_irrefl; rewrite Hmy; lia.
    + rewrite Hmy; lia.
  - simpl. rewrite balanceOf_sum_acc.
    destruct (Z.of_nat (S n) <? Caller ENV) eqn:Hlt.
    + destruct (Z.of_nat (S n) =? Caller ENV) eqn:Heq. * lia.
      * rewrite H0.
        -- destruct (Z.of_nat (S n) =? NextAddr) eqn:Heq'; try lia.
          ++ destruct H_conds, H_envNextAddrConsistent. apply Z.eqb_eq in Heq'. apply Z.ltb_lt in Hlt. lia.
        -- apply Z.ltb_lt in Hlt. lia.
    + destruct (Z.of_nat (S n) =? Caller ENV) eqn:Heq.
      * rewrite H0.
        -- destruct (Z.of_nat (S n) =? NextAddr) eqn:Heq'; try lia.
          ++ destruct H_conds, H_envNextAddrConsistent. rewrite_b_left Heq'. lia.
          ++ destruct (Z.of_nat (S n) <? NextAddr) eqn:Hlt'; try lia.

            apply Z.ltb_ge in Hlt'.
            apply Z.eqb_eq in Heq. rewrite Heq in *. destruct H_conds, H_envNextAddrConsistent. lia.
        -- apply Z.eqb_eq in Heq. rewrite <- Heq. lia.
      * rewrite IHn.
        assert ( Z.of_nat n <? Caller ENV = false).
        { apply Z.ltb_ge in Hlt. apply Z.eqb_neq in Heq. lia. }
        rewrite H.
        destruct (Z.of_nat n <? NextAddr) eqn:Hlt', (Z.of_nat (S n) =? NextAddr) eqn:Heq'.
        -- assert (Z.of_nat (S n) <? NextAddr = false). lia.
        rewrite H1. lia.
        -- assert (Z.of_nat (S n) < NextAddr) as Hlt''. bool_to_prop. lia.
          prop_to_bool. rewrite Hlt''. lia.
        -- bool_to_prop. lia.
        -- assert (Z.of_nat (S n) <? NextAddr = false); [apply Z.ltb_ge; lia|].
           rewrite H1. lia.
Qed.

Theorem initialSupply: forall ENV t0 t1 _totalSupply NextAddr STATE NextAddr',
    0 <= Caller ENV <= MAX_ADDRESS ->
    constructor ENV t0 t1 _totalSupply NextAddr STATE NextAddr' ->
    balanceOf_sum STATE =
    totalSupply STATE.
Proof.
  intros.
  unfold balanceOf_sum.
  (*destruct H0 as [? H_conds _ _].*)
  erewrite -> initialSupply'; try (now eassumption); destruct H0 as [? H_conds _ ?].
  - rewrite Z2Nat.id.
    + destruct (MAX_ADDRESS <? Caller ENV) eqn:Hineq.
      * apply Z.ltb_lt in Hineq. lia.
      * destruct (MAX_ADDRESS <? NextAddr) eqn:Hineq'.
        -- apply Z.ltb_lt in Hineq'.
           destruct H_conds, H_envNextAddrConsistent ; unfold MAX_ADDRESS in *; lia.
        -- reflexivity.
    + unfold MAX_ADDRESS. unfold UINT_MAX. lia.
  - destruct H_conds; lia.
  - destruct H_conds, H_envNextAddrConsistent; lia.
Qed.

Theorem deltas: forall x1 x2 y1 y2,
  x1 = y1 -> x1 - x2 = y1 - y2 -> x2 = y2.
Proof.
  intros. lia.
Qed.


Definition Amm_liqs_sum_eq_total_Prop (ENV : Env) (T0 T1 : Token.State) (L : Z) (NextAddr : address) (STATE : State) : Prop :=
  balanceOf_sum STATE = totalSupply STATE.

Definition Amm_liqs_sum_eq_total_AssistedProp (ENV: Env) (T0 T1 : Token.State) (L : Z) (NextAddr : address) (STATE : State) : Prop :=
  Amm_allowance_zero_Prop ENV T0 T1 L NextAddr STATE /\
  Amm_balance_ge_reserve_0_AssistedProp ENV T0 T1 L NextAddr STATE /\
  Amm_balance_ge_reserve_1_AssistedProp ENV T0 T1 L NextAddr STATE /\
  Amm_liqs_sum_eq_total_Prop ENV T0 T1 L NextAddr STATE.

Lemma Amm_liqs_sum_eq_total_init : invariantInit Amm_liqs_sum_eq_total_AssistedProp.
Proof.
  intros ENV t0 t1 L NextAddr State NexrAddr' Hconstr.
  unfold Amm_liqs_sum_eq_total_AssistedProp, Amm_liqs_sum_eq_total_Prop.
  split. assert (invariantInit Amm_allowance_zero_Prop); eapply Amm_allowance_zero_init; eassumption.
  split. assert (invariantInit Amm_balance_ge_reserve_0_AssistedProp); eapply Amm_balance_ge_reserve_0_init; eassumption.
  split. assert (invariantInit Amm_balance_ge_reserve_1_AssistedProp); eapply Amm_balance_ge_reserve_1_init; eassumption.
  eapply initialSupply; [| eassumption].
  destruct Hconstr as [? H_conds ? ?], H_conds, H_envNextAddrConsistent; assumption.
Qed.

Lemma Amm_liqs_sum_eq_total_step : invariantStep Amm_liqs_sum_eq_total_AssistedProp.
Proof.
  intros ENV0 T0 T1 L NextAddr0 STATE STATE' HinitPrecs Hstep [Hyp1 [Hyp2 [Hyp3 Hyp4]]].
  unfold Amm_liqs_sum_eq_total_AssistedProp, Amm_liqs_sum_eq_total_Prop in *.
  split. assert (invariantStep Amm_allowance_zero_Prop); eapply Amm_allowance_zero_step; eassumption.
  split. assert (invariantStep Amm_balance_ge_reserve_0_AssistedProp); eapply Amm_balance_ge_reserve_0_step; eassumption.
  split. assert (invariantStep Amm_balance_ge_reserve_1_AssistedProp); eapply Amm_balance_ge_reserve_1_step; eassumption.
  destruct Hstep as [ENV [NextAddr [NexteAddr' Htransition]]].
  destruct Htransition
    as [ HAmmStep
       | HstateConsistent HTokenExtStep Haddr_const _ _ Hbalance_const _ _ Htk1_const
       | HstateConsistent HTokenExtStep Haddr_const _ _ Hbalance_const _ _ Htk0_const ].
  - destruct HAmmStep; simpl.
    + (* swap0 *)
      destruct H; simpl; auto.
    + (* swap1 *)
      destruct H; simpl; auto.
    + (* mint *)
      apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [assumption|].
      unfold balanceOf_sum. simpl.
      rewrite balanceOf_sum_thm' with (x := to) (f' := balanceOf STATE').
      * destruct H; simpl; rewrite Z.eqb_refl; lia.
      * destruct H; simpl; intros; rewrite_eqbs; reflexivity.
      * destruct H; simpl; unfold MAX_ADDRESS; destruct H_conds; lia.
    + (* burn *)
      apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [assumption|].
      unfold balanceOf_sum. simpl.
      rewrite balanceOf_sum_thm' with (x := Caller ENV) (f' := balanceOf STATE').
      * destruct H; simpl; rewrite Z.eqb_refl; lia.
      * destruct H; simpl; intros; rewrite_eqbs; reflexivity.
      * destruct H; simpl; unfold MAX_ADDRESS; destruct H_conds, H_envNextAddrConsistent; lia.
    + (* transfer *)
      apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [assumption|].
      unfold balanceOf_sum. simpl.
      rewrite balanceOf_sum_transfer_thm with (x1 := Caller ENV) (x2 := to) (f' := balanceOf STATE').
      * destruct H; simpl; lia.
      * destruct H; simpl; intros; rewrite_eqbs; reflexivity.
      * destruct H; simpl; rewrite_eqbs; repeat rewrite Z.eqb_refl; lia.
      * destruct H; simpl; unfold MAX_ADDRESS; destruct H_conds, H_envNextAddrConsistent; lia.
      * destruct H; simpl; unfold MAX_ADDRESS; destruct H_conds; lia.
    + (* transferFrom *)
      apply deltas with (x1 := balanceOf_sum STATE) (y1 := totalSupply STATE); [assumption|].
      unfold balanceOf_sum. simpl.
      rewrite balanceOf_sum_transfer_thm with (x1 := src) (x2 := dst) (f' := balanceOf STATE').
      * destruct H; simpl; lia.
      * destruct H; simpl; intros; rewrite_eqbs; reflexivity.
      * destruct H; simpl; destructAnds; rewrite_eqbs; repeat rewrite Z.eqb_refl; lia.
      * destruct H; simpl; unfold MAX_ADDRESS; destruct H_conds; lia.
      * destruct H; simpl; unfold MAX_ADDRESS; destruct H_conds; lia.
    + (* approve *)
      destruct H; simpl; auto.
    + (* totalSupply *)
      destruct H; simpl; auto.
    + (* balanceOf *)
      destruct H; simpl; auto.
    + (* allowance *)
      destruct H; simpl; auto.
  - destruct HTokenExtStep. unfold balanceOf_sum. rewrite <- H, <- Hbalance_const. assumption.
  - destruct HTokenExtStep. unfold balanceOf_sum. rewrite <- H, <- Hbalance_const. assumption.
Qed.

Lemma Amm_liqs_sum_eq_total_reach :

  forall (ENV : Env) (t0 : Token.State) (t1 : Token.State) (liquidity : Z) (NextAddr : address) (STATE : State),
     reachableFromInit ENV t0 t1 liquidity NextAddr STATE
  -> Amm_liqs_sum_eq_total_AssistedProp ENV t0 t1 liquidity NextAddr STATE
.
Proof.
  intros.
  apply invariantReachable.
  exact Amm_liqs_sum_eq_total_init.
  exact Amm_liqs_sum_eq_total_step.
  assumption.
Qed.

Lemma sum_mono :
  forall f N M acc,
  (forall (x : nat), (x <= M)%nat -> 0 <= f (Z.of_nat x))
  -> (N <= M)%nat
  -> balanceOf_sum' f N acc <= balanceOf_sum' f M acc.
Proof.
  intros f N M acc Hfnneg Hnm.
  induction M.
  - destruct N.
    + reflexivity.
    + lia.
  - destruct (N ?= S M)%nat eqn:HnSm.
    + apply Nat.compare_eq in HnSm.
      subst. reflexivity.
    + simpl. rewrite balanceOf_sum_acc.
      rewrite <- Z.add_0_r at 1.
      apply Z.add_le_mono.
      * apply IHM; apply Nat.compare_lt_iff in HnSm.
        -- intros. apply Hfnneg. lia.
        -- lia.
      * apply Hfnneg. lia.
    + apply Nat.compare_gt_iff in HnSm.
      lia.
Qed.

Lemma sum_pos :
forall f n N,
   (forall m, (m <= Z.of_nat N)-> 0 <= f m)
-> (n <= N)%nat
-> 0 <= balanceOf_sum' f n 0.
Proof.
intros.
induction n.
- unfold balanceOf_sum'.
  rewrite Z.add_0_r.
  apply H with (m := 0). lia.
- simpl. rewrite balanceOf_sum_acc.
  apply Z.add_nonneg_nonneg.
  + apply IHn. lia.
  + apply H. lia.
Qed.

Lemma sum_le_total' :
forall f total n N,
balanceOf_sum' f N 0 = total
-> (n <= N)%nat
-> (forall x, x <= Z.of_nat N -> 0 <= f x)
-> (forall (m : nat), (m <= n)%nat -> f (Z.of_nat m) <= total).
Proof.
  intros f total n N HtotalBalance HnLeN Hfnneg m HmLen .
  assert (0 <= total) as HtotalNneg. {

    rewrite <- HtotalBalance. apply sum_pos with (N := N); [assumption | lia].
  }

  assert (forall x acc, f (Z.of_nat (S x)) = balanceOf_sum' f (S x) acc - balanceOf_sum' f x acc). {
    intros. simpl. rewrite balanceOf_sum_acc. lia.

  }
  assert (f 0 = balanceOf_sum' f 0 0). { simpl; lia. }

  destruct m.
  - rewrite <- HtotalBalance. rewrite Nat2Z.inj_0. rewrite H0.
    apply sum_mono.
    + intros. apply Hfnneg with (x := Z.of_nat x). lia.
    + lia.
  - rewrite H with (acc := 0).
    rewrite <- HtotalBalance.
    rewrite <- Z.sub_0_r with (n := balanceOf_sum' f N 0).
    apply Z.sub_le_mono.
    + apply sum_mono.
      * intros. apply Hfnneg with (x := Z.of_nat x). lia.
      * lia.
    + apply sum_pos with (N := N).
      * intros. apply Hfnneg. lia.
      * lia.
Qed.

Definition Amm_balance_nneg_Prop (ENV : Env) (T0 T1 : Token.State) (L : Z) (NextAddr : address) (STATE : State) : Prop :=
  forall x, 0 <= balanceOf STATE x.

Lemma Amm_balance_nneg_init : invariantInit Amm_balance_nneg_Prop.
Proof.
  unfold invariantInit, Amm_balance_nneg_Prop.
  intros.
  destruct H.
  simpl.
  destruct (x =? Caller ENV) eqn:Hcond1.
  - destruct (x =? NextAddr) eqn:Hcond2.
    + lia.
    + destruct H_conds; lia.
  - destruct (x =? NextAddr) eqn:Hcond2; lia.
Qed.

Lemma Amm_balance_nneg_step : invariantStep Amm_balance_nneg_Prop.
Proof.
  unfold invariantStep, Amm_balance_nneg_Prop.
  intros ENV0 t0 t1 liquidity NextAddr0 STATE STATE' H_conds0 Hstep Hyp x.
  destruct Hstep as [ENV [NextAddr [NextAddr' Htransition]]].
  destruct Htransition
    as [ HAmmStep
       | HstateConsistent HTokenTransition Haddr_const _ _ Hbalance_const _ _ Htk1_const
       | HstateConsistent HTokenTransition Haddr_const _ _ Hbalance_const _ _ Htk0_const].
  - destruct HAmmStep; simpl; auto;
    destruct H; simpl; destruct H_conds; destruct_ifs; try apply Hyp; try lia.
  - destruct HTokenTransition. rewrite <- Hbalance_const. apply Hyp.
  - destruct HTokenTransition. rewrite <- Hbalance_const. apply Hyp.
Qed.

Lemma Amm_balance_nneg_reach :

  forall (ENV : Env) (t0 : Token.State) (t1 : Token.State) (liquidity : Z) (NextAddr : address) (STATE : State),
     reachableFromInit ENV t0 t1 liquidity (NextAddr : address) (STATE : State)
  -> Amm_balance_nneg_Prop ENV t0 t1 liquidity NextAddr STATE
.
Proof.
  intros.
  apply invariantReachable.
  exact Amm_balance_nneg_init.
  exact Amm_balance_nneg_step.
  assumption.
Qed.

Definition Amm_reserve_nneg_Prop (ENV : Env) (T0 T1 : Token.State) (L : Z) (NextAddr : address) (STATE : State) : Prop :=
  0 <= reserve0 STATE /\ 0 <= reserve1 STATE.

Lemma Amm_reserve_nneg_init : invariantInit Amm_reserve_nneg_Prop.
Proof.
  unfold invariantInit, Amm_reserve_nneg_Prop.
  intros.
  destruct H; destruct H_conds.
  simpl.
  split; lia.
Qed.

Lemma Amm_reserve_nneg_step : invariantStep Amm_reserve_nneg_Prop.
Proof.
  unfold invariantStep, Amm_reserve_nneg_Prop.
  intros ENV0 t0 t1 liquidity NextAddr0 STATE STATE' HinitPrecs Hstep Hyp.
  destruct Hstep as [ENV [NextAddr [NextAddr' Htransition]]].
  destruct Htransition
    as [ HAmmStep
       | HstateConsistent HTokenTransition Haddr_const _ _ Hbalance_const Hres0_const Hres1_const Htk1_const
       | HstateConsistent HTokenTransition Haddr_const _ _ Hbalance_const Hres0_const Hres1_const Htk0_const].
  - destruct HAmmStep; simpl; auto;
    destruct H; destruct H_conds; simpl; lia.
  - destruct HTokenTransition. rewrite <- Hres0_const, <- Hres1_const. apply Hyp.
  - destruct HTokenTransition. rewrite <- Hres0_const, <- Hres1_const. apply Hyp.
Qed.

Lemma Amm_reserve_nneg_reach :

  forall (ENV : Env) (t0 : Token.State) (t1 : Token.State) (liquidity : Z) (NextAddr : address) (STATE : State),
     reachableFromInit ENV t0 t1 liquidity NextAddr (STATE : State)
  -> Amm_reserve_nneg_Prop ENV t0 t1 liquidity NextAddr STATE
.
Proof.
  intros.
  apply invariantReachable.
  exact Amm_reserve_nneg_init.
  exact Amm_reserve_nneg_step.
  assumption.
Qed.

Definition Amm_solvency_Prop (ENV : Env) (T0 T1 : Token.State) (L : Z) (STATE : State) : Prop :=
  forall x, 0 <= x <= MAX_ADDRESS ->
  0 < balanceOf STATE x ->
  balanceOf STATE x * reserve0 STATE / totalSupply STATE <= Token.balanceOf (token0 STATE) (addr STATE) /\
  balanceOf STATE x * reserve1 STATE / totalSupply STATE <= Token.balanceOf (token1 STATE) (addr STATE).

Lemma Amm_solvency_reach :
  forall (ENV : Env) (t0 : Token.State) (t1 : Token.State) (liquidity : Z) (NextAddr : address) (STATE : State),
     reachableFromInit ENV t0 t1 liquidity NextAddr STATE
     (*-> totalSupply STATE  > 0*)
  -> Amm_solvency_Prop ENV t0 t1 liquidity STATE
.
Proof.
  intros.
  assert (Amm_liqs_sum_eq_total_AssistedProp ENV t0 t1 liquidity NextAddr STATE) as HsumEq. {
    apply Amm_liqs_sum_eq_total_reach. assumption.
  }
  assert (Amm_balance_nneg_Prop ENV t0 t1 liquidity NextAddr STATE) as HbalNneg. {
    apply Amm_balance_nneg_reach. assumption.
  }
  assert (Amm_reserve_nneg_Prop ENV t0 t1 liquidity NextAddr STATE) as [Hres0Nneg Hres1Nneg]. {
    apply Amm_reserve_nneg_reach. assumption.
  }
  unfold Amm_solvency_Prop.
  unfold Amm_liqs_sum_eq_total_AssistedProp in HsumEq.
  intros.

  assert (forall p, 0 <= p <= MAX_ADDRESS -> balanceOf STATE p <= totalSupply STATE) as HbalLeTotal. {
    intros.
    unfold Amm_liqs_sum_eq_total_Prop in HsumEq.
    destruct HsumEq as [_ [_ [_ H']]].
    (*rewrite <- H'.*)
    remember (Z.to_nat p) as pn eqn:Heqpn.
    assert (p = Z.of_nat pn) as Heqp. { rewrite Heqpn. apply Z.eq_sym_iff. apply Z2Nat.id. lia. }
    rewrite Heqp.
    apply sum_le_total' with (f := balanceOf STATE) (total := totalSupply STATE) (n := pn) (N := Z.to_nat MAX_ADDRESS).
    - assumption.
    - lia.
    - intros. apply HbalNneg.
    - lia.
    }
  assert (0 < totalSupply STATE). {
    apply Z.lt_le_trans with (m := balanceOf STATE x).
    - assumption.
    - apply HbalLeTotal. assumption.
  }
  split.
  - apply Z.le_trans with (m := totalSupply STATE * reserve0 STATE / totalSupply  STATE).
    + apply Z.div_le_mono.
      * lia.
      * apply Z.mul_le_mono_nonneg_r.
        -- assumption.
        -- apply HbalLeTotal. lia.
    + rewrite Z.mul_comm, Z.div_mul. destruct HsumEq as [_ [H' [_ _]]].
      apply H'.
      lia.
  - apply Z.le_trans with (m := totalSupply STATE * reserve1 STATE / totalSupply  STATE).
    + apply Z.div_le_mono.
      * lia.
      * apply Z.mul_le_mono_nonneg_r.
        -- assumption.
        -- apply HbalLeTotal. lia.
    + rewrite Z.mul_comm, Z.div_mul. destruct HsumEq as [_ [_ [H' _]]].
      apply H'.
      lia.
Qed.
