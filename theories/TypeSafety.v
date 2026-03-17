(** * Type Safety
    Formalizes Section 6 of the tech report: type safety lemmas
    for all syntactic categories. *)

From Stdlib Require Import String ZArith List Bool Classical_Prop Lia.
From Act Require Import Maps Syntax Domains Semantics ValueTyping Typing.
Import ListNotations.

Tactic Notation "inv" hyp(H) := inversion H; subst; clear H.

(** Rewrite contract_env accessors through Σ_with_* wrappers *)
Ltac Σ_rw :=
  repeat first
    [ rewrite Σ_storage_with_storage
    | rewrite Σ_cnstr_with_storage
    | rewrite Σ_trans_with_storage
    | rewrite Σ_storage_with_cnstr
    | rewrite Σ_cnstr_with_cnstr
    | rewrite Σ_trans_with_cnstr
    | rewrite Σ_storage_with_trans
    | rewrite Σ_cnstr_with_trans
    | rewrite Σ_trans_with_trans ].

Ltac Σ_rw_in H :=
  repeat first
    [ rewrite Σ_storage_with_storage in H
    | rewrite Σ_cnstr_with_storage in H
    | rewrite Σ_trans_with_storage in H
    | rewrite Σ_storage_with_cnstr in H
    | rewrite Σ_cnstr_with_cnstr in H
    | rewrite Σ_trans_with_cnstr in H
    | rewrite Σ_storage_with_trans in H
    | rewrite Σ_cnstr_with_trans in H
    | rewrite Σ_trans_with_trans in H ].

Lemma int_binop_dec : forall (op1 op2 : int_binop), {op1 = op2} + {op1 <> op2}.
Proof. decide equality. Defined.

(** slot_type_wf / abi_type_wf are covariant in Σ *)
Lemma abi_type_wf_incl : forall Σ Σ' alpha,
  Σ_incl Σ Σ' -> abi_type_wf Σ alpha -> abi_type_wf Σ' alpha.
Proof.
  intros Σ Σ' alpha [Hst _] Hwf. destruct Hwf; constructor; auto.
  destruct H as [v Hv]. exists v. exact (Hst _ _ Hv).
Qed.

Lemma slot_type_wf_incl : forall Σ Σ' st,
  Σ_incl Σ Σ' -> slot_type_wf Σ st -> slot_type_wf Σ' st.
Proof.
  intros Σ Σ' st Hincl Hwf. destruct Hwf; constructor.
  - destruct H as [v Hv]. exists v. exact (proj1 Hincl _ _ Hv).
  - eapply abi_type_wf_incl; eauto.
Qed.

(* ================================================================= *)
(** ** Extending Σ Preserves Well-Typedness (Lemma 6.2 of tech report §6) *)

(** Helper: Σ_incl from Σ to Σ'' produced by type_contract *)
Lemma type_contract_Σ_incl : forall Σ c Σ',
  type_contract Σ c Σ' -> Σ_incl Σ Σ'.
Proof.
  intros Σ c Σ' Htc. inv Htc.
  eapply Σ_incl_trans. eapply Σ_incl_trans.
  - eapply Σ_incl_with_storage_fresh; eauto.
  - eapply Σ_incl_with_cnstr_fresh. Σ_rw. exact H0.
  - eapply Σ_incl_with_trans_fresh. Σ_rw. exact H1.
Qed.

(** Helper: well-typedness of intermediate contract_env *)
Lemma Σ_well_typed_intermediate :
  forall Σ a layout ctor,
    Σ_well_typed Σ ->
    ~ dom (Σ_storage Σ) a ->
    ~ dom (Σ_cnstr Σ) a ->
    type_constructor Σ a ctor layout ->
    Σ_well_typed (Σ_with_cnstr (Σ_with_storage Σ a layout) a ctor).
Proof.
  intros Σ a layout ctor Hwt Hfs Hfc Htctor.
  assert (Hincl_ext : Σ_incl Σ (Σ_with_cnstr (Σ_with_storage Σ a layout) a ctor)).
  { eapply Σ_incl_trans.
    eapply Σ_incl_with_storage_fresh; eauto.
    eapply Σ_incl_with_cnstr_fresh. Σ_rw. exact Hfc. }
  constructor.
  - (* S0: storage well-formedness *)
    intros a' layout' Hsto'. Σ_rw_in Hsto'.
    destruct (String.eqb_spec a a').
    + subst. rewrite update_eq in Hsto'. injection Hsto' as Heql.
      subst layout'.
      assert (Hlwf : Forall (fun p => slot_type_wf Σ (snd p)) layout)
        by (inv Htctor; assumption).
      eapply Forall_impl; [|exact Hlwf].
      intros p Hp. eapply slot_type_wf_incl; eauto.
    + rewrite update_neq in Hsto' by auto.
      inv Hwt.
      match goal with Hswf : forall a l, Σ_storage _ a = Some l -> _ |- _ =>
        eapply Forall_impl; [|exact (Hswf _ _ Hsto')]
      end.
      intros p Hp. eapply slot_type_wf_incl; eauto.
  - (* S1: constructors *)
    intros a' ctor' Hctor'. Σ_rw_in Hctor'.
    destruct (String.eqb_spec a a').
    + subst. rewrite update_eq in Hctor'. injection Hctor' as ->.
      exists Σ, layout. split; [|split; [|split; [|split; [|split]]]].
      * exact Hincl_ext.
      * unfold dom in Hfc. destruct (Σ_cnstr Σ a') eqn:E; [exfalso; apply Hfc; eauto|reflexivity].
      * rewrite Σ_cnstr_size_with_cnstr, Σ_cnstr_size_with_storage. lia.
      * exact Hwt.
      * exact Htctor.
      * Σ_rw. apply update_eq.
    + rewrite update_neq in Hctor' by auto.
      inv Hwt.
      match goal with Hcond : forall a c, Σ_cnstr _ a = Some c -> _ |- _ =>
        destruct (Hcond a' ctor' Hctor') as [Σ'' [layout' [Hincl [Hnone [Hlt [Hwt' [Htc' Hsto']]]]]]]
      end.
      exists Σ'', layout'. split; [|split; [|split; [|split; [|split]]]].
      * eapply Σ_incl_trans; [exact Hincl|]. exact Hincl_ext.
      * exact Hnone.
      * rewrite Σ_cnstr_size_with_cnstr, Σ_cnstr_size_with_storage. lia.
      * exact Hwt'.
      * exact Htc'.
      * Σ_rw. rewrite update_neq by auto. exact Hsto'.
  - (* S2: transitions *)
    intros a' transs' Htrans'. Σ_rw_in Htrans'.
    inv Hwt.
    match goal with Hcond : forall a t, Σ_trans _ a = Some t -> _ |- _ =>
      destruct (Hcond a' transs' Htrans') as [Σ'' [Hincl [Hwt' Htyped]]]
    end.
    exists Σ''. split; [|split].
    + eapply Σ_incl_trans; [exact Hincl|]. exact Hincl_ext.
    + exact Hwt'.
    + exact Htyped.
Qed.

Lemma extending_Σ_well_typed :
  forall Σ c Σ',
    Σ_well_typed Σ ->
    type_contract Σ c Σ' ->
    Σ_well_typed Σ'.
Proof.
  intros sg1 c1 sg1' Hwt Htc.
  pose proof Htc as Htc0.
  pose proof (type_contract_Σ_incl _ _ _ Htc0) as Hincl_ext.
  inversion Htc; subst. subst Σ'' Σ' Σ'0.
  constructor.
  - (* S0: storage well-formedness *)
    intros a' layout' Hsto'.
    rewrite Σ_storage_with_trans, Σ_storage_with_cnstr, Σ_storage_with_storage in Hsto'.
    destruct (String.eqb_spec a0 a').
    + subst. rewrite update_eq in Hsto'. injection Hsto' as Heql. subst layout'.
      assert (Hlwf : Forall (fun p => slot_type_wf sg1 (snd p)) layout)
        by (inv H2; assumption).
      eapply Forall_impl; [|exact Hlwf].
      intros p Hp. eapply slot_type_wf_incl; eauto.
    + rewrite update_neq in Hsto' by auto.
      inv Hwt.
      match goal with Hswf : forall a l, Σ_storage _ a = Some l -> _ |- _ =>
        eapply Forall_impl; [|exact (Hswf _ _ Hsto')]
      end.
      intros p Hp. eapply slot_type_wf_incl; eauto.
  - (* S1: constructors *)
    intros a' ctor' Hctor'.
    rewrite Σ_cnstr_with_trans, Σ_cnstr_with_cnstr, Σ_cnstr_with_storage in Hctor'.
    destruct (String.eqb_spec a0 a').
    + subst. rewrite update_eq in Hctor'. injection Hctor' as <-.
      exists sg1, layout. split; [|split; [|split; [|split; [|split]]]].
      * exact Hincl_ext.
      * unfold dom in H0. destruct (Σ_cnstr sg1 a0) eqn:E; [exfalso; apply H0; eauto|reflexivity].
      * rewrite Σ_cnstr_size_with_trans, Σ_cnstr_size_with_cnstr, Σ_cnstr_size_with_storage. lia.
      * exact Hwt.
      * exact H2.
      * rewrite Σ_storage_with_trans, Σ_storage_with_cnstr, Σ_storage_with_storage.
        apply update_eq.
    + rewrite update_neq in Hctor' by auto.
      inv Hwt.
      match goal with
      | [Hcond : forall a c, Σ_cnstr sg1 a = Some c -> _ |- _] =>
        destruct (Hcond _ _ Hctor') as [sg2 [layout' [Hincl [Hnone [Hlt [Hwt' [Htc' Hsto']]]]]]]
      end.
      exists sg2, layout'. split; [|split; [|split; [|split; [|split]]]].
      * eapply Σ_incl_trans; [exact Hincl|]. exact Hincl_ext.
      * exact Hnone.
      * eapply Nat.lt_trans; [exact Hlt|].
        rewrite Σ_cnstr_size_with_trans, Σ_cnstr_size_with_cnstr, Σ_cnstr_size_with_storage. lia.
      * exact Hwt'.
      * exact Htc'.
      * rewrite Σ_storage_with_trans, Σ_storage_with_cnstr, Σ_storage_with_storage.
        rewrite update_neq by auto. exact Hsto'.
  - (* S2: transitions *)
    intros a' transs' Htrans'.
    rewrite Σ_trans_with_trans in Htrans'.
    destruct (String.eqb_spec a0 a').
    + subst. rewrite update_eq in Htrans'. injection Htrans' as <-.
      eexists. split; [|split].
      * eapply Σ_incl_with_trans_fresh.
        rewrite Σ_trans_with_cnstr, Σ_trans_with_storage. exact H1.
      * eapply Σ_well_typed_intermediate; eauto.
      * exact H3.
    + rewrite update_neq in Htrans' by auto.
      rewrite Σ_trans_with_cnstr, Σ_trans_with_storage in Htrans'.
      inv Hwt.
      match goal with
      | [Hcond : forall a t, Σ_trans sg1 a = Some t -> _ |- _] =>
        destruct (Hcond _ _ Htrans') as [sg2 [Hincl [Hwt' Htyped]]]
      end.
      exists sg2. split; [|split].
      * eapply Σ_incl_trans; [exact Hincl|].
        eapply type_contract_Σ_incl. exact Htc0.
      * exact Hwt'.
      * exact Htyped.
Qed.

(* ================================================================= *)
(** ** Well-typed State is Well-founded (Theorem 7.1 of tech report §7) *)

Theorem wf_state :
  forall Σ c Σ',
    type_contract Σ c Σ' ->
    Σ_wf Σ ->
    Σ_storage_wf Σ ->
    Σ_wf Σ'.
Proof.
  intros sg1 c1 sg1' Htc Hwf Hswf.
  inversion Htc; subst. subst Σ'' Σ' Σ'0.
  assert (Hdep_equiv : forall b d, d <> a0 ->
    (contract_dep (Σ_with_trans (Σ_with_cnstr (Σ_with_storage sg1 a0 layout)
        a0 (contract_ctor c1)) a0 (contract_trans c1)) b d <-> contract_dep sg1 b d)).
  { intros b d Hne. unfold contract_dep.
    split; intros [x Hx]; exists x; unfold Σ_storage_var in *;
      rewrite Σ_storage_with_trans, Σ_storage_with_cnstr, Σ_storage_with_storage in *;
      rewrite update_neq in * by auto; exact Hx. }
  assert (Hno_dep_a0 : forall z, ~ contract_dep sg1 z a0).
  { intros z [x Hx]. apply H. unfold Σ_storage_var in Hx.
    destruct (Σ_storage sg1 a0) eqn:E; [exists s; exact E|].
    destruct Hx; discriminate. }
  set (Σ_final := Σ_with_trans (Σ_with_cnstr (Σ_with_storage sg1 a0 layout)
        a0 (contract_ctor c1)) a0 (contract_trans c1)) in *.
  assert (Htransfer : forall z, Acc (contract_dep sg1) z -> z <> a0 ->
    Acc (contract_dep Σ_final) z).
  { intros z Hacc. induction Hacc as [z _ IH]. intro Hne.
    constructor. intros w Hw.
    apply Hdep_equiv in Hw; [|exact Hne].
    destruct (String.eqb_spec w a0).
    - subst. exfalso. apply H. apply Hswf with z. exact Hw.
    - apply IH; auto. }
  assert (Hlayout_wf : Forall (fun p => slot_type_wf sg1 (snd p)) layout).
  { inversion H2; auto. }
  assert (Hlayout_dep_dom : forall w x,
    (alist_lookup layout x = Some (SContract w) \/
     alist_lookup layout x = Some (SAbi (AContractAddr w))) ->
    dom (Σ_storage sg1) w).
  { intros w x [Hx|Hx];
    destruct (alist_lookup_In _ _ _ _ Hx) as [[pn ps] [Hin Hst]]; simpl in Hst; subst;
    pose proof (proj1 (Forall_forall _ _) Hlayout_wf _ Hin) as Hwf0; simpl in Hwf0;
    inversion Hwf0; subst; auto;
    match goal with
    | [Ha : abi_type_wf _ (AContractAddr _) |- _] => inversion Ha; subst; auto
    end. }
  assert (Hdep_a0_dom : forall w,
    contract_dep Σ_final w a0 -> dom (Σ_storage sg1) w).
  { intros w [x Hx]. unfold Σ_storage_var in Hx. unfold Σ_final in Hx.
    rewrite Σ_storage_with_trans, Σ_storage_with_cnstr, Σ_storage_with_storage in Hx.
    rewrite update_eq in Hx. eapply Hlayout_dep_dom. exact Hx. }
  intro y.
  destruct (String.eqb_spec y a0).
  - subst. constructor. intros w Hw.
    assert (Hne : w <> a0).
    { intro Heq. subst. exact (H (Hdep_a0_dom _ Hw)). }
    apply Htransfer; auto. apply Hwf.
  - apply Htransfer; auto. apply Hwf.
Qed.

(* ================================================================= *)
(** ** Σ_storage_wf is preserved by type_contract *)

Lemma type_contract_preserves_storage_wf :
  forall Σ c Σ',
    type_contract Σ c Σ' ->
    Σ_storage_wf Σ ->
    Σ_storage_wf Σ'.
Proof.
  intros sg1 c1 sg1' Htc Hswf.
  inversion Htc; subst. subst Σ'' Σ' Σ'0.
  intros d b Hdep.
  destruct Hdep as [x Hx].
  unfold Σ_storage_var in Hx.
  rewrite Σ_storage_with_trans in Hx.
  rewrite Σ_storage_with_cnstr in Hx.
  rewrite Σ_storage_with_storage in Hx.
  assert (Hlayout_wf : Forall (fun p => slot_type_wf sg1 (snd p)) layout).
  { match goal with
    | [Htctor : type_constructor _ _ _ _ |- _] => inversion Htctor; auto
    end. }
  destruct (String.eqb_spec (contract_name c1) d).
  - subst. rewrite update_eq in Hx.
    assert (Hdom : dom (Σ_storage sg1) b).
    { destruct Hx as [Hx|Hx];
      destruct (alist_lookup_In _ _ _ _ Hx) as [[pn ps] [Hin Hst]]; simpl in Hst; subst;
      pose proof (proj1 (Forall_forall _ _) Hlayout_wf _ Hin) as Hwf0; simpl in Hwf0;
      inversion Hwf0; subst; auto;
      match goal with
      | [Ha : abi_type_wf _ (AContractAddr _) |- _] => inversion Ha; subst; auto
      end. }
    destruct Hdom as [v Hv].
    unfold dom. exists v.
    rewrite Σ_storage_with_trans.
    rewrite Σ_storage_with_cnstr.
    rewrite Σ_storage_with_storage.
    destruct (String.eqb_spec (contract_name c1) b).
    + subst. exfalso.
      match goal with
      | [Hfresh : ~ dom (Σ_storage sg1) _ |- _] => apply Hfresh; exists v; exact Hv
      end.
    + rewrite update_neq by auto. exact Hv.
  - rewrite update_neq in Hx by auto.
    assert (Hdom : dom (Σ_storage sg1) b).
    { apply Hswf with d. exists x.
      unfold Σ_storage_var. destruct (Σ_storage sg1 d) eqn:E.
      + exact Hx.
      + destruct Hx as [Hx'|Hx']; discriminate. }
    destruct Hdom as [v Hv].
    unfold dom. exists v.
    rewrite Σ_storage_with_trans.
    rewrite Σ_storage_with_cnstr.
    rewrite Σ_storage_with_storage.
    destruct (String.eqb_spec (contract_name c1) b).
    + subst. exfalso.
      match goal with
      | [Hfresh : ~ dom (Σ_storage sg1) _ |- _] => apply Hfresh; exists v; exact Hv
      end.
    + rewrite update_neq by auto. exact Hv.
Qed.

Lemma type_spec_storage_wf :
  forall sp Σ,
    type_spec sp Σ ->
    Σ_storage_wf Σ.
Proof.
  intros sp Σ Hts. induction Hts.
  - intros d b [x Hx]. unfold Σ_storage_var in Hx.
    unfold Σ_storage, Σ_empty in Hx; simpl in Hx.
    destruct Hx as [Hx|Hx]; discriminate.
  - eapply type_contract_preserves_storage_wf; eauto.
Qed.

(* ================================================================= *)
(** ** Environment References Type Safety (Lemma 6.1) *)

Lemma ethenv_typesafety :
  forall Σ iface oid ev alpha s rho l,
    type_env_ref Σ iface oid ev alpha ->
    env_well_typed Σ rho s iface ->
    loc_has_opt_type Σ l s oid ->
    exists v, eval_env rho ev l v /\ has_abi_type Σ v s alpha.
Proof.
  intros Σ iface oid ev alpha s rho l Htyp Henv Hloc.
  destruct Henv as (Hdom & Hvars & [vc [Hvc Htvc]] & [vo [Hvo Htvo]] & [vcv [Hcv Htcv]]).
  inv Htyp.
  - exists vc. split; [constructor; auto | constructor; auto].
  - exists vo. split; [constructor; auto | constructor; auto].
  - exists vcv. split; [constructor; auto | constructor; auto].
  - exists (VAddr l). split; [constructor |].
    simpl in Hloc. inv Hloc.
    match goal with [H : has_abi_type _ _ _ _ |- _] => exact H end.
Qed.

Lemma env_rho_none : forall Σ rho s iface x,
  env_well_typed Σ rho s iface ->
  ~ alist_dom iface x ->
  x <> "caller"%string -> x <> "origin"%string -> x <> "callvalue"%string ->
  rho x = None.
Proof.
  intros Σ rho s iface x [Hdom _] Hni Hc Ho Hcv.
  destruct (rho x) eqn:E; [|reflexivity]. exfalso.
  destruct (proj1 (Hdom x) (ex_intro _ v E)) as [?|[?|[?|?]]]; contradiction.
Qed.

(* ================================================================= *)
(** ** References & Expression Type Safety (Untimed) (Lemmas 6.2/6.3) *)

Lemma ref_expr_typesafety_untimed :
  (forall Σ iface k oid t r sty,
    type_ref Σ iface k oid t r sty -> t = TagU ->
    forall s rho l, env_well_typed Σ rho s iface -> loc_has_opt_type Σ l s oid ->
      exists v, eval_ref (TSUntimed s) rho r l v RTU /\ has_slot_type Σ v s sty) /\
  (forall Σ iface oid t e bt,
    type_expr Σ iface oid t e bt -> t = TagU ->
    forall s rho l, env_well_typed Σ rho s iface -> loc_has_opt_type Σ l s oid ->
      exists v, eval_expr (TSUntimed s) rho e l v /\ has_base_type v bt).
Proof.
  apply type_ref_expr_mutind.
  { (* T_Calldata *)
    intros Σ iface oid t x alpha Hlk _ s rho l Henv Hloc.
    destruct Henv as (_ & Hvars & _).
    destruct (Hvars _ _ Hlk) as [v [Hv Htv]].
    exists v. split; [apply E_Calldata; exact Hv | constructor; exact Htv]. }
  { (* T_Storage *)
    intros Σ iface a x sty layout Hsto Hlk Hni Hnc Hno Hncv _ s rho l Henv Hloc.
    assert (Hrho : rho x = None) by (eapply env_rho_none; eauto).
    simpl in Hloc. inv Hloc.
    match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
    assert (Hssv : Σ_storage_var Σ a x = Some sty)
      by (unfold Σ_storage_var; rewrite Hsto; exact Hlk).
    match goal with
    | [Hvdom : forall _, _ <-> _,
       Hvars : forall _ _, Σ_storage_var _ _ _ = Some _ -> _ |- _] =>
      destruct (proj2 (Hvdom x) (ex_intro _ sty Hssv)) as [w Hw];
      exists w; split; [apply E_Storage; auto |];
      specialize (Hvars _ _ Hssv);
      unfold state_var_force in Hvars; rewrite Hw in Hvars; exact Hvars
    end. }
  { intros; discriminate. }
  { intros; discriminate. }
  { (* T_Coerce *)
    intros Σ iface k oid t r a _ IH HeqU s rho l Henv Hloc. subst.
    destruct (IH eq_refl s rho l Henv Hloc) as [v [Hev Htv]].
    exists v. split; [apply E_Coerce; exact Hev |].
    inv Htv. match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
    constructor. econstructor; eauto. }
  { (* T_Upcast *)
    intros Σ iface k oid t r a _ IH HeqU s rho l Henv Hloc. subst.
    destruct (IH eq_refl s rho l Henv Hloc) as [v [Hev Htv]].
    exists v. split; [exact Hev |].
    inv Htv. match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
    do 3 constructor. }
  { (* T_Field *)
    intros Σ iface k oid t r a x sty _ IH Hssv HeqU s rho l Henv Hloc. subst.
    destruct (IH eq_refl s rho l Henv Hloc) as [v [Hev Htv]].
    inv Htv. match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
    match goal with
    | [Hvdom : forall _, _ <-> _,
       Hvars : forall _ _, Σ_storage_var _ _ _ = Some _ -> _ |- _] =>
      destruct (proj2 (Hvdom x) (ex_intro _ sty Hssv)) as [fv Hfv];
      exists fv; split; [eapply E_Field; eauto |];
      specialize (Hvars _ _ Hssv);
      unfold state_var_force in Hvars; rewrite Hfv in Hvars; exact Hvars
    end. }
  { (* T_MapIndex *)
    intros Σ iface k oid t r e bt mu _ IHr _ IHe HeqU s rho l Henv Hloc. subst.
    destruct (IHr eq_refl s rho l Henv Hloc) as [vr [Hevr Htvr]].
    destruct (IHe eq_refl s rho l Henv Hloc) as [ve [Heve Htve]].
    inv Htvr. match goal with [Hm : has_mapping_type _ _ |- _] => inv Hm end.
    - inv Htve. exists (f n). split;
      [eapply E_RefMapping; eauto; reflexivity |].
      constructor. match goal with [H : forall _, _ -> has_mapping_type _ _ |- _] =>
        apply H; constructor; auto end.
    - inv Htve. exists (f b). split;
      [eapply E_RefMapping; eauto; reflexivity |].
      constructor. match goal with [H : forall _, has_mapping_type _ _ |- _] =>
        apply H end.
    - inv Htve. exists (f a). split;
      [eapply E_RefMapping; eauto; reflexivity |].
      constructor. match goal with [H : forall _, has_mapping_type _ _ |- _] =>
        apply H end. }
  { (* T_Environment *)
    intros Σ iface oid ev alpha Htyp HeqU s rho l Henv Hloc. subst.
    destruct (ethenv_typesafety _ _ _ _ _ _ _ _ Htyp Henv Hloc) as [v [Hev Htv]].
    exists v. split; [apply E_Environment; exact Hev | constructor; exact Htv]. }
  { (* T_Int *)
    intros Σ iface oid t n it Hin _ s rho l Henv Hloc.
    exists (VInt n). split; [constructor | constructor; auto]. }
  { (* T_Bool *)
    intros Σ iface oid t b _ s rho l Henv Hloc.
    exists (VBool b). split; [constructor | constructor]. }
  { (* T_Ref *)
    intros Σ iface oid t k r bt _ IH HeqU s rho l Henv Hloc. subst.
    destruct (IH eq_refl s rho l Henv Hloc) as [v [Hev Htv]].
    inv Htv. match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
    eexists. split; [eapply E_Ref; eauto | auto]. }
  { (* T_Addr *)
    intros Σ iface oid k r a _ IH _ s rho l Henv Hloc.
    destruct (IH eq_refl s rho l Henv Hloc) as [v [Hev Htv]].
    inv Htv. match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
    eexists. split; [eapply E_Addr; eauto | constructor]. }
  { (* T_Range *)
    intros Σ iface oid t e it1 it2 _ IH HeqU s rho l Henv Hloc. subst.
    destruct (IH eq_refl s rho l Henv Hloc) as [v [Hev Htv]]. inv Htv.
    destruct (classic (in_range it1 n)).
    - exists (VBool true). split; [eapply E_RangeTrue; eauto | constructor].
    - exists (VBool false). split; [eapply E_RangeFalse; eauto | constructor]. }
  { (* T_BopI *)
    intros Σ iface oid t e1 op e2 it1 it2 _ IH1 _ IH2 HeqU s rho l Henv Hloc. subst.
    destruct (IH1 eq_refl s rho l Henv Hloc) as [v1 [Hev1 Htv1]].
    destruct (IH2 eq_refl s rho l Henv Hloc) as [v2 [Hev2 Htv2]].
    inv Htv1. inv Htv2.
    destruct (int_binop_dec op OpDiv) as [->|Hnd].
    - destruct (Z.eq_dec n0 0) as [->|Hnz].
      + exists (VInt 0). split; [eapply E_DivZero; eauto | constructor; simpl; auto].
      + exists (VInt (Z.div n n0)). split; [eapply E_Div; eauto | constructor; simpl; auto].
    - destruct (int_binop_dec op OpMod) as [->|Hnm].
      + destruct (Z.eq_dec n0 0) as [->|Hnz].
        * exists (VInt 0). split; [eapply E_ModZero; eauto | constructor; simpl; auto].
        * exists (VInt (Z.modulo n n0)). split; [eapply E_Mod; eauto | constructor; simpl; auto].
      + exists (VInt (eval_int_binop op n n0)). split;
        [eapply E_BopI; eauto | constructor; simpl; auto]. }
  { (* T_NumConv *)
    intros Σ iface oid t e it _ IH HeqU s rho l Henv Hloc. subst.
    destruct (IH eq_refl s rho l Henv Hloc) as [v [Hev Htv]]. inv Htv.
    exists (VInt n). split; [exact Hev | constructor; simpl; auto]. }
  { (* T_BopB *)
    intros Σ iface oid t e1 op e2 _ IH1 _ IH2 HeqU s rho l Henv Hloc. subst.
    destruct (IH1 eq_refl s rho l Henv Hloc) as [v1 [Hev1 Htv1]].
    destruct (IH2 eq_refl s rho l Henv Hloc) as [v2 [Hev2 Htv2]].
    inv Htv1. inv Htv2.
    exists (VBool (eval_bool_binop op b b0)). split;
    [eapply E_BopB; eauto | constructor]. }
  { (* T_Neg *)
    intros Σ iface oid t e _ IH HeqU s rho l Henv Hloc. subst.
    destruct (IH eq_refl s rho l Henv Hloc) as [v [Hev Htv]]. inv Htv.
    exists (VBool (negb b)). split; [eapply E_Neg; eauto | constructor]. }
  { (* T_Cmp *)
    intros Σ iface oid t e1 op e2 it _ IH1 _ IH2 HeqU s rho l Henv Hloc. subst.
    destruct (IH1 eq_refl s rho l Henv Hloc) as [v1 [Hev1 Htv1]].
    destruct (IH2 eq_refl s rho l Henv Hloc) as [v2 [Hev2 Htv2]].
    inv Htv1. inv Htv2.
    exists (VBool (eval_cmp op n n0)). split;
    [eapply E_Cmp; eauto | constructor]. }
  { (* T_ITE *)
    intros Σ iface oid t e1 e2 e3 bt _ IH1 _ IH2 _ IH3 HeqU s rho l Henv Hloc. subst.
    destruct (IH1 eq_refl s rho l Henv Hloc) as [vc [Hevc Htvc]]. inv Htvc.
    destruct b.
    - destruct (IH2 eq_refl s rho l Henv Hloc) as [v2 [Hev2 Htv2]].
      exists v2. split; [eapply E_ITETrue; eauto | exact Htv2].
    - destruct (IH3 eq_refl s rho l Henv Hloc) as [v3 [Hev3 Htv3]].
      exists v3. split; [eapply E_ITEFalse; eauto | exact Htv3]. }
  { (* T_Eq *)
    intros Σ iface oid t e1 e2 bt _ IH1 _ IH2 HeqU s rho l Henv Hloc. subst.
    destruct (IH1 eq_refl s rho l Henv Hloc) as [v1 [Hev1 Htv1]].
    destruct (IH2 eq_refl s rho l Henv Hloc) as [v2 [Hev2 Htv2]].
    destruct (classic (v1 = v2)) as [->|Hne].
    - exists (VBool true). split; [eapply E_EqTrue; eauto | constructor].
    - exists (VBool false). split; [eapply E_EqFalse; eauto | constructor]. }
Qed.

Lemma ref_typesafety_untimed :
  forall Σ iface oid k r sty s rho l,
    type_ref Σ iface k oid TagU r sty ->
    env_well_typed Σ rho s iface ->
    loc_has_opt_type Σ l s oid ->
    exists v,
      eval_ref (TSUntimed s) rho r l v RTU /\
      has_slot_type Σ v s sty.
Proof.
  intros. exact (proj1 ref_expr_typesafety_untimed _ _ _ _ _ _ _ H eq_refl _ _ _ H0 H1).
Qed.

Lemma expr_typesafety_untimed :
  forall Σ iface oid e bt s rho l,
    type_expr Σ iface oid TagU e bt ->
    env_well_typed Σ rho s iface ->
    loc_has_opt_type Σ l s oid ->
    exists v,
      eval_expr (TSUntimed s) rho e l v /\
      has_base_type v bt.
Proof.
  intros. exact (proj2 ref_expr_typesafety_untimed _ _ _ _ _ _ H eq_refl _ _ _ H0 H1).
Qed.

(* ================================================================= *)
(** ** References & Expression Type Safety (Timed) (Lemmas 6.4/6.5) *)

Lemma ref_expr_typesafety_timed :
  (forall Σ iface k oid t r sty,
    type_ref Σ iface k oid t r sty -> t = TagT ->
    forall s_pre s_post rho l,
      env_well_typed Σ rho s_pre iface -> env_well_typed Σ rho s_post iface ->
      loc_has_opt_type Σ l s_pre oid -> loc_has_opt_type Σ l s_post oid ->
      exists v tp,
        eval_ref (TSTimed s_pre s_post) rho r l v tp /\
        (tp = RTPre \/ tp = RTPost) /\
        (tp = RTPre -> has_slot_type Σ v s_pre sty) /\
        (tp = RTPost -> has_slot_type Σ v s_post sty)) /\
  (forall Σ iface oid t e bt,
    type_expr Σ iface oid t e bt -> t = TagT ->
    forall s_pre s_post rho l,
      env_well_typed Σ rho s_pre iface -> env_well_typed Σ rho s_post iface ->
      loc_has_opt_type Σ l s_pre oid -> loc_has_opt_type Σ l s_post oid ->
      exists v,
        eval_expr (TSTimed s_pre s_post) rho e l v /\
        has_base_type v bt).
Proof.
  apply type_ref_expr_mutind.
  { (* T_Calldata *)
    intros Σ iface oid t x alpha Hlk _ s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post.
    destruct Henv_pre as (_ & Hvars & _).
    destruct (Hvars _ _ Hlk) as [v [Hv Htv]].
    exists v, RTPre. split; [apply E_CalldataTimed; exact Hv |].
    split; [left; reflexivity |].
    split.
    { intros _. constructor. exact Htv. }
    { intros; discriminate. } }
  { (* T_Storage *) intros; discriminate. }
  { (* T_StoragePre *)
    intros Σ iface a x sty layout Hsto Hlk Hni Hnc Hno Hncv _ s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post.
    assert (Hrho : rho x = None) by (eapply env_rho_none; eauto).
    simpl in Hloc_pre. inv Hloc_pre.
    match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
    assert (Hssv : Σ_storage_var Σ a x = Some sty)
      by (unfold Σ_storage_var; rewrite Hsto; exact Hlk).
    match goal with
    | [Hvdom : forall _, _ <-> _,
       Hvars : forall _ _, Σ_storage_var _ _ _ = Some _ -> _ |- _] =>
      destruct (proj2 (Hvdom x) (ex_intro _ sty Hssv)) as [w Hw];
      exists w, RTPre; split; [apply E_StoragePre; auto |];
      split; [left; reflexivity |];
      split
    end.
    { intros _. match goal with
      | [Hvars : forall _ _, Σ_storage_var _ _ _ = Some _ -> _ |- _] =>
        specialize (Hvars _ _ Hssv);
        unfold state_var_force in Hvars; rewrite Hw in Hvars; exact Hvars end. }
    { intros; discriminate. } }
  { (* T_StoragePost *)
    intros Σ iface a x sty layout Hsto Hlk Hni Hnc Hno Hncv _ s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post.
    assert (Hrho : rho x = None) by (eapply env_rho_none; eauto).
    simpl in Hloc_post. inv Hloc_post.
    match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
    assert (Hssv : Σ_storage_var Σ a x = Some sty)
      by (unfold Σ_storage_var; rewrite Hsto; exact Hlk).
    match goal with
    | [Hvdom : forall _, _ <-> _,
       Hvars : forall _ _, Σ_storage_var _ _ _ = Some _ -> _ |- _] =>
      destruct (proj2 (Hvdom x) (ex_intro _ sty Hssv)) as [w Hw];
      exists w, RTPost; split; [apply E_StoragePost; auto |];
      split; [right; reflexivity |];
      split
    end.
    { intros; discriminate. }
    { intros _. match goal with
      | [Hvars : forall _ _, Σ_storage_var _ _ _ = Some _ -> _ |- _] =>
        specialize (Hvars _ _ Hssv);
        unfold state_var_force in Hvars; rewrite Hw in Hvars; exact Hvars end. } }
  { (* T_Coerce *)
    intros Σ iface k oid t r a _ IH HeqT s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post. subst.
    destruct (IH eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v [tp [Hev [Hor [Hpre Hpost]]]]].
    exists v, tp. split; [apply E_Coerce; exact Hev |].
    split; [exact Hor |].
    split; intro Heq.
    { specialize (Hpre Heq). inv Hpre.
      match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
      constructor. econstructor; eauto. }
    { specialize (Hpost Heq). inv Hpost.
      match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
      constructor. econstructor; eauto. } }
  { (* T_Upcast *)
    intros Σ iface k oid t r a _ IH HeqT s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post. subst.
    destruct (IH eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v [tp [Hev [Hor [Hpre Hpost]]]]].
    exists v, tp. split; [exact Hev |].
    split; [exact Hor |].
    split; intro Heq.
    { specialize (Hpre Heq). inv Hpre.
      match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
      do 3 constructor. }
    { specialize (Hpost Heq). inv Hpost.
      match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
      do 3 constructor. } }
  { (* T_Field *)
    intros Σ iface k oid t r a x sty _ IH Hssv HeqT s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post. subst.
    destruct (IH eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v [tp [Hev [Hor [Hpre Hpost]]]]].
    destruct Hor as [-> | ->].
    { (* RTPre *)
      assert (Htv := Hpre eq_refl).
      inv Htv. match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
      match goal with
      | [Hvdom : forall _, _ <-> _,
         Hvars : forall _ _, Σ_storage_var _ _ _ = Some _ -> _ |- _] =>
        destruct (proj2 (Hvdom x) (ex_intro _ sty Hssv)) as [fv Hfv];
        exists fv, RTPre; split; [eapply E_FieldPre; eauto |];
        split; [left; reflexivity |]; split
      end.
      { intros _. match goal with
        | [Hvars : forall _ _, Σ_storage_var _ _ _ = Some _ -> _ |- _] =>
          specialize (Hvars _ _ Hssv);
          unfold state_var_force in Hvars; rewrite Hfv in Hvars; exact Hvars end. }
      { intros; discriminate. } }
    { (* RTPost *)
      assert (Htv := Hpost eq_refl).
      inv Htv. match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
      match goal with
      | [Hvdom : forall _, _ <-> _,
         Hvars : forall _ _, Σ_storage_var _ _ _ = Some _ -> _ |- _] =>
        destruct (proj2 (Hvdom x) (ex_intro _ sty Hssv)) as [fv Hfv];
        exists fv, RTPost; split; [eapply E_FieldPost; eauto |];
        split; [right; reflexivity |]; split
      end.
      { intros; discriminate. }
      { intros _. match goal with
        | [Hvars : forall _ _, Σ_storage_var _ _ _ = Some _ -> _ |- _] =>
          specialize (Hvars _ _ Hssv);
          unfold state_var_force in Hvars; rewrite Hfv in Hvars; exact Hvars end. } } }
  { (* T_MapIndex *)
    intros Σ iface k oid t r e bt mu _ IHr _ IHe HeqT s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post. subst.
    destruct (IHr eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [vr [tp [Hevr [Hor [Hpre_r Hpost_r]]]]].
    destruct (IHe eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [ve [Heve Htve]].
    destruct Hor as [-> | ->].
    { (* RTPre *)
      assert (Htv := Hpre_r eq_refl). inv Htv.
      match goal with [Hm : has_mapping_type _ _ |- _] => inv Hm end.
      { inv Htve. exists (f n), RTPre. split;
        [eapply E_RefMapping; eauto; reflexivity |].
        split; [left; reflexivity |]. split.
        { intros _. constructor.
          match goal with [H : forall _, _ -> has_mapping_type _ _ |- _] =>
            apply H; constructor; auto end. }
        { intros; discriminate. } }
      { inv Htve. exists (f b), RTPre. split;
        [eapply E_RefMapping; eauto; reflexivity |].
        split; [left; reflexivity |]. split.
        { intros _. constructor.
          match goal with [H : forall _, has_mapping_type _ _ |- _] =>
            apply H end. }
        { intros; discriminate. } }
      { inv Htve. exists (f a), RTPre. split;
        [eapply E_RefMapping; eauto; reflexivity |].
        split; [left; reflexivity |]. split.
        { intros _. constructor.
          match goal with [H : forall _, has_mapping_type _ _ |- _] =>
            apply H end. }
        { intros; discriminate. } } }
    { (* RTPost *)
      assert (Htv := Hpost_r eq_refl). inv Htv.
      match goal with [Hm : has_mapping_type _ _ |- _] => inv Hm end.
      { inv Htve. exists (f n), RTPost. split;
        [eapply E_RefMapping; eauto; reflexivity |].
        split; [right; reflexivity |]. split.
        { intros; discriminate. }
        { intros _. constructor.
          match goal with [H : forall _, _ -> has_mapping_type _ _ |- _] =>
            apply H; constructor; auto end. } }
      { inv Htve. exists (f b), RTPost. split;
        [eapply E_RefMapping; eauto; reflexivity |].
        split; [right; reflexivity |]. split.
        { intros; discriminate. }
        { intros _. constructor.
          match goal with [H : forall _, has_mapping_type _ _ |- _] =>
            apply H end. } }
      { inv Htve. exists (f a), RTPost. split;
        [eapply E_RefMapping; eauto; reflexivity |].
        split; [right; reflexivity |]. split.
        { intros; discriminate. }
        { intros _. constructor.
          match goal with [H : forall _, has_mapping_type _ _ |- _] =>
            apply H end. } } } }
  { (* T_Environment: t = TagU, contradicts t = TagT *) intros; discriminate. }
  { (* T_Int *)
    intros Σ iface oid t n it Hin _ s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post.
    exists (VInt n). split; [constructor | constructor; auto]. }
  { (* T_Bool *)
    intros Σ iface oid t b _ s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post.
    exists (VBool b). split; [constructor | constructor]. }
  { (* T_Ref *)
    intros Σ iface oid t k r bt _ IH HeqT s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post. subst.
    destruct (IH eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v [tp [Hev [Hor [Hpre Hpost]]]]].
    destruct Hor as [-> | ->].
    { assert (Htv := Hpre eq_refl). inv Htv.
      match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
      eexists. split; [eapply E_Ref; eauto | auto]. }
    { assert (Htv := Hpost eq_refl). inv Htv.
      match goal with [Ha : has_abi_type _ _ _ _ |- _] => inv Ha end.
      eexists. split; [eapply E_Ref; eauto | auto]. } }
  { (* T_Addr: TagU only *) intros; discriminate. }
  { (* T_Range *)
    intros Σ iface oid t e it1 it2 _ IH HeqT s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post. subst.
    destruct (IH eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v [Hev Htv]]. inv Htv.
    destruct (classic (in_range it1 n)).
    { exists (VBool true). split; [eapply E_RangeTrue; eauto | constructor]. }
    { exists (VBool false). split; [eapply E_RangeFalse; eauto | constructor]. } }
  { (* T_BopI *)
    intros Σ iface oid t e1 op e2 it1 it2 _ IH1 _ IH2 HeqT s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post. subst.
    destruct (IH1 eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v1 [Hev1 Htv1]].
    destruct (IH2 eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v2 [Hev2 Htv2]].
    inv Htv1. inv Htv2.
    destruct (int_binop_dec op OpDiv) as [->|Hnd].
    { destruct (Z.eq_dec n0 0) as [->|Hnz].
      { exists (VInt 0). split; [eapply E_DivZero; eauto | constructor; simpl; auto]. }
      { exists (VInt (Z.div n n0)). split; [eapply E_Div; eauto | constructor; simpl; auto]. } }
    { destruct (int_binop_dec op OpMod) as [->|Hnm].
      { destruct (Z.eq_dec n0 0) as [->|Hnz].
        { exists (VInt 0). split; [eapply E_ModZero; eauto | constructor; simpl; auto]. }
        { exists (VInt (Z.modulo n n0)). split; [eapply E_Mod; eauto | constructor; simpl; auto]. } }
      { exists (VInt (eval_int_binop op n n0)). split;
        [eapply E_BopI; eauto | constructor; simpl; auto]. } } }
  { (* T_NumConv *)
    intros Σ iface oid t e it _ IH HeqT s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post. subst.
    destruct (IH eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v [Hev Htv]]. inv Htv.
    exists (VInt n). split; [exact Hev | constructor; simpl; auto]. }
  { (* T_BopB *)
    intros Σ iface oid t e1 op e2 _ IH1 _ IH2 HeqT s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post. subst.
    destruct (IH1 eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v1 [Hev1 Htv1]].
    destruct (IH2 eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v2 [Hev2 Htv2]].
    inv Htv1. inv Htv2.
    exists (VBool (eval_bool_binop op b b0)). split;
    [eapply E_BopB; eauto | constructor]. }
  { (* T_Neg *)
    intros Σ iface oid t e _ IH HeqT s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post. subst.
    destruct (IH eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v [Hev Htv]]. inv Htv.
    exists (VBool (negb b)). split; [eapply E_Neg; eauto | constructor]. }
  { (* T_Cmp *)
    intros Σ iface oid t e1 op e2 it _ IH1 _ IH2 HeqT s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post. subst.
    destruct (IH1 eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v1 [Hev1 Htv1]].
    destruct (IH2 eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v2 [Hev2 Htv2]].
    inv Htv1. inv Htv2.
    exists (VBool (eval_cmp op n n0)). split;
    [eapply E_Cmp; eauto | constructor]. }
  { (* T_ITE *)
    intros Σ iface oid t e1 e2 e3 bt _ IH1 _ IH2 _ IH3 HeqT s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post. subst.
    destruct (IH1 eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [vc [Hevc Htvc]]. inv Htvc.
    destruct b.
    { destruct (IH2 eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v2 [Hev2 Htv2]].
      exists v2. split; [eapply E_ITETrue; eauto | exact Htv2]. }
    { destruct (IH3 eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v3 [Hev3 Htv3]].
      exists v3. split; [eapply E_ITEFalse; eauto | exact Htv3]. } }
  { (* T_Eq *)
    intros Σ iface oid t e1 e2 bt _ IH1 _ IH2 HeqT s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post. subst.
    destruct (IH1 eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v1 [Hev1 Htv1]].
    destruct (IH2 eq_refl s_pre s_post rho l Henv_pre Henv_post Hloc_pre Hloc_post) as [v2 [Hev2 Htv2]].
    destruct (classic (v1 = v2)) as [->|Hne].
    { exists (VBool true). split; [eapply E_EqTrue; eauto | constructor]. }
    { exists (VBool false). split; [eapply E_EqFalse; eauto | constructor]. } }
Qed.

Lemma ref_typesafety_timed :
  forall Σ iface oid k r sty s_pre s_post rho l,
    type_ref Σ iface k oid TagT r sty ->
    env_well_typed Σ rho s_pre iface ->
    env_well_typed Σ rho s_post iface ->
    loc_has_opt_type Σ l s_pre oid ->
    loc_has_opt_type Σ l s_post oid ->
    exists v tp,
      eval_ref (TSTimed s_pre s_post) rho r l v tp /\
      (tp = RTPre \/ tp = RTPost) /\
      (tp = RTPre -> has_slot_type Σ v s_pre sty) /\
      (tp = RTPost -> has_slot_type Σ v s_post sty).
Proof.
  intros. exact (proj1 ref_expr_typesafety_timed _ _ _ _ _ _ _ H eq_refl _ _ _ _ H0 H1 H2 H3).
Qed.

Lemma expr_typesafety_timed :
  forall Σ iface oid e bt s_pre s_post rho l,
    type_expr Σ iface oid TagT e bt ->
    env_well_typed Σ rho s_pre iface ->
    env_well_typed Σ rho s_post iface ->
    loc_has_opt_type Σ l s_pre oid ->
    loc_has_opt_type Σ l s_post oid ->
    exists v,
      eval_expr (TSTimed s_pre s_post) rho e l v /\
      has_base_type v bt.
Proof.
  intros. exact (proj2 ref_expr_typesafety_timed _ _ _ _ _ _ H eq_refl _ _ _ _ H0 H1 H2 H3).
Qed.

(* ================================================================= *)
(** ** Mapping Expression Type Safety (Lemma 6.6) *)

Lemma slot_mapping_inv : forall Σ v s mu,
  has_slot_type Σ v s (SMapping mu) -> has_mapping_type v mu.
Proof. intros Σ v s mu H. inv H. assumption. Qed.

Lemma lookup_or_default_typed :
  forall keys vals x def mu,
    has_mapping_type def mu ->
    Forall (fun v => has_mapping_type v mu) vals ->
    has_mapping_type (lookup_or_default keys vals x def) mu.
Proof.
  intros keys. induction keys as [|k ks IH]; intros vals x def mu Hdef Hvals; simpl.
  - exact Hdef.
  - destruct vals as [|v vs]; [exact Hdef|].
    inv Hvals. destruct (value_eqb k x); auto.
Qed.

Lemma lookup_or_apply_typed_Z :
  forall keys vals n it mu f,
    (forall n0, has_base_type (VInt n0) (TInt it) -> has_mapping_type (f n0) mu) ->
    has_base_type (VInt n) (TInt it) ->
    Forall (fun v => has_mapping_type v mu) vals ->
    has_mapping_type (lookup_or_apply keys vals (VInt n) (VMapZ f)) mu.
Proof.
  intros keys. induction keys as [|k ks IH]; intros vals n it mu f Hf Hin Hvals; simpl.
  - apply Hf; exact Hin.
  - destruct vals as [|v vs]; [apply Hf; exact Hin|].
    inv Hvals. destruct (value_eqb k (VInt n)); [exact H1 | apply IH with (it := it); auto].
Qed.

Lemma lookup_or_apply_typed_B :
  forall keys vals b mu f,
    (forall b0, has_mapping_type (f b0) mu) ->
    Forall (fun v => has_mapping_type v mu) vals ->
    has_mapping_type (lookup_or_apply keys vals (VBool b) (VMapB f)) mu.
Proof.
  intros keys. induction keys as [|k ks IH]; intros vals b mu f Hf Hvals; simpl.
  - apply Hf.
  - destruct vals as [|v vs]; [apply Hf|].
    inv Hvals. destruct (value_eqb k (VBool b)); auto.
Qed.

Lemma lookup_or_apply_typed_A :
  forall keys vals a mu f,
    (forall a0, has_mapping_type (f a0) mu) ->
    Forall (fun v => has_mapping_type v mu) vals ->
    has_mapping_type (lookup_or_apply keys vals (VAddr a) (VMapA f)) mu.
Proof.
  intros keys. induction keys as [|k ks IH]; intros vals a mu f Hf Hvals; simpl.
  - apply Hf.
  - destruct vals as [|v vs]; [apply Hf|].
    inv Hvals. destruct (value_eqb k (VAddr a)); auto.
Qed.

Lemma eval_binding_keys_typed :
  forall (bindings : list (expr * map_expr)) Σ iface oid bt s rho l,
    Forall (fun p => type_expr Σ iface oid TagU (fst p) bt) bindings ->
    env_well_typed Σ rho s iface ->
    loc_has_opt_type Σ l s oid ->
    exists keys,
      Forall2 (fun p k => eval_expr (TSUntimed s) rho (fst p) l k) bindings keys /\
      Forall (fun v => has_base_type v bt) keys.
Proof.
  induction bindings as [|[e m] rest IH]; intros Σ iface oid bt s rho l Hall Henv Hloc.
  - exists []. split; constructor.
  - inv Hall. simpl in H1.
    destruct (expr_typesafety_untimed _ _ _ _ _ _ _ _ H1 Henv Hloc) as [v [Hev Htv]].
    destruct (IH _ _ _ _ _ _ _ H2 Henv Hloc) as [ks [Heks Htks]].
    exists (v :: ks). split; constructor; auto.
Qed.

Lemma eval_binding_vals_realized :
  forall (bindings : list (expr * map_expr)) mu ts rho l,
    Forall (fun p =>
      exists v, eval_mapexpr ts rho (snd p) l v /\ has_mapping_type v mu) bindings ->
    exists vals,
      Forall2 (fun p v => eval_mapexpr ts rho (snd p) l v) bindings vals /\
      Forall (fun v => has_mapping_type v mu) vals.
Proof.
  induction bindings as [|[e m] rest IH]; intros mu ts rho l Hall.
  - exists []. split; constructor.
  - inv Hall. simpl in H1. destruct H1 as [u [Heu Htu]].
    destruct (IH _ _ _ _ H2) as [us [Heus Htus]].
    exists (u :: us). split; constructor; auto.
Qed.

Lemma build_map_typed :
  forall bt mu keys vals,
    default_value_typable mu ->
    Forall (fun v => has_mapping_type v mu) vals ->
    exists f,
      build_map_from_bindings keys vals (MMapping bt mu) = Some f /\
      has_mapping_type f (MMapping bt mu).
Proof.
  intros bt mu keys vals Hdef Htvals.
  assert (Hdefm : has_mapping_type (default_value mu) mu)
    by (apply default_has_mapping_type; exact Hdef).
  destruct bt; simpl; eexists; (split; [reflexivity|]).
  - constructor. intros n Hin. apply lookup_or_default_typed; auto.
  - constructor. intros b. apply lookup_or_default_typed; auto.
  - constructor. intros a. apply lookup_or_default_typed; auto.
Qed.

Lemma update_map_typed :
  forall bt mu keys vals vold,
    has_mapping_type vold (MMapping bt mu) ->
    Forall (fun v => has_mapping_type v mu) vals ->
    exists f,
      update_map_from_bindings keys vals vold (MMapping bt mu) = Some f /\
      has_mapping_type f (MMapping bt mu).
Proof.
  intros bt mu keys vals vold Hvold Htvals.
  inv Hvold.
  { simpl. eexists. split; [reflexivity|].
    constructor. intros n Hbt.
    apply lookup_or_apply_typed_Z with (it := it); assumption. }
  { simpl. eexists. split; [reflexivity|].
    constructor. intros b.
    apply lookup_or_apply_typed_B; assumption. }
  { simpl. eexists. split; [reflexivity|].
    constructor. intros a.
    apply lookup_or_apply_typed_A; assumption. }
Qed.

Lemma mapexpr_typesafety_aux :
  forall Σ iface oid m mu,
    type_mapexpr Σ iface oid m mu ->
    forall s rho l,
      env_well_typed Σ rho s iface ->
      loc_has_opt_type Σ l s oid ->
      exists v,
        eval_mapexpr (TSUntimed s) rho m l v /\
        has_mapping_type v mu.
Proof.
  fix IH 6.
  intros Σ iface oid m mu Htyp.
  destruct Htyp; intros s rho l Henv Hloc.
  - (* T_Exp *)
    match goal with [He : type_expr _ _ _ _ _ _ |- _] =>
      destruct (expr_typesafety_untimed _ _ _ _ _ _ _ _ He Henv Hloc) as [v [Hev Htv]] end.
    exists v. split; [apply E_MExp; exact Hev | constructor; exact Htv].
  - (* T_Mapping *)
    match goal with [H : default_value_typable _ |- _] => rename H into Hd end.
    match goal with [H : Forall (fun p => type_expr _ _ _ _ (fst p) _) _ |- _] => rename H into Hkeys_ty end.
    match goal with [H : Forall (fun p => type_mapexpr _ _ _ (snd p) _) _ |- _] => rename H into Hvals_ty end.
    destruct (eval_binding_keys_typed _ _ _ _ _ _ _ _ Hkeys_ty Henv Hloc) as [keys [Hkeys Htkeys]].
    assert (Hvals_ih : Forall (fun p =>
      exists v, eval_mapexpr (TSUntimed s) rho (snd p) l v /\ has_mapping_type v mu) bindings).
    { clear Hkeys_ty Hd Hkeys Htkeys keys.
      induction Hvals_ty as [|p rest Hm Hrest IHF].
      { constructor. }
      { constructor.
        { apply (IH _ _ _ _ _ Hm _ _ _ Henv Hloc). }
        { apply IHF. } } }
    destruct (eval_binding_vals_realized _ _ _ _ _ Hvals_ih) as [vals [Hvals Htvals]].
    destruct (build_map_typed bt mu keys vals Hd Htvals) as [fv [Hbuild Htfv]].
    exists fv. split; [eapply E_Mapping; eauto | exact Htfv].
  - (* T_MappingUpd *)
    match goal with [Hr : type_ref _ _ _ _ _ _ (SMapping (MMapping _ _)) |- _] =>
      destruct (ref_typesafety_untimed _ _ _ _ _ _ _ _ _ Hr Henv Hloc) as [vold [Hevold Htvold]] end.
    apply slot_mapping_inv in Htvold.
    match goal with [H : Forall (fun p => type_expr _ _ _ _ (fst p) _) _ |- _] => rename H into Hkeys_ty end.
    match goal with [H : Forall (fun p => type_mapexpr _ _ _ (snd p) _) _ |- _] => rename H into Hvals_ty end.
    destruct (eval_binding_keys_typed _ _ _ _ _ _ _ _ Hkeys_ty Henv Hloc) as [keys [Hkeys Htkeys]].
    assert (Hvals_ih : Forall (fun p =>
      exists v, eval_mapexpr (TSUntimed s) rho (snd p) l v /\ has_mapping_type v mu) bindings).
    { clear Hkeys_ty Htvold Hkeys Htkeys keys Hevold vold.
      induction Hvals_ty as [|p rest Hm Hrest IHF].
      { constructor. }
      { constructor.
        { apply (IH _ _ _ _ _ Hm _ _ _ Henv Hloc). }
        { apply IHF. } } }
    destruct (eval_binding_vals_realized _ _ _ _ _ Hvals_ih) as [vals [Hvals Htvals]].
    destruct (update_map_typed _ _ keys vals _ Htvold Htvals) as [fv [Hupd Htfv]].
    exists fv. split; [eapply E_MappingUpd; eauto | exact Htfv].
Qed.

Lemma mapexpr_typesafety :
  forall Σ iface oid m mu s rho l,
    type_mapexpr Σ iface oid m mu ->
    env_well_typed Σ rho s iface ->
    loc_has_opt_type Σ l s oid ->
    exists v,
      eval_mapexpr (TSUntimed s) rho m l v /\
      has_mapping_type v mu.
Proof.
  intros. eapply mapexpr_typesafety_aux; eauto.
Qed.

(** Helper: inverting has_slot_type for SContract *)
Lemma slot_contract_inv : forall Σ v s a,
  has_slot_type Σ v s (SContract a) ->
  has_abi_type Σ v s (AContractAddr a).
Proof. intros. inv H. assumption. Qed.

(** Helper: loc_has_opt_type weakening *)
Lemma loc_has_opt_type_weak : forall Σ l s s' oid,
  state_incl s s' ->
  loc_has_opt_type Σ l s oid ->
  loc_has_opt_type Σ l s' oid.
Proof.
  intros Σ l s s' oid Hincl Hloc.
  unfold loc_has_opt_type in *. destruct oid.
  - exact I.
  - eapply valuetyp_storage_weak_slot; eauto.
Qed.

(** Helper: inverting has_slot_type for SAbi *)
Lemma slot_abi_inv : forall Σ v s alpha,
  has_slot_type Σ v s (SAbi alpha) ->
  has_abi_type Σ v s alpha.
Proof. intros. inv H. assumption. Qed.

(* ================================================================= *)
(** ** Sigma-down transfer for typing *)

(** Key lemma: has_abi_type for AContractAddr can be transferred from
    a bigger contract_env to a smaller one, given the contract is well-formed
    in the smaller contract_env. Proved by Acc induction on contract_dep. *)
Lemma has_abi_type_Σ_down_contract :
  forall Σ Σ',
    Σ_incl Σ' Σ ->
    Σ_well_typed Σ' ->
    forall a,
      Acc (fun b c => contract_dep Σ' b c) a ->
      dom (Σ_storage Σ') a ->
      forall v s,
        has_abi_type Σ v s (AContractAddr a) ->
        has_abi_type Σ' v s (AContractAddr a).
Proof.
  intros Σ Σ' Hincl Hwt a Hacc.
  induction Hacc as [a _ IH].
  intros Hdom_a v s Hab.
  inversion Hab as [| ? ? ? ? Hsd Hds Hstype Hdom_eq Htyp_corr]; subst; clear Hab.
  assert (Hsto_eq : Σ_storage Σ' a = Σ_storage Σ a).
  { destruct Hdom_a as [layout' Hlayout'].
    rewrite (proj1 Hincl _ _ Hlayout'). exact Hlayout'. }
  assert (Hssv_eq : forall x, Σ_storage_var Σ' a x = Σ_storage_var Σ a x).
  { intro x. unfold Σ_storage_var. rewrite Hsto_eq. reflexivity. }
  assert (Hswf_a : forall layout', Σ_storage Σ' a = Some layout' ->
    Forall (fun p => slot_type_wf Σ' (snd p)) layout').
  { destruct Hwt as [? Hswf0 _ _]. intros. eapply Hswf0; eassumption. }
  assert (Hswf_var : forall x st, Σ_storage_var Σ a x = Some st -> slot_type_wf Σ' st).
  { intros x st Hx. destruct Hdom_a as [la Hla].
    specialize (Hswf_a la Hla). unfold Σ_storage_var in Hx.
    rewrite <- Hsto_eq, Hla in Hx.
    apply alist_lookup_In in Hx. destruct Hx as [p [Hp1 Hp2]].
    simpl in Hp2; subst. rewrite Forall_forall in Hswf_a. exact (Hswf_a p Hp1). }
  constructor.
  - exact Hsd.
  - exact Hdom_a.
  - exact Hstype.
  - intros x. rewrite Hdom_eq.
    split; intros [st Hst]; exists st; rewrite Hssv_eq in *; exact Hst.
  - intros x st Hssv.
    rewrite Hssv_eq in Hssv.
    specialize (Htyp_corr x st Hssv).
    specialize (Hswf_var x st Hssv).
    destruct st as [mu | alpha | c].
    + inv Htyp_corr. constructor. assumption.
    + destruct alpha as [bt | c].
      * inv Htyp_corr.
        match goal with [Habi : has_abi_type _ _ _ _ |- _] => inv Habi end.
        constructor. constructor. assumption.
      * inv Htyp_corr.
        match goal with [Habi : has_abi_type _ _ _ _ |- _] =>
          constructor; apply (IH c) end.
        { exists x. right. rewrite Hssv_eq. assumption. }
        { inv Hswf_var.
          match goal with [Hw : abi_type_wf _ _ |- _] => inv Hw; assumption end. }
        { assumption. }
    + inv Htyp_corr.
      match goal with [Habi : has_abi_type _ _ _ _ |- _] =>
        constructor; apply (IH c) end.
      { exists x. left. rewrite Hssv_eq. assumption. }
      { inv Hswf_var. assumption. }
      { assumption. }
Qed.

Lemma has_slot_type_Σ_down :
  forall Σ Σ' v s st,
    Σ_incl Σ' Σ ->
    Σ_wf Σ' ->
    Σ_well_typed Σ' ->
    slot_type_wf Σ' st ->
    has_slot_type Σ v s st -> has_slot_type Σ' v s st.
Proof.
  intros Σ Σ' v s st Hincl Hwf Hwt Hswf Hst.
  destruct st as [mu | alpha | a].
  - inv Hst. constructor. assumption.
  - destruct alpha as [bt | a].
    + inversion Hst as [| ? ? ? ? Habi_bt |]; subst; clear Hst.
      inversion Habi_bt; subst; clear Habi_bt.
      constructor. constructor. assumption.
    + inversion Hst as [| ? ? ? ? Habi |]; subst; clear Hst.
      constructor. eapply has_abi_type_Σ_down_contract; eauto.
      { apply Hwf. }
      { inv Hswf. inversion H0; subst. assumption. }
  - inversion Hst as [| | ? ? ? ? Habi]; subst; clear Hst.
    constructor. eapply has_abi_type_Σ_down_contract; eauto.
    { apply Hwf. }
    { inv Hswf. assumption. }
Qed.

Lemma env_well_typed_Σ_down :
  forall Σ Σ' rho s iface,
    Σ_incl Σ' Σ ->
    Σ_wf Σ' ->
    Σ_well_typed Σ' ->
    interface_wf Σ' iface ->
    env_well_typed Σ rho s iface ->
    env_well_typed Σ' rho s iface.
Proof.
  intros Σ Σ' rho s iface Hincl Hwf Hwt [Hiwf _] Henv.
  destruct Henv as [Hdom [Htyp [Hcaller [Horigin Hcv]]]].
  refine (conj Hdom (conj _ (conj Hcaller (conj Horigin Hcv)))).
  intros x alpha Hlook.
  destruct (Htyp x alpha Hlook) as [v [Hv Hav]].
  exists v. split; [exact Hv|].
  destruct alpha as [bt | a].
  - inversion Hav; subst; clear Hav. constructor. assumption.
  - eapply has_abi_type_Σ_down_contract; eauto.
    + apply Hwf.
    + rewrite Forall_forall in Hiwf.
      apply alist_lookup_In in Hlook.
      destruct Hlook as [p [Hp1 Hp2]]. simpl in Hp2. subst.
      specialize (Hiwf p Hp1). rewrite Hp2 in Hiwf. simpl in Hiwf.
      inversion Hiwf; subst; assumption.
Qed.

(* ================================================================= *)
(** ** Creates-typed property for store_wt *)

(** Every location in s' either existed in s or has a contract type. *)
Definition creates_typed (Σ : contract_env) (s s' : state) : Prop :=
  forall l, state_dom s' l ->
    state_dom s l \/ exists a, has_slot_type Σ (VAddr l) s' (SContract a).

Lemma creates_typed_refl : forall Σ s, creates_typed Σ s s.
Proof. intros Σ s l Hd. left. exact Hd. Qed.

Lemma creates_typed_trans :
  forall Σ s1 s2 s3,
    creates_typed Σ s1 s2 ->
    creates_typed Σ s2 s3 ->
    (forall v st, has_slot_type Σ v s2 st -> has_slot_type Σ v s3 st) ->
    creates_typed Σ s1 s3.
Proof.
  intros Σ s1 s2 s3 H12 H23 Hpres l Hd3.
  destruct (H23 l Hd3) as [Hd2 | [a Ha]].
  - destruct (H12 l Hd2) as [Hd1 | [a Ha]].
    + left. exact Hd1.
    + right. exists a. apply Hpres. exact Ha.
  - right. exists a. exact Ha.
Qed.

Lemma state_update_var_dom_back :
  forall s l x v l',
    state_dom (state_update_var s l x v) l' -> state_dom s l'.
Proof.
  intros s l x v l' [ls Hls].
  rewrite state_update_var_store in Hls.
  destruct (s l) eqn:Esl.
  - destruct (Nat.eqb_spec l l').
    + subst. exists l0. exact Esl.
    + exists ls. exact Hls.
  - exists ls. exact Hls.
Qed.

Lemma eval_insert_dom_back :
  forall s rho r v l s',
    eval_insert s rho r v l s' ->
    forall l', state_dom s' l' -> state_dom s l'.
Proof.
  intros s rho r v l s' Hins l' Hd'. inv Hins;
    eapply state_update_var_dom_back; eauto.
Qed.

Lemma eval_update_inserts_dom_back :
  forall s rho upds vals l s',
    eval_update_inserts s rho upds vals l s' ->
    forall l', state_dom s' l' -> state_dom s l'.
Proof.
  intros s rho upds vals l s' Hins.
  induction Hins as [| s0 rho0 r se rest v vs l0 s1 s_final Hins1 Hins_rest IH].
  - auto.
  - intros l' Hd'. apply (eval_insert_dom_back _ _ _ _ _ _ Hins1).
    apply IH. exact Hd'.
Qed.

Lemma creates_typed_Σ_up :
  forall Σ Σ' s s',
    Σ_incl Σ Σ' ->
    creates_typed Σ s s' -> creates_typed Σ' s s'.
Proof.
  intros Σ Σ' s s' Hincl Hct l Hd.
  destruct (Hct l Hd) as [Hd0 | [a Ha]].
  - left. exact Hd0.
  - right. exists a. eapply valuetyp_storetyp_weak_slot; eauto.
Qed.

(* ================================================================= *)
(** ** Constructor Cases Evaluate (by well-founded induction) *)

(** Abbreviation: all constructors of Σ evaluate. This is what the
    tech report calls "mutual induction" between SE/create type safety.
    In Rocq, we prove it by Acc induction on contract_dep, then
    derive the universal statement from Σ_wf. *)
Definition ctor_eval_prop (Σ : contract_env) : Prop :=
  forall a ctor,
    Σ_cnstr Σ a = Some ctor ->
    forall s rho,
      env_well_typed Σ rho s (ctor_iface ctor) ->
      Forall (fun pre => eval_expr (TSUntimed s) rho pre dummy_loc (VBool true))
             (ctor_iff ctor) ->
      exists l s',
        eval_ctor_cases (Σ_cnstr Σ) s rho (ctor_cases ctor) a l s' /\
        has_slot_type Σ (VAddr l) s' (SContract a) /\
        state_incl s s' /\
        (forall v st, has_slot_type Σ v s st -> has_slot_type Σ v s' st) /\
        creates_typed Σ s s'.

(** Helper: extract interface_wf for a constructor from Σ_well_typed *)
Lemma ctor_iface_wf : forall Σ a ctor,
  Σ_well_typed Σ ->
  Σ_cnstr Σ a = Some ctor ->
  ~ alist_dom (ctor_iface ctor) "caller"%string /\
  ~ alist_dom (ctor_iface ctor) "origin"%string /\
  ~ alist_dom (ctor_iface ctor) "callvalue"%string.
Proof.
  intros Σ a ctor Hswt Hcl.
  inversion Hswt as [? _ Hswt_c _]; subst.
  destruct (Hswt_c a ctor Hcl) as [Σ' [layout' [_ [_ [_ [_ [Htc _]]]]]]].
  inversion Htc; subst.
  match goal with H : interface_wf _ _ |- _ => destruct H as [_ [? [? ?]]] end.
  auto.
Qed.

(** SE type safety given that constructors evaluate.
    The ctor_eval_prop hypothesis is discharged later by Acc induction. *)
Lemma se_typesafety_with_ctors :
  forall Σ iface oid se sty,
    ctor_eval_prop Σ ->
    Σ_well_typed Σ ->
    type_slotexpr Σ iface oid se sty ->
    forall s rho l,
      env_well_typed Σ rho s iface ->
      loc_has_opt_type Σ l s oid ->
      exists v s',
        eval_slotexpr (Σ_cnstr Σ) s rho se l v s' /\
        has_slot_type Σ v s' sty /\
        state_incl s s' /\
        (forall v' st', has_slot_type Σ v' s st' -> has_slot_type Σ v' s' st') /\
        creates_typed Σ s s'.
Proof.
  intros Σ iface oid se sty Hctors Hswt Htyp.
  induction Htyp using type_slotexpr_ind2;
    intros s rho l Henv Hloc.
  - (* T_SlotMap *)
    destruct (mapexpr_typesafety _ _ _ _ _ _ _ _ H Henv Hloc) as [v [Hev Htv]].
    exists v, s. refine (conj _ (conj _ (conj _ (conj _ _)))).
    + apply E_SlotMap; exact Hev.
    + constructor; exact Htv.
    + intros l' ls' Hl'; exact Hl'.
    + auto.
    + apply creates_typed_refl.
  - (* T_SlotRef *)
    destruct (ref_typesafety_untimed _ _ _ _ _ _ _ _ _ H Henv Hloc) as [v [Hev Htv]].
    exists v, s. refine (conj _ (conj _ (conj _ (conj _ _)))).
    + apply E_SlotRef with (tp := RTU); exact Hev.
    + exact Htv.
    + intros l' ls' Hl'; exact Hl'.
    + auto.
    + apply creates_typed_refl.
  - (* T_SlotAddr *)
    destruct (IHHtyp Hctors Hswt s rho l Henv Hloc) as [v [s' [Hev [Htv [Hincl [Hpres Hct]]]]]].
    exists v, s'. refine (conj _ (conj _ (conj Hincl (conj Hpres Hct)))).
    + apply E_SlotAddr; exact Hev.
    + apply slot_contract_inv in Htv. constructor. exact Htv.
  - (* T_Create *)
    rename H into Hcl, H0 into Hnp, H2 into HIH, H3 into HP4.
    (* Evaluate each argument se using the structural IH *)
    assert (Hse_eval : forall s0 rho0 l0,
      env_well_typed Σ rho0 s0 iface ->
      loc_has_opt_type Σ l0 s0 oid ->
      exists vals s_final,
        eval_slotexpr_list (Σ_cnstr Σ) s0 rho0 ses l0 vals s_final /\
        Forall2 (fun v alpha => has_abi_type Σ v s_final alpha) vals (map snd (ctor_iface ctor)) /\
        state_incl s0 s_final /\
        (forall v' st', has_slot_type Σ v' s0 st' -> has_slot_type Σ v' s_final st') /\
        creates_typed Σ s0 s_final).
    { clear Hcl Hnp HP4 H1.
      induction HIH as [|se0 alpha0 rses ralphas Hse0 _ IHfa];
        intros s0 rho0 l0 Henv0 Hloc0.
      - exists [], s0. refine (conj _ (conj _ (conj _ (conj _ _)))).
        + constructor.
        + constructor.
        + intros l' ls' Hl'; exact Hl'.
        + auto.
        + apply creates_typed_refl.
      - destruct (Hse0 Hctors Hswt s0 rho0 l0 Henv0 Hloc0)
          as [v0 [s1 [Hev0 [Htv0 [Hincl01 [Hpres01 Hct01]]]]]].
        assert (Henv1 : env_well_typed Σ rho0 s1 iface)
          by (eapply valuetyp_storage_weak_env; eauto).
        assert (Hloc1 : loc_has_opt_type Σ l0 s1 oid)
          by (eapply loc_has_opt_type_weak; eauto).
        destruct (IHfa s1 rho0 l0 Henv1 Hloc1)
          as [vs [sf [Hevs [Htvs [Hincl1f [Hpres1f Hct1f]]]]]].
        exists (v0 :: vs), sf. refine (conj _ (conj _ (conj _ (conj _ _)))).
        + eapply E_SlotListCons; eauto.
        + constructor.
          * apply slot_abi_inv. apply Hpres1f. exact Htv0.
          * exact Htvs.
        + intros l' ls' Hl'. apply Hincl1f. apply Hincl01. exact Hl'.
        + intros v' st' Hv'. apply Hpres1f. apply Hpres01. exact Hv'.
        + eapply creates_typed_trans; eauto. }
    destruct (Hse_eval s rho l Henv Hloc)
      as [vals [s_final [Hevl [Htvals [Hincl_sf [Hpres_sf Hct_sf]]]]]].
    set (rho' := build_ctor_env (ctor_iface ctor) vals l (env_origin rho) (VInt 0%Z)).
    assert (Hiffs : Forall (fun pre =>
      eval_expr (TSUntimed s_final) rho' pre dummy_loc (VBool true))
      (ctor_iff ctor)) by (apply HP4 with (s := s); auto).
    assert (Henv_rho' : env_well_typed Σ rho' s_final (ctor_iface ctor)).
    { apply build_ctor_env_well_typed.
      - exact Htvals.
      - (* origin : address *)
        destruct Henv as [_ [_ [_ [[vo [Hvo Htvo]] _]]]].
        unfold env_origin. rewrite Hvo. exact Htvo.
      - (* VInt 0 : uint256 *)
        constructor. simpl. lia.
      - exact (proj1 (ctor_iface_wf Σ a ctor Hswt Hcl)).
      - exact (proj1 (proj2 (ctor_iface_wf Σ a ctor Hswt Hcl))).
      - exact (proj2 (proj2 (ctor_iface_wf Σ a ctor Hswt Hcl))). }
    destruct (Hctors a ctor Hcl s_final rho' Henv_rho' Hiffs)
      as [l' [s' [Heval_cc [Htloc [Hincl_s' [Hpres_s' Hct_s']]]]]].
    exists (VAddr l'), s'. split; [|split; [|split; [|split]]].
    { eapply E_Create; eauto. }
    { exact Htloc. }
    { intros l0 ls0 Hl0. apply Hincl_s'. apply Hincl_sf. exact Hl0. }
    { intros v' st' Hv'. apply Hpres_s'. apply Hpres_sf. exact Hv'. }
    { eapply creates_typed_trans; eauto. }
  - (* T_CreatePayable *)
    rename H into Hcl, H0 into Hpay, H2 into HIH, H3 into Hval.
    (* Evaluate arguments *)
    assert (Hse_eval : forall s0 rho0 l0,
      env_well_typed Σ rho0 s0 iface ->
      loc_has_opt_type Σ l0 s0 oid ->
      exists vals s_final,
        eval_slotexpr_list (Σ_cnstr Σ) s0 rho0 ses l0 vals s_final /\
        Forall2 (fun v alpha => has_abi_type Σ v s_final alpha) vals (map snd (ctor_iface ctor)) /\
        state_incl s0 s_final /\
        (forall v' st', has_slot_type Σ v' s0 st' -> has_slot_type Σ v' s_final st') /\
        creates_typed Σ s0 s_final).
    { clear Hcl Hpay Hval IHHtyp H1.
      induction HIH as [|se0 alpha0 rses ralphas Hse0 _ IHfa];
        intros s0 rho0 l0 Henv0 Hloc0.
      - exists [], s0. refine (conj _ (conj _ (conj _ (conj _ _)))).
        + constructor.
        + constructor.
        + intros l' ls' Hl'; exact Hl'.
        + auto.
        + apply creates_typed_refl.
      - destruct (Hse0 Hctors Hswt s0 rho0 l0 Henv0 Hloc0)
          as [v0 [s1 [Hev0 [Htv0 [Hincl01 [Hpres01 Hct01]]]]]].
        assert (Henv1 : env_well_typed Σ rho0 s1 iface)
          by (eapply valuetyp_storage_weak_env; eauto).
        assert (Hloc1 : loc_has_opt_type Σ l0 s1 oid)
          by (eapply loc_has_opt_type_weak; eauto).
        destruct (IHfa s1 rho0 l0 Henv1 Hloc1)
          as [vs [sf [Hevs [Htvs [Hincl1f [Hpres1f Hct1f]]]]]].
        exists (v0 :: vs), sf. refine (conj _ (conj _ (conj _ (conj _ _)))).
        + eapply E_SlotListCons; eauto.
        + constructor.
          * apply slot_abi_inv. apply Hpres1f. exact Htv0.
          * exact Htvs.
        + intros l' ls' Hl'. apply Hincl1f. apply Hincl01. exact Hl'.
        + intros v' st' Hv'. apply Hpres1f. apply Hpres01. exact Hv'.
        + eapply creates_typed_trans; eauto. }
    destruct (Hse_eval s rho l Henv Hloc)
      as [vals [s_final [Hevl [Htvals [Hincl_sf [Hpres_sf Hct_sf]]]]]].
    assert (Henv_sf : env_well_typed Σ rho s_final iface)
      by (eapply valuetyp_storage_weak_env; eauto).
    assert (Hloc_sf : loc_has_opt_type Σ l s_final oid)
      by (eapply loc_has_opt_type_weak; eauto).
    destruct (IHHtyp Hctors Hswt s_final rho l Henv_sf Hloc_sf)
      as [sv [s_v [Hev_sv [Htv_sv [Hincl_sv [Hpres_sv Hct_sv]]]]]].
    set (rho' := build_ctor_env (ctor_iface ctor) vals l (env_origin rho) sv).
    assert (Hiffs : Forall (fun pre =>
      eval_expr (TSUntimed s_v) rho' pre dummy_loc (VBool true))
      (ctor_iff ctor)).
    { match goal with
      | [HP4 : forall _ _ _ _ _ _ _, env_well_typed _ _ _ _ -> _ |- _] =>
        exact (HP4 s rho l vals s_final sv s_v Henv Hloc Hevl Hev_sv)
      | _ => exact (H4 s rho l vals s_final sv s_v Henv Hloc Hevl Hev_sv)
      end. }
    assert (Henv_rho' : env_well_typed Σ rho' s_v (ctor_iface ctor)).
    { apply build_ctor_env_well_typed.
      - eapply Forall2_impl; [|exact Htvals]. intros v0 alpha0 Hv0. apply slot_abi_inv. apply Hpres_sv. constructor. exact Hv0.
      - destruct Henv as [_ [_ [_ [[vo [Hvo Htvo]] _]]]].
        unfold env_origin. rewrite Hvo. exact Htvo.
      - apply slot_abi_inv in Htv_sv. inv Htv_sv. assumption.
      - exact (proj1 (ctor_iface_wf Σ a ctor Hswt Hcl)).
      - exact (proj1 (proj2 (ctor_iface_wf Σ a ctor Hswt Hcl))).
      - exact (proj2 (proj2 (ctor_iface_wf Σ a ctor Hswt Hcl))). }
    destruct (Hctors a ctor Hcl s_v rho' Henv_rho' Hiffs)
      as [l' [s' [Heval_cc [Htloc [Hincl_s' [Hpres_s' Hct_s']]]]]].
    exists (VAddr l'), s'. split; [|split; [|split; [|split]]].
    { eapply E_CreatePayable; eauto. }
    { exact Htloc. }
    { intros l0 ls0 Hl0. apply Hincl_s'. apply Hincl_sv. apply Hincl_sf. exact Hl0. }
    { intros v' st' Hv'. apply Hpres_s'. apply Hpres_sv. apply Hpres_sf. exact Hv'. }
    { eapply creates_typed_trans; [|eapply creates_typed_trans|]; eauto. }
Qed.

(** Helper: Forall2 with matching keys implies alist_dom correspondence *)
Lemma forall2_alist_dom_fwd :
  forall A B (xs : list (ident * A)) (ys : list (ident * B)),
    Forall2 (fun p q => fst p = fst q) xs ys ->
    forall x, alist_dom xs x -> alist_dom ys x.
Proof.
  intros A B xs ys Hfa.
  induction Hfa as [| [kx vx] [ky vy] xs' ys' Heq _ IH]; intros x [v Hv].
  - discriminate.
  - simpl in Heq. subst ky. simpl in Hv.
    destruct (String.eqb_spec kx x).
    + exists vy. simpl. subst. rewrite String.eqb_refl. auto.
    + destruct (IH x) as [w Hw]; [exists v; exact Hv |].
      exists w. simpl. destruct (String.eqb_spec kx x); [contradiction | exact Hw].
Qed.

Lemma forall2_alist_dom_bwd :
  forall A B (xs : list (ident * A)) (ys : list (ident * B)),
    Forall2 (fun p q => fst p = fst q) xs ys ->
    forall x, alist_dom ys x -> alist_dom xs x.
Proof.
  intros A B xs ys Hfa.
  induction Hfa as [| [kx vx] [ky vy] xs' ys' Heq _ IH]; intros x [v Hv].
  - discriminate.
  - simpl in Heq. subst ky. simpl in Hv.
    destruct (String.eqb_spec kx x).
    + exists vx. simpl. subst. rewrite String.eqb_refl. auto.
    + destruct (IH x) as [w Hw]; [exists v; exact Hv |].
      exists w. simpl. destruct (String.eqb_spec kx x); [contradiction | exact Hw].
Qed.

(** Helper: parallel Forall2 implies parallel alist_lookup with typing *)
Lemma forall2_alist_lookup_typed :
  forall A B (R : A -> B -> Prop) (xs : list (ident * A)) (ys : list (ident * B)),
    Forall2 (fun p q => fst p = fst q /\ R (snd p) (snd q)) xs ys ->
    forall x a, alist_lookup xs x = Some a ->
    exists b, alist_lookup ys x = Some b /\ R a b.
Proof.
  intros A B R xs ys Hfa.
  induction Hfa as [| [kx vx] [ky vy] xs' ys' [Heq HR] _ IH]; intros x a Ha.
  - discriminate.
  - simpl in Heq. subst ky. simpl in Ha.
    destruct (String.eqb_spec kx x).
    + inv Ha. exists vy. simpl. subst. rewrite String.eqb_refl. auto.
    + destruct (IH x a Ha) as [b [Hb HRab]].
      exists b. simpl. destruct (String.eqb_spec kx x); [contradiction | auto].
Qed.

(** Helper: evaluate a list of creates *)
Lemma creates_list_eval :
  forall Σ creates iface,
    ctor_eval_prop Σ ->
    Σ_well_typed Σ ->
    Forall (fun c : create => type_slotexpr Σ iface ONone (snd c) (fst (fst c))) creates ->
    forall s rho,
      env_well_typed Σ rho s iface ->
      exists s_n bindings,
        eval_create_list (Σ_cnstr Σ) s rho creates dummy_loc s_n bindings /\
        Forall2 (fun (b : ident * value) (c : create) =>
          fst b = snd (fst c) /\ has_slot_type Σ (snd b) s_n (fst (fst c)))
          bindings creates /\
        state_incl s s_n /\
        (forall v st, has_slot_type Σ v s st -> has_slot_type Σ v s_n st) /\
        creates_typed Σ s s_n.
Proof.
  intros Σ creates iface Hctors Hswt Hfa.
  induction Hfa as [| c creates' Hse _ IH]; intros s rho Henv.
  - exists s, []. refine (conj _ (conj _ (conj _ (conj _ _)))).
    + constructor.
    + constructor.
    + intros l ls Hl; exact Hl.
    + auto.
    + apply creates_typed_refl.
  - destruct c as [[st x] se]. simpl in Hse.
    destruct (se_typesafety_with_ctors Σ iface ONone se st Hctors Hswt Hse s rho dummy_loc Henv I)
      as [v [s1 [Hev [Htv [Hincl1 [Hpres1 Hct1]]]]]].
    assert (Henv1 : env_well_typed Σ rho s1 iface)
      by (eapply valuetyp_storage_weak_env; eauto).
    destruct (IH s1 rho Henv1) as [s_n [bs [Hevs [Hbs [Hincln [Hpresn Hctn]]]]]].
    exists s_n, ((x, v) :: bs). refine (conj _ (conj _ (conj _ (conj _ _)))).
    + eapply E_CreateListCons; eauto.
    + constructor.
      * simpl. split; [reflexivity | apply Hpresn; exact Htv].
      * exact Hbs.
    + intros l ls Hl. apply Hincln. apply Hincl1. exact Hl.
    + intros v' st' Hv'. apply Hpresn. apply Hpres1. exact Hv'.
    + eapply creates_typed_trans; eauto.
Qed.

(** The key lemma: all constructors evaluate.
    Proved by strong induction on Σ_cnstr_size.
    Inside the induction, we use [se_typesafety_with_ctors] with the
    IH providing [ctor_eval_prop] for the sub-contract_env. *)
Lemma all_ctors_evaluate :
  forall Σ,
    Σ_wf Σ ->
    Σ_well_typed Σ ->
    ctor_eval_prop Σ.
Proof.
  intro Σ.
  remember (Σ_cnstr_size Σ) as n.
  revert Σ Heqn.
  induction n as [n IHn] using lt_wf_ind.
  intros Σ Hn Hwf Hwt.
  unfold ctor_eval_prop.
  intros a ctor Hcl s rho Henv Hiffs.
  (* From Σ_well_typed, get Σ' where constructor is typed *)
  assert (Hwt_copy := Hwt).
  destruct Hwt as [? Hswf0 Hswt_c Hswt_t].
  destruct (Hswt_c a ctor Hcl) as [Σ' [layout [Hincl [Hfresh [Hsize [Hwt' [Htc Hsto]]]]]]].
  assert (Hwf' : Σ_wf Σ') by (eapply Σ_wf_incl; eauto).
  assert (Hctors' : ctor_eval_prop Σ') by (eapply IHn; eauto; lia).
  (* Extract premises from type_constructor *)
  assert (Hiwf : interface_wf Σ' (ctor_iface ctor)) by (inversion Htc; assumption).
  assert (Hcreates_ty : Forall (fun cc => type_creates Σ' (ctor_iface ctor) (OSome a) (snd cc) layout)
    (ctor_cases ctor)) by (inversion Htc; assumption).
  assert (Hcc : forall s0 rho0,
    Forall (fun pre => eval_expr (TSUntimed s0) rho0 pre dummy_loc (VBool true))
           (ctor_iff ctor) ->
    exists j, j < length (ctor_cases ctor) /\
      eval_expr (TSUntimed s0) rho0 (fst (nth j (ctor_cases ctor) (EBool false, []))) dummy_loc (VBool true) /\
      forall i, i <> j -> i < length (ctor_cases ctor) ->
        eval_expr (TSUntimed s0) rho0 (fst (nth i (ctor_cases ctor) (EBool false, []))) dummy_loc (VBool false))
    by (inversion Htc; assumption).
  (* Transfer env from Σ to Σ' *)
  assert (Henv' : env_well_typed Σ' rho s (ctor_iface ctor)).
  { eapply env_well_typed_Σ_down; eauto. }
  (* Case consistency gives active case j *)
  destruct (Hcc s rho Hiffs) as [j [Hj [Hcond_j Hcond_others]]].
  set (case_j := nth j (ctor_cases ctor) (EBool false, [])) in *.
  (* Get creates typing for case j *)
  assert (Hcreates_j_ty : type_creates Σ' (ctor_iface ctor) (OSome a) (snd case_j) layout)
    by (eapply Forall_nth; eauto).
  inversion Hcreates_j_ty as [? ? ? ? ? Hlayout_eq Hbal Hswf_creates Hse_types].
  (* Evaluate creates in Σ' *)
  destruct (creates_list_eval Σ' (snd case_j) (ctor_iface ctor) Hctors' Hwt' Hse_types s rho Henv')
    as [s_n [bindings [Heval_cl [Hfa2 [Hincl_n [Hpres_n Hct_n]]]]]].
  (* Lift to Σ_cnstr Σ via cmap mono *)
  assert (Heval_cl_Σ : eval_create_list (Σ_cnstr Σ) s rho (snd case_j) dummy_loc s_n bindings).
  { eapply (proj2 (proj2 (proj2 (proj2 (cmap_mono_slotexpr_combined _))))); eauto.
    exact (proj1 (proj2 Hincl)). }
  set (l := state_next s_n).
  set (s' := state_alloc s_n a (list_to_map bindings)).
  (* Factor out Forall2 facts *)
  assert (Hfa_keys : Forall2 (fun b p => fst b = fst p) bindings layout).
  { rewrite Hlayout_eq. clear - Hfa2.
    induction Hfa2 as [| [x0 v0] [[st0 nm0] se0] bs cs [Heq _] _ IH].
    - constructor.
    - constructor; [exact Heq | exact IH]. }
  assert (Hfa_typed : Forall2 (fun b p => fst b = fst p /\ has_slot_type Σ' (snd b) s_n (snd p))
                               bindings layout).
  { rewrite Hlayout_eq. clear - Hfa2.
    induction Hfa2 as [| [x0 v0] [[st0 nm0] se0] bs cs [Heq Hty] _ IH].
    - constructor.
    - constructor; [split; [exact Heq | exact Hty] | exact IH]. }
  (* Factor out the has_slot_type proof for the new location *)
  assert (Hloc_typed : has_slot_type Σ (VAddr l) s' (SContract a)).
  { constructor. constructor.
    - exists (mk_loc_store a (list_to_map bindings)).
      unfold s', l. rewrite state_alloc_self. reflexivity.
    - exists layout. exact Hsto.
    - unfold state_type, s', l. rewrite state_alloc_self. reflexivity.
    - intro x. split.
      + intros [v Hv].
        unfold state_var, s', l in Hv. rewrite state_alloc_self in Hv. simpl in Hv.
        destruct (forall2_alist_dom_fwd _ _ bindings layout Hfa_keys x (ex_intro _ v Hv))
          as [st Hst].
        exists st. unfold Σ_storage_var. rewrite Hsto. exact Hst.
      + intros [st Hst].
        unfold Σ_storage_var in Hst. rewrite Hsto in Hst.
        destruct (forall2_alist_dom_bwd _ _ bindings layout Hfa_keys x (ex_intro _ st Hst))
          as [v Hv].
        exists v. unfold state_var, s', l. rewrite state_alloc_self. simpl. exact Hv.
    - intros x st Hssv.
      unfold Σ_storage_var in Hssv. rewrite Hsto in Hssv.
      assert (Hdom_l : alist_dom layout x) by (exists st; exact Hssv).
      destruct (forall2_alist_dom_bwd _ _ bindings layout Hfa_keys x Hdom_l) as [v Hv].
      destruct (@forall2_alist_lookup_typed value slot_type
        (fun v0 st0 => has_slot_type Σ' v0 s_n st0) bindings layout Hfa_typed x v Hv)
        as [st' [Hst' Htv']].
      assert (Hst_eq : st' = st) by congruence. subst st'.
      unfold state_var_force, state_var, s', l. rewrite state_alloc_self. simpl.
      unfold list_to_map. rewrite Hv.
      eapply valuetyp_storage_weak_slot; [apply state_incl_alloc |].
      eapply valuetyp_storetyp_weak_slot; [exact Hincl | exact Htv']. }
  exists l, s'. refine (conj _ (conj _ (conj _ (conj _ _)))).
  { econstructor; eauto. econstructor; eauto. }
  { exact Hloc_typed. }
  { intros l0 ls0 Hl0. unfold s'.
    apply (state_incl_alloc s_n a (list_to_map bindings)).
    apply Hincl_n. exact Hl0. }
  { intros v' st' Hv'.
    eapply valuetyp_storage_weak_slot; [apply state_incl_alloc |].
    eapply valuetyp_storage_weak_slot; [exact Hincl_n | exact Hv']. }
  { (* creates_typed Σ s s' *)
    assert (Hct_n_Σ : creates_typed Σ s s_n)
      by (eapply creates_typed_Σ_up; eauto).
    intros l0 Hdom0. unfold s' in Hdom0.
    destruct Hdom0 as [ls0 Hls0].
    rewrite state_alloc_store in Hls0.
    destruct (Nat.eqb_spec (state_next s_n) l0).
    - subst l0. right. exists a. exact Hloc_typed.
    - assert (Hdom_sn : state_dom s_n l0) by (exists ls0; exact Hls0).
      destruct (Hct_n_Σ l0 Hdom_sn) as [Hdom_s | [a0 Ha0]].
      + left. exact Hdom_s.
      + right. exists a0.
        eapply valuetyp_storage_weak_slot; [apply state_incl_alloc | exact Ha0]. }
Qed.

(* ================================================================= *)
(** ** Slot Expression Type Safety (Lemma 6.7) *)

Lemma se_typesafety :
  forall Σ iface oid se sty,
    Σ_wf Σ ->
    Σ_well_typed Σ ->
    type_slotexpr Σ iface oid se sty ->
    forall s rho l,
      env_well_typed Σ rho s iface ->
      loc_has_opt_type Σ l s oid ->
      exists v s',
        eval_slotexpr (Σ_cnstr Σ) s rho se l v s' /\
        has_slot_type Σ v s' sty /\
        state_incl s s' /\
        (forall v' st', has_slot_type Σ v' s st' -> has_slot_type Σ v' s' st') /\
        creates_typed Σ s s'.
Proof.
  intros Σ iface oid se sty Hwf Hwt Htyp.
  exact (se_typesafety_with_ctors Σ iface oid se sty
           (all_ctors_evaluate Σ Hwf Hwt) Hwt Htyp).
Qed.

(* ================================================================= *)
(** ** Update Type Safety (Lemma 6.9) *)

Lemma ref_storage_insert :
  forall Σ iface a r sty s rho l,
    Σ_wf Σ ->
    type_ref Σ iface TagS (OSome a) TagU r sty ->
    env_well_typed Σ rho s iface ->
    has_slot_type Σ (VAddr l) s (SContract a) ->
    forall v,
      has_slot_type Σ v s sty ->
      exists s',
        eval_insert s rho r v l s' /\
        has_slot_type Σ (VAddr l) s' (SContract a) /\
        (forall l', state_dom s l' -> state_dom s' l') /\
        (forall v' st, has_slot_type Σ v' s st -> has_slot_type Σ v' s' st).
Proof.
  intros Σ iface a r sty s rho l Hwf Href Henv Hloc v Hv.
  remember TagS as k eqn:Hk. remember (OSome a) as oid eqn:Hoid.
  remember TagU as t eqn:Ht.
  induction Href; try discriminate.
  - (* T_Storage: r = RVar x *)
    inv Hk. inv Hoid. inv Ht.
    assert (Hssv : Σ_storage_var Σ a x = Some sty)
      by (unfold Σ_storage_var; rewrite H; exact H0).
    assert (Hvd : state_var_dom s l x).
    { inversion Hloc; subst.
      match goal with [Habi : has_abi_type _ _ _ _ |- _] => inversion Habi; subst end.
      match goal with [Hdom : forall x0, state_var_dom _ _ x0 <-> _ |- _] =>
        apply Hdom; eexists; eauto end. }
    exists (state_update_var s l x v).
    refine (conj _ (conj _ (conj _ _))).
    { constructor. exact Hvd. }
    { eapply update_preserves_typing; eauto. }
    { intros l' Hl'. apply state_update_var_dom. exact Hl'. }
    { intros v' st Hv'. eapply update_preserves_typing; eauto. }
  - (* T_Field: r = RField r0 x *)
    subst k. subst oid. subst t.
    destruct (ref_typesafety_untimed _ _ _ _ _ _ _ _ _ Href Henv Hloc)
      as [vr [Hevr Htvr]].
    assert (Htvr_copy := Htvr).
    inv Htvr. match goal with [Habi : has_abi_type _ _ _ _ |- _] => inv Habi end.
    rename l0 into l'.
    match goal with
    | [Hdom : forall x0, state_var_dom _ _ x0 <-> _,
       Hsto : Σ_storage_var _ _ _ = Some _ |- _] =>
      destruct (Hdom x) as [_ Hdom_bwd];
      assert (Hvd : state_var_dom s l' x) by (apply Hdom_bwd; eexists; eauto)
    end.
    exists (state_update_var s l' x v).
    refine (conj _ (conj _ (conj _ _))).
    { eapply E_InsField; eauto. }
    { eapply update_preserves_typing; eauto. }
    { intros l0 Hl0. apply state_update_var_dom. exact Hl0. }
    { intros v' st Hv'. eapply update_preserves_typing; eauto. }
Qed.

Lemma update_exprs_typesafety :
  forall Σ iface a upds s rho l,
    Σ_wf Σ ->
    Σ_well_typed Σ ->
    Forall (fun u => type_update Σ iface (OSome a) u) upds ->
    env_well_typed Σ rho s iface ->
    has_slot_type Σ (VAddr l) s (SContract a) ->
    exists vals s_n,
      eval_update_exprs (Σ_cnstr Σ) s rho upds l vals s_n /\
      Forall2 (fun v u =>
        exists sty,
          type_ref Σ iface TagS (OSome a) TagU (fst u) sty /\
          has_slot_type Σ v s_n sty) vals upds /\
      state_incl s s_n /\
      env_well_typed Σ rho s_n iface /\
      has_slot_type Σ (VAddr l) s_n (SContract a) /\
      (forall v st, has_slot_type Σ v s st -> has_slot_type Σ v s_n st) /\
      creates_typed Σ s s_n.
Proof.
  intros Σ iface a upds. intros s rho l Hwf Hwt Hfa.
  revert s rho l.
  induction Hfa as [|u upds' Hupd _ IH]; intros s rho l Henv Hloc.
  - exists [], s.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    + constructor.
    + constructor.
    + intros l' ls' Hl'; exact Hl'.
    + exact Henv.
    + exact Hloc.
    + auto.
    + apply creates_typed_refl.
  - destruct u as [r0 se0].
    inversion Hupd as [? ? ? ? ? st Href Hse]; subst.
    destruct (se_typesafety _ _ _ _ _ Hwf Hwt Hse s rho l Henv Hloc)
      as [v [s1 [Hev [Htv [Hincl1 [Hpres1 Hct1]]]]]].
    destruct (IH s1 rho l
      (valuetyp_storage_weak_env _ _ _ _ _ Hincl1 Henv)
      (Hpres1 _ _ Hloc))
      as [vs [sn [Hevs [Htvs [Hincln [Henvn [Hlocn [Hpresn Hctn]]]]]]]].
    exists (v :: vs), sn.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    + eapply E_UpdExprsCons; eauto.
    + constructor.
      { exists st. split; [exact Href | apply Hpresn; exact Htv]. }
      { exact Htvs. }
    + intros l' ls' Hl'. apply Hincln. apply Hincl1. exact Hl'.
    + exact Henvn.
    + exact Hlocn.
    + intros v' st' Hv'. apply Hpresn. apply Hpres1. exact Hv'.
    + eapply creates_typed_trans; eauto.
Qed.

Lemma update_inserts_typesafety :
  forall Σ iface a upds vals s rho l,
    Σ_wf Σ ->
    Forall2 (fun v u =>
      exists sty,
        type_ref Σ iface TagS (OSome a) TagU (fst u) sty /\
        has_slot_type Σ v s sty) vals upds ->
    env_well_typed Σ rho s iface ->
    has_slot_type Σ (VAddr l) s (SContract a) ->
    exists s',
      eval_update_inserts s rho upds vals l s' /\
      has_slot_type Σ (VAddr l) s' (SContract a) /\
      (forall l', state_dom s l' -> state_dom s' l') /\
      (forall v st, has_slot_type Σ v s st -> has_slot_type Σ v s' st).
Proof.
  intros Σ iface a upds vals.
  revert upds.
  induction vals as [|v vs IH]; intros [|[r se] upds'] s rho l Hwf Hfa Henv Hloc;
    try (inv Hfa; fail).
  - exists s. refine (conj _ (conj _ (conj _ _))); auto. constructor.
  - inv Hfa.
    destruct H2 as [sty [Href Htv]]. simpl in Href.
    destruct (ref_storage_insert _ _ _ _ _ _ _ _ Hwf Href Henv Hloc v Htv)
      as [s1 [Hins [Hloc1 [Hdom1 Hpres1]]]].
    assert (Henv1 : env_well_typed Σ rho s1 iface)
      by (eapply env_well_typed_pres; eauto).
    assert (Hvals1 : Forall2 (fun v0 u =>
      exists st, type_ref Σ iface TagS (OSome a) TagU (fst u) st /\
                 has_slot_type Σ v0 s1 st) vs upds').
    { eapply Forall2_impl; [|exact H4].
      intros v0 u0 [st0 [Hr0 Ht0]]. eexists; eauto. }
    destruct (IH upds' s1 rho l Hwf Hvals1 Henv1 Hloc1)
      as [s' [Hinserts [Hloc' [Hdom' Hpres']]]].
    exists s'. refine (conj _ (conj _ (conj _ _))).
    + econstructor; eauto.
    + exact Hloc'.
    + intros l0 Hl0. apply Hdom'. apply Hdom1. exact Hl0.
    + intros v' st' Hv'. apply Hpres'. apply Hpres1. exact Hv'.
Qed.

Lemma update_typesafety :
  forall Σ iface a upds s rho l,
    Σ_wf Σ ->
    Σ_well_typed Σ ->
    type_updates Σ iface (OSome a) upds ->
    env_well_typed Σ rho s iface ->
    has_slot_type Σ (VAddr l) s (SContract a) ->
    exists s',
      eval_updates (Σ_cnstr Σ) s rho upds l s' /\
      has_slot_type Σ (VAddr l) s' (SContract a) /\
      (forall l', state_dom s l' -> state_dom s' l') /\
      (forall v st, has_slot_type Σ v s st -> has_slot_type Σ v s' st) /\
      creates_typed Σ s s'.
Proof.
  intros Σ iface a upds s rho l Hwf Hwt Htyp Henv Hloc.
  inv Htyp.
  destruct (update_exprs_typesafety _ _ _ _ _ _ _ Hwf Hwt H Henv Hloc)
    as [vals [s_n [Hevs [Htvs [Hincl_n [Henv_n [Hloc_n [Hpres_n Hct_n]]]]]]]].
  destruct (update_inserts_typesafety _ _ _ _ _ _ _ _ Hwf Htvs Henv_n Hloc_n)
    as [s' [Hins [Hloc' [Hdom' Hpres']]]].
  exists s'. refine (conj _ (conj _ (conj _ (conj _ _)))).
  - econstructor; eauto.
  - exact Hloc'.
  - intros l0 Hl0. apply Hdom'. eapply state_incl_dom; eauto.
  - intros v st Hv. apply Hpres'. apply Hpres_n. exact Hv.
  - (* creates_typed: compose update_exprs (creates) with update_inserts (no new locations) *)
    intros l0 Hdom0.
    assert (Hdom0_n : state_dom s_n l0).
    { eapply eval_update_inserts_dom_back; eauto. }
    destruct (Hct_n l0 Hdom0_n) as [Hds | [a0 Ha0]].
    + left. exact Hds.
    + right. exists a0. apply Hpres'. exact Ha0.
Qed.

(* ================================================================= *)
(** ** Constructor Type Safety (Lemma 6.10) *)

Lemma constructor_typesafety :
  forall Σ a ctor s rho,
    Σ_wf Σ ->
    Σ_well_typed Σ ->
    Σ_cnstr Σ a = Some ctor ->
    env_well_typed Σ rho s (ctor_iface ctor) ->
    Forall (fun pre => eval_expr (TSUntimed s) rho pre dummy_loc (VBool true))
           (ctor_iff ctor) ->
    exists l s',
      eval_constructor (Σ_cnstr Σ) s rho ctor a l s' /\
      has_slot_type Σ (VAddr l) s' (SContract a) /\
      state_incl s s' /\
      (forall v st, has_slot_type Σ v s st -> has_slot_type Σ v s' st) /\
      creates_typed Σ s s'.
Proof.
  intros Σ a ctor s rho Hwf Hwt Hcl Henv Hiffs.
  destruct (all_ctors_evaluate Σ Hwf Hwt a ctor Hcl s rho Henv Hiffs)
    as [l [s' [Heval [Htloc [Hincl [Hpres Hct]]]]]].
  exists l, s'. refine (conj _ (conj Htloc (conj Hincl (conj Hpres Hct)))).
  constructor; [exact Hiffs | exact Heval].
Qed.

(* ================================================================= *)
(** ** Transition Type Safety (Lemma 6.11) *)

Lemma transition_typesafety :
  forall Σ a tr s rho l,
    Σ_wf Σ ->
    Σ_well_typed Σ ->
    type_transition Σ a tr ->
    env_well_typed Σ rho s (trans_iface tr) ->
    has_slot_type Σ (VAddr l) s (SContract a) ->
    Forall (fun pre => eval_expr (TSUntimed s) rho pre l (VBool true))
           (trans_iff tr) ->
    exists v s',
      eval_transition (Σ_cnstr Σ) s rho tr l v s' /\
      (forall l', state_dom s l' -> state_dom s' l') /\
      (forall v' st, has_slot_type Σ v' s st -> has_slot_type Σ v' s' st) /\
      creates_typed Σ s s'.
Proof.
  intros Σ a tr s rho l Hwf Hwt Htyp Henv Hloc Hiffs.
  inv Htyp.
  (* Case consistency gives the active case index j *)
  destruct (H5 s rho l Henv Hloc Hiffs) as [j [Hj [Hcond_j Hcond_others]]].
  (* Evaluate updates for case j *)
  assert (Hupd_j : type_updates Σ (trans_iface tr) (OSome a)
    (tc_updates (nth j (trans_cases tr) tc_default))).
  { eapply Forall_nth; eauto. }
  destruct (update_typesafety _ _ _ _ _ _ _ Hwf Hwt Hupd_j Henv Hloc)
    as [s' [Heval_upd [Hloc' [Hdom' [Hpres' Hct']]]]].
  (* Evaluate return expression in timed state (s, s') *)
  assert (Hret_typed : type_expr Σ (trans_iface tr) (OSome a) TagT
    (tc_return (nth j (trans_cases tr) tc_default)) TAddress).
  { eapply Forall_nth; eauto. }
  assert (Henv' : env_well_typed Σ rho s' (trans_iface tr))
    by (eapply env_well_typed_pres; eauto).
  destruct (expr_typesafety_timed _ _ _ _ _ _ _ _ _ Hret_typed Henv Henv' Hloc Hloc')
    as [v [Hev_ret Htv_ret]].
  exists v, s'. split; [|split; [|split]].
  - constructor; auto. econstructor; eauto.
  - exact Hdom'.
  - exact Hpres'.
  - exact Hct'.
Qed.

(* ================================================================= *)
(** ** Well-formed State Transitions *)

(** Steps where each step includes env_well_typed *)
Definition wf_step_cnstr (Σ : contract_env) (a : ident) (s : state) (l : addr) (s' : state) : Prop :=
  exists rho ctor,
    Σ_cnstr Σ a = Some ctor /\
    env_well_typed Σ rho s (ctor_iface ctor) /\
    eval_constructor (Σ_cnstr Σ) s rho ctor a l s'.

Definition wf_step_trans (Σ : contract_env) (a : ident) (s : state) (l : addr) (s' : state) : Prop :=
  exists rho tr v transs,
    Σ_trans Σ a = Some transs /\
    In tr transs /\
    type_transition Σ a tr /\
    has_slot_type Σ (VAddr l) s (SContract a) /\
    env_well_typed Σ rho s (trans_iface tr) /\
    eval_transition (Σ_cnstr Σ) s rho tr l v s'.

Definition wf_step (Σ : contract_env) (s s' : state) : Prop :=
  (exists a l, wf_step_cnstr Σ a s l s') \/
  (exists a l, wf_step_trans Σ a s l s').

Inductive wf_steps (Σ : contract_env) : state -> state -> Prop :=
  | WF_Steps_refl : forall s, wf_steps Σ s s
  | WF_Steps_step : forall s1 s2 s3,
      wf_step Σ s1 s2 -> wf_steps Σ s2 s3 -> wf_steps Σ s1 s3.

Definition wf_possible (Σ : contract_env) (s : state) : Prop :=
  wf_steps Σ state_empty s.

(* ================================================================= *)
(** ** State Transition Type Safety (Lemma 6.12) *)

Lemma state_transition_typesafety :
  forall Σ s s',
    Σ_wf Σ ->
    Σ_well_typed Σ ->
    wf_steps Σ s s' ->
    (forall v st, has_slot_type Σ v s st -> has_slot_type Σ v s' st) /\
    (forall l, state_dom s l -> state_dom s' l).
Proof.
  intros Σ s s' Hwf Hwt Hsteps.
  induction Hsteps as [s0 | s1 s2 s3 Hstep Hrest IH].
  - split; auto.
  - destruct IH as [IHpres IHdom].
    destruct Hstep as [[a [l' Hcnstr]] | [a [l' Htrans]]].
    + (* Constructor step *)
      destruct Hcnstr as [rho [ctor [Hcl [Henv Heval]]]].
      inv Heval.
      destruct (all_ctors_evaluate Σ Hwf Hwt a ctor Hcl s1 rho Henv H)
        as [l2 [s2' [Heval2 [Hloc2 [Hincl2 [Hpres2 _]]]]]].
      assert (Hdet := ctor_cases_det
        (Σ_cnstr Σ) s1 rho (ctor_cases ctor) a l' s2 H0 l2 s2' Heval2).
      destruct Hdet as [-> ->].
      split.
      * intros v st Hv. apply IHpres. apply Hpres2. exact Hv.
      * intros l0 Hl0. apply IHdom. eapply state_incl_dom; eauto.
    + (* Transition step *)
      destruct Htrans as [rho [tr [v [transs [Htl [Hin [Httyp [Hloc [Henv Heval]]]]]]]]].
      destruct (transition_typesafety _ _ _ _ _ _ Hwf Hwt Httyp Henv Hloc)
        as [v' [s2' [Heval2 [Hdom2 [Hpres2 _]]]]].
      * inv Heval. exact H.
      * assert (Hdet := transition_determinism
          (Σ_cnstr Σ) s1 rho tr l' v s2 v' s2' Heval Heval2).
        destruct Hdet as [-> ->].
        split.
        -- intros w st Hw. apply IHpres. apply Hpres2. exact Hw.
        -- intros l0 Hl0. apply IHdom. apply Hdom2. exact Hl0.
Qed.

(* ================================================================= *)
(** ** Reachable Store is Well-typed (Lemma 6.13) *)

Lemma store_wt_aux :
  forall Σ s s',
    Σ_wf Σ ->
    Σ_well_typed Σ ->
    wf_steps Σ s s' ->
    (forall l, state_dom s l -> exists a, has_slot_type Σ (VAddr l) s (SContract a)) ->
    forall l, state_dom s' l -> exists a, has_slot_type Σ (VAddr l) s' (SContract a).
Proof.
  intros Σ s s' Hwf Hwt Hsteps.
  induction Hsteps as [s0 | s1 s2 s3 Hstep Hrest IH]; intros Hall l Hdom.
  - exact (Hall l Hdom).
  - apply IH; [|exact Hdom]. clear IH Hrest s3 l Hdom.
    intros l Hdom2.
    destruct Hstep as [[a [l' Hcnstr]] | [a [l' Htrans]]].
    + (* Constructor step *)
      destruct Hcnstr as [rho [ctor [Hcl [Henv Heval]]]].
      inv Heval.
      destruct (all_ctors_evaluate Σ Hwf Hwt a ctor Hcl s1 rho Henv H)
        as [l2 [s2' [Heval2 [Hloc2 [Hincl2 [Hpres2 Hct2]]]]]].
      assert (Hdet := ctor_cases_det
        (Σ_cnstr Σ) s1 rho (ctor_cases ctor) a l' s2 H0 l2 s2' Heval2).
      destruct Hdet as [-> ->].
      destruct (Hct2 l Hdom2) as [Hds1 | [a0 Ha0]].
      * destruct (Hall l Hds1) as [a0 Ha0]. exists a0. apply Hpres2. exact Ha0.
      * exists a0. exact Ha0.
    + (* Transition step *)
      destruct Htrans as [rho [tr [v [transs [Htl [Hin [Httyp [Hloc [Henv Heval]]]]]]]]].
      destruct (transition_typesafety _ _ _ _ _ _ Hwf Hwt Httyp Henv Hloc)
        as [v' [s2' [Heval2 [Hdom2' [Hpres2 Hct2]]]]].
      { inv Heval. exact H. }
      assert (Hdet := transition_determinism
          (Σ_cnstr Σ) s1 rho tr l' v s2 v' s2' Heval Heval2).
      destruct Hdet as [-> ->].
      destruct (Hct2 l Hdom2) as [Hds1 | [a0 Ha0]].
      * destruct (Hall l Hds1) as [a0 Ha0]. exists a0. apply Hpres2. exact Ha0.
      * exists a0. exact Ha0.
Qed.

Lemma store_wt :
  forall Σ s l,
    Σ_wf Σ ->
    Σ_well_typed Σ ->
    wf_possible Σ s ->
    state_dom s l ->
    exists a, has_slot_type Σ (VAddr l) s (SContract a).
Proof.
  intros Σ s l Hwf Hwt Hposs Hdom.
  eapply store_wt_aux; eauto.
  intros l0 [ls0 Hls0].
  exfalso. simpl in Hls0. discriminate.
Qed.
