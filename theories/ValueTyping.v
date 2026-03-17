(** * Value Typing, Environment Typing, Entailment, Well-typed Σ,
      Well-foundedness, and Helper Lemmas
    Formalizes Sections 3-5 of the tech report. *)

From Stdlib Require Import String ZArith List Bool PeanoNat Lia.
From Act Require Import Maps Syntax Domains Semantics.
Import ListNotations.

(* ================================================================= *)
(** ** Value Typing: ⊢ v : β *)

Inductive has_base_type : value -> base_type -> Prop :=
  (** V-Addr *)
  | V_Addr : forall (a : addr),
      has_base_type (VAddr a) TAddress
  (** V-Bool *)
  | V_Bool : forall (b : bool),
      has_base_type (VBool b) TBool
  (** V-Int *)
  | V_Int : forall (n : Z) (it : int_type),
      in_range it n ->
      has_base_type (VInt n) (TInt it).

(* ================================================================= *)
(** ** Value Typing: ⊢ v : μ *)

Inductive has_mapping_type : value -> mapping_type -> Prop :=
  (** V-BaseValMu *)
  | V_BaseValMu : forall v bt,
      has_base_type v bt ->
      has_mapping_type v (MBase bt)
  (** V-Mapping with Z keys *)
  | V_MappingZ : forall f it mu,
      (forall n, has_base_type (VInt n) (TInt it) ->
                 has_mapping_type (f n) mu) ->
      has_mapping_type (VMapZ f) (MMapping (TInt it) mu)
  (** V-Mapping with bool keys *)
  | V_MappingB : forall f mu,
      (forall b, has_mapping_type (f b) mu) ->
      has_mapping_type (VMapB f) (MMapping TBool mu)
  (** V-Mapping with address keys *)
  | V_MappingA : forall f mu,
      (forall a, has_mapping_type (f a) mu) ->
      has_mapping_type (VMapA f) (MMapping TAddress mu).

(* ================================================================= *)
(** ** Value Typing: Σ ⊢ v :_s α  and  Σ ⊢ v :_s σ *)

Inductive has_abi_type : contract_env -> value -> state -> abi_type -> Prop :=
  (** V-BaseValAlpha *)
  | V_BaseValAlpha : forall Σ v s bt,
      has_base_type v bt ->
      has_abi_type Σ v s (ABase bt)
  (** V-AddrIsContract *)
  | V_AddrIsContract : forall Σ s (l : addr) (a : ident),
      state_dom s l ->
      dom (Σ_storage Σ) a ->
      state_type s l = Some a ->
      (forall x, state_var_dom s l x <->
                 exists st, Σ_storage_var Σ a x = Some st) ->
      (forall x st, Σ_storage_var Σ a x = Some st ->
                    has_slot_type Σ (state_var_force s l x) s st) ->
      has_abi_type Σ (VAddr l) s (AContractAddr a)

with has_slot_type : contract_env -> value -> state -> slot_type -> Prop :=
  (** V-MappingVal *)
  | V_MappingVal : forall Σ v s mu,
      has_mapping_type v mu ->
      has_slot_type Σ v s (SMapping mu)
  (** V-ABIVal *)
  | V_ABIVal : forall Σ v s alpha,
      has_abi_type Σ v s alpha ->
      has_slot_type Σ v s (SAbi alpha)
  (** V-Contract *)
  | V_Contract : forall Σ (l : addr) s (a : ident),
      has_abi_type Σ (VAddr l) s (AContractAddr a) ->
      has_slot_type Σ (VAddr l) s (SContract a).

(** Mutual induction schemes for has_abi_type / has_slot_type *)
Scheme has_abi_type_ind2 := Induction for has_abi_type Sort Prop
  with has_slot_type_ind2 := Induction for has_slot_type Sort Prop.
Combined Scheme has_abi_slot_mutind from has_abi_type_ind2, has_slot_type_ind2.

(* ================================================================= *)
(** ** Optional Slot Typing: Σ ⊢ v :_s ⊥?σ *)

Inductive has_opt_slot_type : contract_env -> value -> state -> opt_id -> Prop :=
  (** V-None: ⊥ accepts any value *)
  | V_None : forall Σ v s,
      has_opt_slot_type Σ v s ONone
  (** V-Some *)
  | V_Some : forall Σ v s a,
      has_slot_type Σ v s (SContract a) ->
      has_opt_slot_type Σ v s (OSome a).

(** Location typing shorthand: Σ ⊢ ℓ :_s ⊥?A *)
Definition loc_has_opt_type (Σ : contract_env) (l : addr) (s : state) (oid : opt_id) : Prop :=
  match oid with
  | ONone => True
  | OSome a => has_slot_type Σ (VAddr l) s (SContract a)
  end.

(* ================================================================= *)
(** ** Environment Typing: Σ ⊢ ρ :_s I *)

(** V-Env *)
Definition env_well_typed (Σ : contract_env) (rho : env) (s : state) (iface : interface) : Prop :=
  (** domain condition: dom(ρ) = dom(I) ∪ {caller, origin, callvalue} *)
  (forall x, dom rho x <->
    (alist_dom iface x \/
     x = "caller"%string \/
     x = "origin"%string \/
     x = "callvalue"%string)) /\
  (** interface variables are well-typed *)
  (forall x alpha, alist_lookup iface x = Some alpha ->
    exists v, rho x = Some v /\ has_abi_type Σ v s alpha) /\
  (** caller : address *)
  (exists vc, rho "caller"%string = Some vc /\ has_base_type vc TAddress) /\
  (** origin : address *)
  (exists vo, rho "origin"%string = Some vo /\ has_base_type vo TAddress) /\
  (** callvalue : uint256 *)
  (exists vcv, rho "callvalue"%string = Some vcv /\
               has_base_type vcv (TInt (UintT 256))).

(* ================================================================= *)
(** ** Semantic Entailment *)

(** Σ; I; Φ ⊨_{⊥?A} es — ValidExps *)
Definition semantic_entailment (Σ : contract_env) (iface : interface) (phi : list expr)
    (oid : opt_id) (es : list expr) : Prop :=
  forall s rho l,
    env_well_typed Σ rho s iface ->
    loc_has_opt_type Σ l s oid ->
    Forall (fun p => eval_expr (TSUntimed s) rho p l (VBool true)) phi ->
    Forall (fun e => eval_expr (TSUntimed s) rho e l (VBool true)) es.

(** Σ; I; Φ ⊨_{⊥?A} (ses, pres) — ValidIffs *)
Definition semantic_entailment_iffs (Σ : contract_env) (iface : interface) (phi : list expr)
    (oid : opt_id) (ses : list slot_expr) (pres : list expr) : Prop :=
  forall s0 rho l vs ss,
    env_well_typed Σ rho s0 iface ->
    loc_has_opt_type Σ l s0 oid ->
    Forall (fun p => eval_expr (TSUntimed s0) rho p l (VBool true)) phi ->
    length vs = length ses ->
    length ss = length ses ->
    (forall i, i < length ses ->
      eval_slotexpr (Σ_cnstr Σ) (nth i ss s0) rho (nth i ses (SEMap (MExp (EBool false)))) l
        (nth i vs (VInt 0%Z)) (nth (S i) ss s0)) ->
    let s_n := last ss s0 in
    let rho' := fold_right (fun '(x, v) r => Maps.update r x v)
                  empty
                  (combine (map fst (firstn (length ses) (ctor_iface (mk_ctor iface false [] [] [])))) vs) in
    Forall (fun e => eval_expr (TSUntimed s_n) rho' e dummy_loc (VBool true)) pres.

(* ================================================================= *)
(** ** Well-foundedness of contract dependency relation *)

(** B ≺_Σ A iff contract B is directly accessible from contract A's storage *)
Definition contract_dep (Σ : contract_env) (b a : ident) : Prop :=
  exists x, (Σ_storage_var Σ a x = Some (SContract b) \/
             Σ_storage_var Σ a x = Some (SAbi (AContractAddr b))).

(** Accessibility: standard well-founded accessibility *)
Definition Σ_accessible (Σ : contract_env) : ident -> Prop :=
  Acc (fun b a => contract_dep Σ b a).

(** WF(≺_Σ) = ∀ x. Acc x *)
Definition Σ_wf (Σ : contract_env) : Prop :=
  forall x, Σ_accessible Σ x.

(** Well-formedness of Σ: all storage references point to defined contracts *)
Definition Σ_storage_wf (Σ : contract_env) : Prop :=
  forall a b, contract_dep Σ b a -> dom (Σ_storage Σ) b.

(** contract_dep only depends on Σ_storage *)
Lemma contract_dep_storage_eq : forall Σ Σ' b a,
  Σ_storage Σ = Σ_storage Σ' ->
  contract_dep Σ b a -> contract_dep Σ' b a.
Proof.
  intros Σ Σ' b a Heq [x Hx].
  exists x. unfold Σ_storage_var in *. rewrite <- Heq. exact Hx.
Qed.

Lemma contract_dep_with_storage_neq : forall Σ a layout b c,
  c <> a ->
  contract_dep (Σ_with_storage Σ a layout) b c <-> contract_dep Σ b c.
Proof.
  intros Σ a layout b c Hne.
  split; intros [x Hx]; exists x; unfold Σ_storage_var in *;
    rewrite Σ_storage_with_storage in *; rewrite update_neq in * by auto;
    exact Hx.
Qed.

Lemma contract_dep_with_cnstr : forall Σ a ctor b c,
  contract_dep (Σ_with_cnstr Σ a ctor) b c <-> contract_dep Σ b c.
Proof.
  intros. split; intros [x Hx]; exists x; exact Hx.
Qed.

Lemma contract_dep_with_trans : forall Σ a transs b c,
  contract_dep (Σ_with_trans Σ a transs) b c <-> contract_dep Σ b c.
Proof.
  intros. split; intros [x Hx]; exists x; exact Hx.
Qed.

(* ================================================================= *)
(** ** len(Σ, A) — chain length *)

(** We define len abstractly — in proofs we use well-foundedness directly *)
Definition Σ_len (Σ : contract_env) (a : ident)
    (acc : Acc (fun b c => contract_dep Σ b c) a) : nat := 0.

(** len extended to slot types *)
Definition Σ_len_slot (Σ : contract_env) (st : slot_type) : nat :=
  match st with
  | SContract a => 0 (* placeholder *)
  | SAbi (AContractAddr a) => 0 (* placeholder *)
  | _ => 0
  end.

(** Σ_incl helpers *)
Lemma Σ_incl_refl : forall Σ, Σ_incl Σ Σ.
Proof.
  intro Σ. split; [|split]; apply includes_refl.
Qed.

Lemma Σ_incl_trans : forall sg1 sg2 sg3,
  Σ_incl sg1 sg2 -> Σ_incl sg2 sg3 -> Σ_incl sg1 sg3.
Proof.
  intros sg1 sg2 sg3 [Hs1 [Hc1 Ht1]] [Hs2 [Hc2 Ht2]].
  split; [|split]; eapply includes_trans; eauto.
Qed.

Lemma Σ_incl_storage : forall Σ Σ' a layout,
  Σ_incl Σ Σ' -> Σ_storage Σ a = Some layout ->
  Σ_storage Σ' a = Some layout.
Proof.
  intros Σ Σ' a layout [Hs _] H. apply Hs. exact H.
Qed.

Lemma Σ_incl_storage_var : forall Σ Σ' a x st,
  Σ_incl Σ Σ' ->
  Σ_storage_var Σ a x = Some st ->
  Σ_storage_var Σ' a x = Some st.
Proof.
  intros Σ Σ' a x st [Hs _] H.
  unfold Σ_storage_var in *.
  destruct (Σ_storage Σ a) eqn:E; [|discriminate].
  rewrite (Hs a s E). exact H.
Qed.

Lemma Σ_incl_storage_dom : forall Σ Σ',
  Σ_incl Σ Σ' ->
  forall a, dom (Σ_storage Σ) a -> dom (Σ_storage Σ') a.
Proof.
  intros Σ Σ' [Hs _] a [v Hv].
  exists v. apply Hs. exact Hv.
Qed.

Lemma Σ_incl_with_storage_fresh : forall Σ a layout,
  ~ dom (Σ_storage Σ) a ->
  Σ_incl Σ (Σ_with_storage Σ a layout).
Proof.
  intros Σ a layout Hfresh.
  split; [|split]; simpl.
  - apply includes_update_fresh. exact Hfresh.
  - apply includes_refl.
  - apply includes_refl.
Qed.

Lemma Σ_incl_with_cnstr_fresh : forall Σ a ctor,
  ~ dom (Σ_cnstr Σ) a ->
  Σ_incl Σ (Σ_with_cnstr Σ a ctor).
Proof.
  intros Σ a ctor Hfresh.
  split; [|split]; simpl.
  - apply includes_refl.
  - apply includes_update_fresh. exact Hfresh.
  - apply includes_refl.
Qed.

Lemma Σ_incl_with_trans_fresh : forall Σ a transs,
  ~ dom (Σ_trans Σ) a ->
  Σ_incl Σ (Σ_with_trans Σ a transs).
Proof.
  intros Σ a transs Hfresh.
  split; [|split]; simpl.
  - apply includes_refl.
  - apply includes_refl.
  - apply includes_update_fresh. exact Hfresh.
Qed.

Lemma Σ_incl_cnstr : forall Σ Σ' a ctor,
  Σ_incl Σ Σ' -> Σ_cnstr Σ a = Some ctor ->
  Σ_cnstr Σ' a = Some ctor.
Proof.
  intros Σ Σ' a ctor [_ [Hc _]] H. apply Hc. exact H.
Qed.

Lemma Σ_incl_trans_lookup : forall Σ Σ' a transs,
  Σ_incl Σ Σ' -> Σ_trans Σ a = Some transs ->
  Σ_trans Σ' a = Some transs.
Proof.
  intros Σ Σ' a transs [_ [_ Ht]] H. apply Ht. exact H.
Qed.

Lemma contract_dep_incl : forall Σ Σ' b a,
  Σ_incl Σ Σ' ->
  contract_dep Σ b a -> contract_dep Σ' b a.
Proof.
  intros Σ Σ' b a Hincl [x Hx].
  exists x. destruct Hx as [Hx|Hx]; [left|right];
    eapply Σ_incl_storage_var; eauto.
Qed.

Lemma Σ_wf_incl : forall Σ Σ',
  Σ_incl Σ Σ' -> Σ_wf Σ' -> Σ_wf Σ.
Proof.
  intros Σ Σ' Hincl Hwf x.
  induction (Hwf x) as [x _ IH].
  constructor. intros y Hd.
  apply IH. eapply contract_dep_incl; eauto.
Qed.

(* Well-formedness predicate for default value typing *)
Fixpoint default_value_typable (mu : mapping_type) : Prop :=
  match mu with
  | MBase (TInt it) => in_range it 0%Z
  | MBase _ => True
  | MMapping _ mu' => default_value_typable mu'
  end.

(* ================================================================= *)
(** ** Key Lemmas *)

(** Uniqueness of Contract Value Typing (Lemma 5.1) *)
Lemma uniqueness_of_value_typing :
  forall Σ l s a b,
    has_slot_type Σ (VAddr l) s (SContract a) ->
    has_slot_type Σ (VAddr l) s (SContract b) ->
    a = b.
Proof.
  intros Σ l s a b Ha Hb.
  inv Ha. inv Hb.
  match goal with
  | [H1 : has_abi_type _ _ _ (AContractAddr a),
     H2 : has_abi_type _ _ _ (AContractAddr b) |- _] =>
    inv H1; inv H2; congruence
  end.
Qed.

(** default(μ) has mapping type (Lemma 5.3)
    Note: requires well-formedness to ensure 0 is in range for all
    integer base types appearing in μ. The paper assumes standard
    Solidity types where this always holds. *)
Lemma default_has_mapping_type :
  forall mu, default_value_typable mu -> has_mapping_type (default_value mu) mu.
Proof.
  induction mu; simpl; intros Hwf.
  - (* MBase *)
    apply V_BaseValMu.
    destruct b; try constructor; auto.
  - (* MMapping *)
    destruct b; simpl.
    + (* TInt *) apply V_MappingZ. intros n _. apply IHmu. exact Hwf.
    + (* TBool *) apply V_MappingB. intros b. apply IHmu. exact Hwf.
    + (* TAddress *) apply V_MappingA. intros a. apply IHmu. exact Hwf.
Qed.

(** Weakening of Storage (Typing) — Lemma 5.4
    By mutual induction on the value typing derivation. *)
Lemma valuetyp_storage_weak :
  (forall Σ v s alpha,
    has_abi_type Σ v s alpha ->
    forall s', state_incl s s' -> has_abi_type Σ v s' alpha) /\
  (forall Σ v s st,
    has_slot_type Σ v s st ->
    forall s', state_incl s s' -> has_slot_type Σ v s' st).
Proof.
  apply has_abi_slot_mutind; intros.
  - (* V_BaseValAlpha *) constructor; auto.
  - (* V_AddrIsContract *)
    assert (Hdom : state_dom s l) by auto.
    econstructor; eauto.
    + eapply state_incl_dom; eauto.
    + eapply state_incl_type; eauto.
    + intro x0. rewrite <- (state_incl_var_dom s s' l x0); auto.
    + intros x0 st0 Hst0.
      rewrite (state_incl_var_force s s' l x0); auto.
  - (* V_MappingVal *) constructor; auto.
  - (* V_ABIVal *) constructor; auto.
  - (* V_Contract *) constructor; auto.
Qed.

Lemma valuetyp_storage_weak_abi :
  forall Σ v s s' alpha,
    state_incl s s' ->
    has_abi_type Σ v s alpha ->
    has_abi_type Σ v s' alpha.
Proof. intros. eapply (proj1 valuetyp_storage_weak); eauto. Qed.

Lemma valuetyp_storage_weak_slot :
  forall Σ v s s' st,
    state_incl s s' ->
    has_slot_type Σ v s st ->
    has_slot_type Σ v s' st.
Proof. intros. eapply (proj2 valuetyp_storage_weak); eauto. Qed.

Lemma valuetyp_storage_weak_env :
  forall Σ rho s s' iface,
    state_incl s s' ->
    env_well_typed Σ rho s iface ->
    env_well_typed Σ rho s' iface.
Proof.
  intros Σ rho s s' iface Hincl H.
  destruct H as (Hdom & Hvars & Hc & Ho & Hcv).
  split; [exact Hdom|].
  split; [|exact (conj Hc (conj Ho Hcv))].
  intros y al Hlook. destruct (Hvars y al Hlook) as [v [Hv Htyp]].
  exists v. split; [exact Hv|]. eapply valuetyp_storage_weak_abi; eauto.
Qed.

Lemma env_well_typed_pres :
  forall Σ rho s s' iface,
    (forall v st, has_slot_type Σ v s st -> has_slot_type Σ v s' st) ->
    env_well_typed Σ rho s iface ->
    env_well_typed Σ rho s' iface.
Proof.
  intros Σ rho s s' iface Hpres H.
  destruct H as (Hdom & Hvars & Hc & Ho & Hcv).
  split; [exact Hdom|].
  split; [|exact (conj Hc (conj Ho Hcv))].
  intros y al Hlook. destruct (Hvars y al Hlook) as [v [Hv Htyp]].
  exists v. split; [exact Hv|].
  assert (Hs := Hpres v (SAbi al) ltac:(constructor; exact Htyp)).
  inv Hs. assumption.
Qed.

(** Weakening of Store Typing — Lemma 5.6
    By mutual induction on the value typing derivation. *)
Lemma valuetyp_storetyp_weak :
  (forall Σ v s alpha,
    has_abi_type Σ v s alpha ->
    forall Σ', Σ_incl Σ Σ' -> has_abi_type Σ' v s alpha) /\
  (forall Σ v s st,
    has_slot_type Σ v s st ->
    forall Σ', Σ_incl Σ Σ' -> has_slot_type Σ' v s st).
Proof.
  apply has_abi_slot_mutind; intros.
  - (* V_BaseValAlpha *) constructor; auto.
  - (* V_AddrIsContract *)
    assert (Hssv : forall y, Σ_storage_var Σ a y = Σ_storage_var Σ' a y).
    { intro y. unfold Σ_storage_var.
      destruct d as [lay Hlay].
      destruct H0 as [Hst _].
      rewrite Hlay. rewrite (Hst a lay Hlay). reflexivity. }
    econstructor; eauto.
    + eapply Σ_incl_storage_dom; eauto.
    + intro x0. rewrite (i x0). split; intros [st0 Hst0]; exists st0.
      * rewrite <- Hssv. exact Hst0.
      * rewrite Hssv. exact Hst0.
    + intros x0 st0 Hst0. rewrite <- Hssv in Hst0. eapply H; eauto.
  - (* V_MappingVal *) constructor; auto.
  - (* V_ABIVal *) constructor. eauto.
  - (* V_Contract *) constructor. eauto.
Qed.

Lemma valuetyp_storetyp_weak_abi :
  forall Σ Σ' v s alpha,
    Σ_incl Σ Σ' ->
    has_abi_type Σ v s alpha ->
    has_abi_type Σ' v s alpha.
Proof. intros. eapply (proj1 valuetyp_storetyp_weak); eauto. Qed.

Lemma valuetyp_storetyp_weak_slot :
  forall Σ Σ' v s st,
    Σ_incl Σ Σ' ->
    has_slot_type Σ v s st ->
    has_slot_type Σ' v s st.
Proof. intros. eapply (proj2 valuetyp_storetyp_weak); eauto. Qed.

(** ** Preservation Lemmas *)

(** Helper: state_update_var preserves dom *)
Lemma state_update_var_dom : forall s l x v l',
  state_dom s l' -> state_dom (state_update_var s l x v) l'.
Proof.
  intros s l x v l' [ls' Hls'].
  unfold state_dom. rewrite state_update_var_store.
  destruct (s l) eqn:El.
  - destruct (Nat.eqb l l') eqn:Ell'.
    + eexists; reflexivity.
    + eexists; eauto.
  - eexists; eauto.
Qed.

(** Helper: state_update_var preserves type *)
Lemma state_update_var_type : forall s l x v l' a,
  state_type s l' = Some a -> state_type (state_update_var s l x v) l' = Some a.
Proof.
  intros. unfold state_type. rewrite state_update_var_store.
  unfold state_type in H.
  destruct (s l) eqn:El.
  - destruct (Nat.eqb_spec l l').
    + subst. rewrite El in H. simpl. exact H.
    + exact H.
  - exact H.
Qed.

(** Helper: state_update_var variable access *)
Lemma state_update_var_same : forall s l x v,
  state_dom s l ->
  state_var (state_update_var s l x v) l x = Some v.
Proof.
  intros s l x v [ls Hls].
  unfold state_var. rewrite state_update_var_store. rewrite Hls.
  rewrite Nat.eqb_refl. simpl.
  unfold Maps.update. rewrite String.eqb_refl. auto.
Qed.

Lemma state_update_var_other : forall s l x v l' y,
  (l' <> l \/ y <> x) ->
  state_var (state_update_var s l x v) l' y = state_var s l' y.
Proof.
  intros. unfold state_var. rewrite state_update_var_store.
  destruct (s l) eqn:El.
  - destruct (Nat.eqb_spec l l').
    + subst. simpl.
      unfold Maps.update. destruct (String.eqb x y) eqn:Exy.
      * apply String.eqb_eq in Exy. subst. exfalso. destruct H as [Hc|Hc]; apply Hc; reflexivity.
      * rewrite El. auto.
    + auto.
  - auto.
Qed.

(** Helper: state_var_force preserved for other locations/variables *)
Lemma state_update_var_force_other : forall s l x v l' y,
  (l' <> l \/ y <> x) ->
  state_var_force (state_update_var s l x v) l' y = state_var_force s l' y.
Proof.
  intros. unfold state_var_force. rewrite state_update_var_other; auto.
Qed.

Lemma state_update_var_force_same : forall s l x v,
  state_dom s l ->
  state_var_force (state_update_var s l x v) l x = v.
Proof.
  intros. unfold state_var_force. rewrite state_update_var_same; auto.
Qed.

Lemma state_update_var_var_dom : forall s l x v l' y,
  (l' <> l \/ y <> x) ->
  state_var_dom (state_update_var s l x v) l' y <-> state_var_dom s l' y.
Proof.
  intros. unfold state_var_dom. split; intros [w Hw].
  - rewrite state_update_var_other in Hw by auto. eauto.
  - rewrite state_update_var_other by auto. eauto.
Qed.

Lemma state_update_var_var_dom_same : forall s l x v,
  state_dom s l ->
  state_var_dom (state_update_var s l x v) l x.
Proof.
  intros. exists v. apply state_update_var_same. auto.
Qed.

(** Convert has_slot_type from s to s' for a slot type that appears in
    a contract's storage, given the IH for contract dependencies *)
Lemma convert_slot_type_from_storage :
  forall Σ s l a x v',
    has_slot_type Σ (VAddr l) s (SContract a) ->
    (exists st, Σ_storage_var Σ a x = Some st /\
                has_slot_type Σ v' s st) ->
    let s' := state_update_var s l x v' in
    forall c,
    (forall b, contract_dep Σ b c ->
       forall w, has_abi_type Σ w s (AContractAddr b) ->
                 has_abi_type Σ w s' (AContractAddr b)) ->
    forall y st w,
      Σ_storage_var Σ c y = Some st ->
      has_slot_type Σ w s st ->
      has_slot_type Σ w s' st.
Proof.
  intros Σ s l a x v' Hloc Hv' s' c IH y st w Hst Htyp.
  destruct st as [mu0 | [bt0 | b0] | b0].
  - inv Htyp. constructor. auto.
  - inv Htyp.
    match goal with [H : has_abi_type _ _ _ _ |- _] => inv H end.
    constructor. constructor. auto.
  - inv Htyp. constructor. apply (IH b0).
    + exists y. right. exact Hst.
    + match goal with [H : has_abi_type _ _ _ _ |- _] => exact H end.
  - inv Htyp. constructor. apply (IH b0).
    + exists y. left. exact Hst.
    + match goal with [H : has_abi_type _ _ _ _ |- _] => exact H end.
Qed.

(** Core preservation: by Acc induction on contract dependency *)
Lemma update_preserves_abi_contract :
  forall Σ s l a x v',
    has_slot_type Σ (VAddr l) s (SContract a) ->
    (exists st, Σ_storage_var Σ a x = Some st /\
                has_slot_type Σ v' s st) ->
    let s' := state_update_var s l x v' in
    forall c, Acc (contract_dep Σ) c ->
    forall w, has_abi_type Σ w s (AContractAddr c) ->
              has_abi_type Σ w s' (AContractAddr c).
Proof.
  intros Σ s l a x v' Hloc Hv' s' c Hacc.
  induction Hacc as [c _ IH].
  intros w Hw. inversion Hw; subst. unfold s' in *.
  assert (Htype_l : state_type s l = Some a).
  { inv Hloc. match goal with [H : has_abi_type _ _ _ _ |- _] => inv H; auto end. }
  assert (Hdom_l : state_dom s l).
  { inv Hloc. match goal with [H : has_abi_type _ _ _ _ |- _] => inv H; auto end. }
  econstructor; eauto using state_update_var_dom, state_update_var_type.
  - (* state_var_dom equivalence *)
    intro y.
    destruct (Nat.eq_dec l0 l) as [Hl|Hl]; [|rewrite state_update_var_var_dom by auto; auto].
    subst l0.
    destruct (String.eqb_spec y x) as [Hyx|Hyx]; [|rewrite state_update_var_var_dom by auto; auto].
    subst y.
    assert (Hca : c = a) by (unfold state_type in *; destruct (s l); [congruence|discriminate]). subst c.
    split.
    + intros _. destruct Hv' as [st0 [Hst0 _]]. eauto.
    + intros _. apply state_update_var_var_dom_same. exact Hdom_l.
  - (* variable typing *)
    intros y st Hst.
    destruct (Nat.eq_dec l0 l) as [Hl|Hl];
    destruct (String.eqb_spec y x) as [Hyx|Hyx].
    + (* l0 = l, y = x: updated variable *)
      subst.
      assert (Hca : c = a) by (unfold state_type in *; destruct (s l); [congruence|discriminate]). subst c.
      rewrite state_update_var_force_same by exact Hdom_l.
      destruct Hv' as [st0 [Hst0 Hv'typ]].
      assert (Heq : st = st0) by (unfold Σ_storage_var in *; congruence). subst st0.
      eapply convert_slot_type_from_storage; eauto.
    + (* l0 = l, y <> x *)
      subst l0. rewrite state_update_var_force_other by auto.
      eapply convert_slot_type_from_storage; eauto.
    + (* l0 <> l, y = x *)
      subst y. rewrite state_update_var_force_other by auto.
      eapply convert_slot_type_from_storage; eauto.
    + (* l0 <> l, y <> x *)
      rewrite state_update_var_force_other by auto.
      eapply convert_slot_type_from_storage; eauto.
Qed.

(** Well-typed Update Preserves Typing — Lemma 5.8
    By well-founded induction on the contract dependency relation. *)
Lemma update_preserves_typing :
  forall Σ v s s' sty l a x v',
    Σ_wf Σ ->
    has_slot_type Σ v s sty ->
    has_slot_type Σ (VAddr l) s (SContract a) ->
    (exists st, Σ_storage_var Σ a x = Some st /\
                has_slot_type Σ v' s st) ->
    s' = state_update_var s l x v' ->
    has_slot_type Σ v s' sty.
Proof.
  intros Σ v s s' sty l a x v' Hwf Hv Hloc Hv' Hs'. subst s'.
  destruct sty as [mu | alpha | b].
  - inversion Hv; subst. constructor. auto.
  - destruct alpha as [bt | b].
    + inversion Hv; subst.
      match goal with [H : has_abi_type _ _ _ _ |- _] => inversion H; subst end.
      constructor. constructor. auto.
    + inversion Hv; subst. constructor.
      apply (update_preserves_abi_contract Σ s l a x v' Hloc Hv' b (Hwf b)).
      match goal with [H : has_abi_type _ _ _ _ |- _] => exact H end.
  - inversion Hv; subst. constructor.
    apply (update_preserves_abi_contract Σ s l a x v' Hloc Hv' b (Hwf b)).
    match goal with [H : has_abi_type _ _ _ _ |- _] => exact H end.
Qed.

(** Well-typed Insertion Preserves Typing — Lemma 5.9
    eval_insert always results in a state_update_var, so this
    reduces to update_preserves_typing after case analysis. *)
Lemma insertion_preserves_typing :
  forall Σ v s s' sty l a rho r v',
    Σ_wf Σ ->
    has_slot_type Σ v s sty ->
    has_slot_type Σ (VAddr l) s (SContract a) ->
    eval_insert s rho r v' l s' ->
    (forall l' x, s' = state_update_var s l' x v' ->
      has_slot_type Σ (VAddr l') s (SContract a) /\
      exists st, Σ_storage_var Σ a x = Some st /\
                 has_slot_type Σ v' s st) ->
    has_slot_type Σ v s' sty.
Proof.
  intros Σ v s s' sty l a rho r v' Hwf Hv Hloc Hins Htarget.
  inversion Hins; subst.
  - (* E_InsStorage *)
    destruct (Htarget l x eq_refl) as [Hloc' [st [Hst Hv'typ]]].
    eapply update_preserves_typing; eauto.
  - (* E_InsField *)
    destruct (Htarget l' x eq_refl) as [Hloc' [st [Hst Hv'typ]]].
    eapply update_preserves_typing; eauto.
Qed.

(* ================================================================= *)
(** ** build_ctor_env produces a well-typed environment *)

Lemma combine_forall2_lookup :
  forall Σ s (iface : interface) (vals : list value) x alpha,
    Forall2 (fun v alpha => has_abi_type Σ v s alpha) vals (map snd iface) ->
    alist_lookup iface x = Some alpha ->
    exists v, alist_lookup (combine (map fst iface) vals) x = Some v /\
              has_abi_type Σ v s alpha.
Proof.
  intros Σ s iface. induction iface as [|[k a] rest IH]; intros vals x alpha HF Hlk.
  - simpl in Hlk. discriminate.
  - destruct vals as [|v vt]; [inversion HF|].
    inversion HF as [|? ? ? ? Hv HFrest]; subst.
    simpl in *. destruct (String.eqb_spec k x).
    + subst. injection Hlk as ->. exists v. split; [reflexivity | exact Hv].
    + exact (IH _ _ _ HFrest Hlk).
Qed.

Lemma combine_dom_fwd :
  forall (A B : Type) (iface : list (ident * A)) (vals : list B) x,
    length vals = length iface ->
    alist_dom (combine (map fst iface) vals) x -> alist_dom iface x.
Proof.
  intros A B iface. induction iface as [|[k a] rest IH]; intros vals x Hlen [w Hw].
  - destruct vals; simpl in Hw; discriminate.
  - destruct vals as [|v vt]; [simpl in Hlen; discriminate|].
    simpl in Hw. simpl in Hlen. injection Hlen as Hlen.
    destruct (String.eqb_spec k x) as [->|Hne].
    + exists a. apply alist_cons_eq.
    + destruct (IH vt x Hlen (ex_intro _ w Hw)) as [w' Hw'].
      exists w'. rewrite alist_cons_neq by auto. exact Hw'.
Qed.

Lemma combine_dom_bwd :
  forall (A B : Type) (iface : list (ident * A)) (vals : list B) x,
    length vals = length iface ->
    alist_dom iface x -> alist_dom (combine (map fst iface) vals) x.
Proof.
  intros A B iface. induction iface as [|[k a] rest IH]; intros vals x Hlen [w Hw].
  - simpl in Hw. discriminate.
  - destruct vals as [|v vt]; [simpl in Hlen; discriminate|].
    simpl in Hw. simpl in Hlen. injection Hlen as Hlen.
    destruct (String.eqb_spec k x) as [->|Hne].
    + exists v. simpl. rewrite String.eqb_refl. reflexivity.
    + destruct (IH vt x Hlen (ex_intro _ w Hw)) as [w' Hw'].
      exists w'. simpl. destruct (String.eqb_spec k x); [contradiction|exact Hw'].
Qed.

Lemma build_ctor_env_well_typed :
  forall Σ s (iface : interface) (vals : list value)
    (caller : addr) (origin : value) (callvalue : value),
    Forall2 (fun v alpha => has_abi_type Σ v s alpha) vals (map snd iface) ->
    has_base_type origin TAddress ->
    has_base_type callvalue (TInt (UintT 256)) ->
    ~ alist_dom iface "caller"%string ->
    ~ alist_dom iface "origin"%string ->
    ~ alist_dom iface "callvalue"%string ->
    env_well_typed Σ (build_ctor_env iface vals caller origin callvalue) s iface.
Proof.
  intros Σ s iface vals caller origin callvalue HF Horigin Hcv Hnc Hno Hncv.
  assert (Hlen : length vals = length iface).
  { apply Forall2_length in HF. rewrite map_length in HF. exact HF. }
  unfold build_ctor_env, list_to_map, env_well_typed.
  split; [|split; [|split; [|split]]].
  - (* domain *)
    intro x. split.
    + intros [v0 Hv0]. rewrite alist_lookup_app in Hv0.
      destruct (alist_lookup (combine (map fst iface) vals) x) eqn:E.
      * left. exact (combine_dom_fwd _ _ _ _ _ Hlen (ex_intro _ _ E)).
      * destruct (String.eqb_spec "caller"%string x) as [->|Hc1].
        { right; left; auto. }
        destruct (String.eqb_spec "origin"%string x) as [->|Ho1].
        { right; right; left; auto. }
        destruct (String.eqb_spec "callvalue"%string x) as [->|Hcv1].
        { right; right; right; auto. }
        exfalso.
        unfold alist_lookup in Hv0. fold (@alist_lookup value) in Hv0.
        destruct (String.eqb_spec "caller"%string x); [contradiction|].
        destruct (String.eqb_spec "origin"%string x); [contradiction|].
        destruct (String.eqb_spec "callvalue"%string x); [contradiction|].
        discriminate.
    + intros [Hdom | [-> | [-> | ->]]].
      * destruct (combine_dom_bwd _ _ _ _ _ Hlen Hdom) as [v Hv].
        exists v. apply alist_lookup_app_some. exact Hv.
      * apply alist_dom_app_r. exists (VAddr caller).
        apply alist_cons_eq.
      * apply alist_dom_app_r. exists origin.
        rewrite alist_cons_neq by discriminate. apply alist_cons_eq.
      * apply alist_dom_app_r. exists callvalue.
        rewrite alist_cons_neq by discriminate.
        rewrite alist_cons_neq by discriminate.
        apply alist_cons_eq.
  - (* interface variables *)
    intros x alpha Hlk.
    destruct (combine_forall2_lookup _ _ _ _ _ _ HF Hlk) as [v [Hv Htv]].
    exists v. split; [apply alist_lookup_app_some; exact Hv | exact Htv].
  - (* caller — not in iface, so combine lookup is None *)
    assert (Ecaller : alist_lookup (combine (map fst iface) vals) "caller"%string = None).
    { destruct (alist_lookup (combine (map fst iface) vals) "caller"%string) eqn:E; [|reflexivity].
      exfalso. apply Hnc. exact (combine_dom_fwd _ _ _ _ _ Hlen (ex_intro _ _ E)). }
    exists (VAddr caller). split.
    + unfold build_ctor_env, list_to_map.
      rewrite alist_lookup_app_none by exact Ecaller.
      apply alist_cons_eq.
    + constructor.
  - (* origin — not in iface *)
    assert (Eorigin : alist_lookup (combine (map fst iface) vals) "origin"%string = None).
    { destruct (alist_lookup (combine (map fst iface) vals) "origin"%string) eqn:E; [|reflexivity].
      exfalso. apply Hno. exact (combine_dom_fwd _ _ _ _ _ Hlen (ex_intro _ _ E)). }
    exists origin. split.
    + unfold build_ctor_env, list_to_map.
      rewrite alist_lookup_app_none by exact Eorigin.
      rewrite alist_cons_neq by discriminate. apply alist_cons_eq.
    + exact Horigin.
  - (* callvalue — not in iface *)
    assert (Ecallvalue : alist_lookup (combine (map fst iface) vals) "callvalue"%string = None).
    { destruct (alist_lookup (combine (map fst iface) vals) "callvalue"%string) eqn:E; [|reflexivity].
      exfalso. apply Hncv. exact (combine_dom_fwd _ _ _ _ _ Hlen (ex_intro _ _ E)). }
    exists callvalue. split.
    + unfold build_ctor_env, list_to_map.
      rewrite alist_lookup_app_none by exact Ecallvalue.
      rewrite alist_cons_neq by discriminate.
      rewrite alist_cons_neq by discriminate.
      apply alist_cons_eq.
    + exact Hcv.
Qed.

(** Σ_well_typed is defined in Typing.v where the typing judgments
    are available. Well-founded state and extending Σ preserves
    well-typedness are stated in TypeSafety.v. *)
