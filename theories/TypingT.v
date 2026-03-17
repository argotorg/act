(** * Typing Judgments in Type
    Mirror of Typing.v but with all inductives in Type instead of Prop,
    enabling large elimination for defining denotation functions.
    Includes correspondence lemmas: Type → Prop. *)

From Stdlib Require Import String ZArith List Bool.
From Act Require Import Maps Syntax Domains Semantics ValueTyping Typing.
Import ListNotations.

(* ================================================================= *)
(** ** ForallT / Forall2T — Type-valued versions of Forall / Forall2 *)

Inductive ForallT {A : Type} (P : A -> Type) : list A -> Type :=
  | ForallT_nil : ForallT P []
  | ForallT_cons : forall x xs, P x -> ForallT P xs -> ForallT P (x :: xs).

Arguments ForallT_nil {A P}.
Arguments ForallT_cons {A P x xs}.

Inductive Forall2T {A B : Type} (R : A -> B -> Type) : list A -> list B -> Type :=
  | Forall2T_nil : Forall2T R [] []
  | Forall2T_cons : forall x y xs ys,
      R x y -> Forall2T R xs ys -> Forall2T R (x :: xs) (y :: ys).

Arguments Forall2T_nil {A B R}.
Arguments Forall2T_cons {A B R x y xs ys}.

(** Correspondence: ForallT → Forall *)
Lemma ForallT_to_Forall : forall {A} {P : A -> Prop} {l},
  ForallT P l -> Forall P l.
Proof.
  intros A P l H. induction H; constructor; assumption.
Qed.

Lemma Forall2T_to_Forall2 : forall {A B} {R : A -> B -> Prop} {la lb},
  Forall2T R la lb -> Forall2 R la lb.
Proof.
  intros A B R la lb H. induction H; constructor; assumption.
Qed.

Lemma ForallT_map : forall {A} {P : A -> Type} {Q : A -> Prop} {l},
  (forall a, P a -> Q a) -> ForallT P l -> Forall Q l.
Proof.
  intros A P Q l f H. induction H; constructor; auto.
Qed.

Lemma Forall2T_map : forall {A B} {P : A -> B -> Type} {Q : A -> B -> Prop}
    {la lb},
  (forall a b, P a b -> Q a b) -> Forall2T P la lb -> Forall2 Q la lb.
Proof.
  intros A B P Q la lb f H. induction H; constructor; auto.
Qed.

(* ================================================================= *)
(** ** Environment References — Type version *)

Inductive type_env_ref_t : contract_env -> interface -> opt_id -> env_var -> abi_type -> Type :=
  | T_Caller_t : forall Σ iface oid,
      type_env_ref_t Σ iface oid EnvCaller (ABase TAddress)
  | T_Origin_t : forall Σ iface oid,
      type_env_ref_t Σ iface oid EnvOrigin (ABase TAddress)
  | T_Callvalue_t : forall Σ iface oid,
      type_env_ref_t Σ iface oid EnvCallvalue (ABase (TInt (UintT 256)))
  | T_This_t : forall Σ iface a,
      type_env_ref_t Σ iface (OSome a) EnvThis (AContractAddr a).

(* ================================================================= *)
(** ** References and Expressions — Type version (mutual) *)

Inductive type_ref_t : contract_env -> interface -> ref_tag -> opt_id -> time_tag ->
                        ref -> slot_type -> Type :=
  | T_Calldata_t : forall Σ iface oid t x alpha,
      alist_lookup iface x = Some alpha ->
      type_ref_t Σ iface TagN oid t (RVar x) (SAbi alpha)

  | T_Storage_t : forall Σ iface a x sty layout,
      Σ_storage Σ a = Some layout ->
      alist_lookup layout x = Some sty ->
      ~ alist_dom iface x ->
      x <> "caller"%string -> x <> "origin"%string -> x <> "callvalue"%string ->
      type_ref_t Σ iface TagS (OSome a) TagU (RVar x) sty

  | T_StoragePre_t : forall Σ iface a x sty layout,
      Σ_storage Σ a = Some layout ->
      alist_lookup layout x = Some sty ->
      ~ alist_dom iface x ->
      x <> "caller"%string -> x <> "origin"%string -> x <> "callvalue"%string ->
      type_ref_t Σ iface TagS (OSome a) TagT (RPre x) sty

  | T_StoragePost_t : forall Σ iface a x sty layout,
      Σ_storage Σ a = Some layout ->
      alist_lookup layout x = Some sty ->
      ~ alist_dom iface x ->
      x <> "caller"%string -> x <> "origin"%string -> x <> "callvalue"%string ->
      type_ref_t Σ iface TagS (OSome a) TagT (RPost x) sty

  | T_Coerce_t : forall Σ iface k oid t r a,
      type_ref_t Σ iface k oid t r (SAbi (AContractAddr a)) ->
      type_ref_t Σ iface TagN oid t (RCoerce r a) (SContract a)

  | T_Upcast_t : forall Σ iface k oid t r a,
      type_ref_t Σ iface k oid t r (SAbi (AContractAddr a)) ->
      type_ref_t Σ iface TagN oid t r (SAbi (ABase TAddress))

  | T_Field_t : forall Σ iface k oid t r a x sty,
      type_ref_t Σ iface k oid t r (SContract a) ->
      Σ_storage_var Σ a x = Some sty ->
      type_ref_t Σ iface k oid t (RField r x) sty

  | T_MapIndex_t : forall Σ iface k oid t r e bt mu,
      type_ref_t Σ iface k oid t r (SMapping (MMapping bt mu)) ->
      type_expr_t Σ iface oid t e bt ->
      type_ref_t Σ iface TagN oid t (RIndex r e) (SMapping mu)

  | T_Environment_t : forall Σ iface oid ev alpha,
      type_env_ref_t Σ iface oid ev alpha ->
      type_ref_t Σ iface TagN oid TagU (REnv ev) (SAbi alpha)

with type_expr_t : contract_env -> interface -> opt_id -> time_tag ->
                    expr -> base_type -> Type :=
  | T_Int_t : forall Σ iface oid t n it,
      in_range it n ->
      type_expr_t Σ iface oid t (EInt n) (TInt it)

  | T_Bool_t : forall Σ iface oid t b,
      type_expr_t Σ iface oid t (EBool b) TBool

  | T_Ref_t : forall Σ iface oid t k r bt,
      type_ref_t Σ iface k oid t r (SAbi (ABase bt)) ->
      type_expr_t Σ iface oid t (ERef r) bt

  | T_Addr_t : forall Σ iface oid k r a,
      type_ref_t Σ iface k oid TagU r (SContract a) ->
      type_expr_t Σ iface oid TagU (EAddr r) TAddress

  | T_Range_t : forall Σ iface oid t e it1 it2,
      type_expr_t Σ iface oid t e (TInt it2) ->
      type_expr_t Σ iface oid t (EInRange it1 e) TBool

  | T_BopI_t : forall Σ iface oid t e1 op e2 it1 it2,
      type_expr_t Σ iface oid t e1 (TInt it1) ->
      type_expr_t Σ iface oid t e2 (TInt it2) ->
      type_expr_t Σ iface oid t (EBopI e1 op e2) (TInt IntUnbounded)

  | T_NumConv_t : forall Σ iface oid t e it,
      type_expr_t Σ iface oid t e (TInt it) ->
      type_expr_t Σ iface oid t e (TInt IntUnbounded)

  | T_BopB_t : forall Σ iface oid t e1 op e2,
      type_expr_t Σ iface oid t e1 TBool ->
      type_expr_t Σ iface oid t e2 TBool ->
      type_expr_t Σ iface oid t (EBopB e1 op e2) TBool

  | T_Neg_t : forall Σ iface oid t e,
      type_expr_t Σ iface oid t e TBool ->
      type_expr_t Σ iface oid t (ENeg e) TBool

  | T_Cmp_t : forall Σ iface oid t e1 op e2 it,
      type_expr_t Σ iface oid t e1 (TInt it) ->
      type_expr_t Σ iface oid t e2 (TInt it) ->
      type_expr_t Σ iface oid t (ECmp e1 op e2) TBool

  | T_ITE_t : forall Σ iface oid t e1 e2 e3 bt,
      type_expr_t Σ iface oid t e1 TBool ->
      type_expr_t Σ iface oid t e2 bt ->
      type_expr_t Σ iface oid t e3 bt ->
      type_expr_t Σ iface oid t (EITE e1 e2 e3) bt

  | T_Eq_t : forall Σ iface oid t e1 e2 bt,
      type_expr_t Σ iface oid t e1 bt ->
      type_expr_t Σ iface oid t e2 bt ->
      type_expr_t Σ iface oid t (EEq e1 e2) TBool.

(** Mutual induction schemes are auto-generated for Type inductives. *)

(* ================================================================= *)
(** ** Mapping Expression — Type version *)

Inductive type_mapexpr_t : contract_env -> interface -> opt_id ->
                            map_expr -> mapping_type -> Type :=
  | T_Exp_t : forall Σ iface oid e bt,
      type_expr_t Σ iface oid TagU e bt ->
      type_mapexpr_t Σ iface oid (MExp e) (MBase bt)

  | T_Mapping_t : forall Σ iface oid bindings bt mu,
      default_value_typable mu ->
      ForallT (fun p => type_expr_t Σ iface oid TagU (fst p) bt) bindings ->
      ForallT (fun p => type_mapexpr_t Σ iface oid (snd p) mu) bindings ->
      type_mapexpr_t Σ iface oid (MMap bindings (MMapping bt mu)) (MMapping bt mu)

  | T_MappingUpd_t : forall Σ iface oid r bindings bt mu k,
      type_ref_t Σ iface k oid TagU r (SMapping (MMapping bt mu)) ->
      ForallT (fun p => type_expr_t Σ iface oid TagU (fst p) bt) bindings ->
      ForallT (fun p => type_mapexpr_t Σ iface oid (snd p) mu) bindings ->
      type_mapexpr_t Σ iface oid (MMapUpd r bindings (MMapping bt mu)) (MMapping bt mu).

(* ================================================================= *)
(** ** Slot Expression — Type version *)

Inductive type_slotexpr_t : contract_env -> interface -> opt_id ->
                              slot_expr -> slot_type -> Type :=
  | T_SlotMap_t : forall Σ iface oid m mu,
      type_mapexpr_t Σ iface oid m mu ->
      type_slotexpr_t Σ iface oid (SEMap m) (SMapping mu)

  | T_SlotRef_t : forall Σ iface oid k r a,
      type_ref_t Σ iface k oid TagU r (SContract a) ->
      type_slotexpr_t Σ iface oid (SERef r) (SContract a)

  | T_SlotAddr_t : forall Σ iface oid se a,
      type_slotexpr_t Σ iface oid se (SContract a) ->
      type_slotexpr_t Σ iface oid (SEAddr se) (SAbi (AContractAddr a))

  | T_Create_t : forall Σ iface oid a ctor ses,
      Σ_cnstr Σ a = Some ctor ->
      isPayable ctor = false ->
      Forall2T (fun se alpha => type_slotexpr_t Σ iface oid se (SAbi alpha))
               ses (map snd (ctor_iface ctor)) ->
      (** P4: semantic entailment — stays in Prop *)
      (forall s rho l vals s_final,
        env_well_typed Σ rho s iface ->
        loc_has_opt_type Σ l s oid ->
        eval_slotexpr_list (Σ_cnstr Σ) s rho ses l vals s_final ->
        Forall (fun pre =>
          eval_expr (TSUntimed s_final)
            (build_ctor_env (ctor_iface ctor) vals l (env_origin rho) (VInt 0%Z))
            pre dummy_loc (VBool true))
          (ctor_iff ctor)) ->
      type_slotexpr_t Σ iface oid (SENew a None ses) (SContract a)

  | T_CreatePayable_t : forall Σ iface oid a ctor se_val ses,
      Σ_cnstr Σ a = Some ctor ->
      isPayable ctor = true ->
      Forall2T (fun se alpha => type_slotexpr_t Σ iface oid se (SAbi alpha))
               ses (map snd (ctor_iface ctor)) ->
      type_slotexpr_t Σ iface oid se_val (SAbi (ABase (TInt (UintT 256)))) ->
      (** P4: semantic entailment — stays in Prop *)
      (forall s rho l vals s_final sv s_v,
        env_well_typed Σ rho s iface ->
        loc_has_opt_type Σ l s oid ->
        eval_slotexpr_list (Σ_cnstr Σ) s rho ses l vals s_final ->
        eval_slotexpr (Σ_cnstr Σ) s_final rho se_val l sv s_v ->
        Forall (fun pre =>
          eval_expr (TSUntimed s_v)
            (build_ctor_env (ctor_iface ctor) vals l (env_origin rho) sv)
            pre dummy_loc (VBool true))
          (ctor_iff ctor)) ->
      type_slotexpr_t Σ iface oid (SENew a (Some se_val) ses) (SContract a).

(* ================================================================= *)
(** ** Create — Type version *)

Inductive type_creates_t : contract_env -> interface -> opt_id ->
                            list create -> storage_layout -> Type :=
  | T_Creates_t : forall Σ iface oid creates layout,
      layout = map (fun c => (snd (fst c), fst (fst c))) creates ->
      alist_lookup layout "balance"%string = Some (SAbi (ABase (TInt (UintT 256)))) ->
      Forall (fun c => slot_type_wf Σ (fst (fst c))) creates ->
      ForallT (fun c => type_slotexpr_t Σ iface ONone (snd c) (fst (fst c))) creates ->
      type_creates_t Σ iface oid creates layout.

(* ================================================================= *)
(** ** Update — Type version *)

Inductive type_update_t : contract_env -> interface -> opt_id ->
                           update -> Type :=
  | T_Update_t : forall Σ iface oid r se sty,
      type_ref_t Σ iface TagS oid TagU r sty ->
      type_slotexpr_t Σ iface oid se sty ->
      type_update_t Σ iface oid (r, se).

Inductive type_updates_t : contract_env -> interface -> opt_id ->
                            list update -> Type :=
  | T_Updates_t : forall Σ iface oid upds,
      ForallT (fun u => type_update_t Σ iface oid u) upds ->
      (forall i j, i < length upds -> j < i ->
        ~ more_specific_eq (fst (nth j upds (RVar ""%string, SEMap (MExp (EBool false)))))
                            (fst (nth i upds (RVar ""%string, SEMap (MExp (EBool false)))))) ->
      type_updates_t Σ iface oid upds.

(* ================================================================= *)
(** ** Constructor — Type version *)

Inductive type_constructor_t : contract_env -> ident -> constructor ->
                                storage_layout -> Type :=
  | T_Ctor_t : forall Σ a ctor layout,
      interface_wf Σ (ctor_iface ctor) ->
      ForallT (fun pre => type_expr_t Σ (ctor_iface ctor) ONone TagU pre TBool)
              (ctor_iff ctor) ->
      ForallT (fun cc => type_expr_t Σ (ctor_iface ctor) ONone TagU (fst cc) TBool)
              (ctor_cases ctor) ->
      ForallT (fun cc => type_creates_t Σ (ctor_iface ctor) (OSome a) (snd cc) layout)
              (ctor_cases ctor) ->
      Forall (fun p => slot_type_wf Σ (snd p)) layout ->
      (forall x, alist_dom layout x -> ~ alist_dom (ctor_iface ctor) x) ->
      let Σ' := Σ_with_storage Σ a layout in
      ForallT (fun post => type_expr_t Σ' (ctor_iface ctor) (OSome a) TagU post TBool)
              (ctor_post ctor) ->
      (forall s rho,
        Forall (fun pre => eval_expr (TSUntimed s) rho pre dummy_loc (VBool true))
               (ctor_iff ctor) ->
        exists j, j < length (ctor_cases ctor) /\
          eval_expr (TSUntimed s) rho (fst (nth j (ctor_cases ctor) (EBool false, []))) dummy_loc (VBool true) /\
          forall i, i <> j -> i < length (ctor_cases ctor) ->
            eval_expr (TSUntimed s) rho (fst (nth i (ctor_cases ctor) (EBool false, []))) dummy_loc (VBool false)) ->
      type_constructor_t Σ a ctor layout.

(* ================================================================= *)
(** ** Transition — Type version *)

Inductive type_transition_t : contract_env -> ident -> transition -> Type :=
  | T_Trans_t : forall Σ a tr,
      interface_wf Σ (trans_iface tr) ->
      ForallT (fun pre => type_expr_t Σ (trans_iface tr) (OSome a) TagU pre TBool)
              (trans_iff tr) ->
      ForallT (fun tc => type_expr_t Σ (trans_iface tr) (OSome a) TagU (tc_cond tc) TBool)
              (trans_cases tr) ->
      ForallT (fun tc => type_updates_t Σ (trans_iface tr) (OSome a) (tc_updates tc))
              (trans_cases tr) ->
      ForallT (fun tc => type_expr_t Σ (trans_iface tr) (OSome a) TagT
                          (tc_return tc) TAddress)
              (trans_cases tr) ->
      ForallT (fun post => type_expr_t Σ (trans_iface tr) (OSome a) TagT post TBool)
              (trans_post tr) ->
      (forall s rho l,
        env_well_typed Σ rho s (trans_iface tr) ->
        has_slot_type Σ (VAddr l) s (SContract a) ->
        Forall (fun pre => eval_expr (TSUntimed s) rho pre l (VBool true))
               (trans_iff tr) ->
        exists j, j < length (trans_cases tr) /\
          eval_expr (TSUntimed s) rho (tc_cond (nth j (trans_cases tr) tc_default)) l (VBool true) /\
          forall i, i <> j -> i < length (trans_cases tr) ->
            eval_expr (TSUntimed s) rho (tc_cond (nth i (trans_cases tr) tc_default)) l (VBool false)) ->
      type_transition_t Σ a tr.

(* ================================================================= *)
(** ** Correspondence: Type → Prop *)

Lemma type_env_ref_t_to_prop : forall Σ iface oid ev alpha,
  type_env_ref_t Σ iface oid ev alpha ->
  type_env_ref Σ iface oid ev alpha.
Proof.
  intros Σ iface oid ev alpha H. destruct H; constructor.
Qed.

Fixpoint type_ref_t_to_prop Σ iface k oid t r sty
    (H : type_ref_t Σ iface k oid t r sty)
    : type_ref Σ iface k oid t r sty
with type_expr_t_to_prop Σ iface oid t e bt
    (H : type_expr_t Σ iface oid t e bt)
    : type_expr Σ iface oid t e bt.
Proof.
  - destruct H;
      first [ eapply T_Calldata
            | eapply T_Storage
            | eapply T_StoragePre
            | eapply T_StoragePost
            | eapply T_Coerce; eapply type_ref_t_to_prop
            | eapply T_Upcast; eapply type_ref_t_to_prop
            | eapply T_Field; [eapply type_ref_t_to_prop|]
            | eapply T_MapIndex;
                [eapply type_ref_t_to_prop | eapply type_expr_t_to_prop]
            | eapply T_Environment; eapply type_env_ref_t_to_prop
            ]; eassumption.
  - destruct H;
      first [ eapply T_Int
            | eapply T_Bool
            | eapply T_Ref; eapply type_ref_t_to_prop
            | eapply T_Addr; eapply type_ref_t_to_prop
            | eapply T_Range; eapply type_expr_t_to_prop
            | eapply T_BopI; eapply type_expr_t_to_prop
            | eapply T_NumConv; eapply type_expr_t_to_prop
            | eapply T_BopB; eapply type_expr_t_to_prop
            | eapply T_Neg; eapply type_expr_t_to_prop
            | eapply T_Cmp; eapply type_expr_t_to_prop
            | eapply T_ITE; eapply type_expr_t_to_prop
            | eapply T_Eq; eapply type_expr_t_to_prop
            ]; eassumption.
Qed.

Fixpoint type_mapexpr_t_to_prop Σ iface oid m mu
    (H : type_mapexpr_t Σ iface oid m mu)
    : type_mapexpr Σ iface oid m mu :=
  match H with
  | T_Exp_t _ _ _ _ _ He =>
      T_Exp _ _ _ _ _ (type_expr_t_to_prop _ _ _ _ _ _ He)
  | T_Mapping_t _ _ _ bindings _ _ Hd Hkeys Hvals =>
      T_Mapping _ _ _ bindings _ _
        Hd
        ((fix goK l (hl : ForallT _ l) : Forall _ l :=
          match hl with
          | ForallT_nil => Forall_nil _
          | ForallT_cons h hl' =>
              Forall_cons _ (type_expr_t_to_prop _ _ _ _ _ _ h) (goK _ hl')
          end) _ Hkeys)
        ((fix goV l (hl : ForallT _ l) : Forall _ l :=
          match hl with
          | ForallT_nil => Forall_nil _
          | ForallT_cons h hl' =>
              Forall_cons _ (type_mapexpr_t_to_prop _ _ _ _ _ h) (goV _ hl')
          end) _ Hvals)
  | T_MappingUpd_t _ _ _ _ bindings _ _ k Hr Hkeys Hvals =>
      T_MappingUpd _ _ _ _ bindings _ _ k
        (type_ref_t_to_prop _ _ _ _ _ _ _ Hr)
        ((fix goK l (hl : ForallT _ l) : Forall _ l :=
          match hl with
          | ForallT_nil => Forall_nil _
          | ForallT_cons h hl' =>
              Forall_cons _ (type_expr_t_to_prop _ _ _ _ _ _ h) (goK _ hl')
          end) _ Hkeys)
        ((fix goV l (hl : ForallT _ l) : Forall _ l :=
          match hl with
          | ForallT_nil => Forall_nil _
          | ForallT_cons h hl' =>
              Forall_cons _ (type_mapexpr_t_to_prop _ _ _ _ _ h) (goV _ hl')
          end) _ Hvals)
  end.

Fixpoint type_slotexpr_t_to_prop Σ iface oid se sty
    (H : type_slotexpr_t Σ iface oid se sty)
    : type_slotexpr Σ iface oid se sty :=
  match H with
  | T_SlotMap_t _ _ _ _ _ Hm =>
      T_SlotMap _ _ _ _ _ (type_mapexpr_t_to_prop _ _ _ _ _ Hm)
  | T_SlotRef_t _ _ _ k _ _ Hr =>
      T_SlotRef _ _ _ k _ _ (type_ref_t_to_prop _ _ _ _ _ _ _ Hr)
  | T_SlotAddr_t _ _ _ _ _ Hse =>
      T_SlotAddr _ _ _ _ _ (type_slotexpr_t_to_prop _ _ _ _ _ Hse)
  | T_Create_t _ _ _ _ ctor _ Hcl Hnp Hses HP4 =>
      T_Create _ _ _ _ ctor _
        Hcl Hnp
        ((fix go ses alphas (hs : Forall2T _ ses alphas) :
            Forall2 _ ses alphas :=
          match hs with
          | Forall2T_nil => Forall2_nil _
          | Forall2T_cons h hs' =>
              Forall2_cons _ _ (type_slotexpr_t_to_prop _ _ _ _ _ h)
                               (go _ _ hs')
          end) _ _ Hses)
        HP4
  | T_CreatePayable_t _ _ _ _ ctor _ _ Hcl Hpay Hses Hval HP4 =>
      T_CreatePayable _ _ _ _ ctor _ _
        Hcl Hpay
        ((fix go ses alphas (hs : Forall2T _ ses alphas) :
            Forall2 _ ses alphas :=
          match hs with
          | Forall2T_nil => Forall2_nil _
          | Forall2T_cons h hs' =>
              Forall2_cons _ _ (type_slotexpr_t_to_prop _ _ _ _ _ h)
                               (go _ _ hs')
          end) _ _ Hses)
        (type_slotexpr_t_to_prop _ _ _ _ _ Hval)
        HP4
  end.

Lemma type_creates_t_to_prop : forall Σ iface oid creates layout,
  type_creates_t Σ iface oid creates layout ->
  type_creates Σ iface oid creates layout.
Proof.
  intros Σ iface oid creates layout H. destruct H.
  eapply T_Creates; try eassumption.
  eapply ForallT_map; [|eassumption].
  intros a Ha; exact (type_slotexpr_t_to_prop _ _ _ _ _ Ha).
Qed.

Lemma type_update_t_to_prop : forall Σ iface oid u,
  type_update_t Σ iface oid u ->
  type_update Σ iface oid u.
Proof.
  intros Σ iface oid u H. destruct H.
  eapply T_Update;
    [eapply type_ref_t_to_prop | eapply type_slotexpr_t_to_prop]; eassumption.
Qed.

Lemma type_updates_t_to_prop : forall Σ iface oid upds,
  type_updates_t Σ iface oid upds ->
  type_updates Σ iface oid upds.
Proof.
  intros Σ iface oid upds H. destruct H.
  eapply T_Updates; try eassumption.
  eapply ForallT_map; [|eassumption].
  intros a Ha; exact (type_update_t_to_prop _ _ _ _ Ha).
Qed.

Lemma type_constructor_t_to_prop : forall Σ a ctor layout,
  type_constructor_t Σ a ctor layout ->
  type_constructor Σ a ctor layout.
Proof.
  intros Σ a ctor layout H. destruct H.
  eapply T_Ctor.
  - eassumption.
  - eapply ForallT_map; [|exact f].
    intros x Hx; exact (type_expr_t_to_prop _ _ _ _ _ _ Hx).
  - eapply ForallT_map; [|exact f0].
    intros x Hx; exact (type_expr_t_to_prop _ _ _ _ _ _ Hx).
  - eapply ForallT_map; [|exact f1].
    intros x Hx; exact (type_creates_t_to_prop _ _ _ _ _ Hx).
  - eassumption.
  - eassumption.
  - eapply ForallT_map; [|exact f3].
    intros x Hx; exact (type_expr_t_to_prop _ _ _ _ _ _ Hx).
  - eassumption.
Qed.

Lemma type_transition_t_to_prop : forall Σ a tr,
  type_transition_t Σ a tr ->
  type_transition Σ a tr.
Proof.
  intros Σ a tr H. destruct H.
  eapply T_Trans.
  - eassumption.
  - eapply ForallT_map; [|exact f].
    intros x Hx; exact (type_expr_t_to_prop _ _ _ _ _ _ Hx).
  - eapply ForallT_map; [|exact f0].
    intros x Hx; exact (type_expr_t_to_prop _ _ _ _ _ _ Hx).
  - eapply ForallT_map; [|exact f1].
    intros x Hx; exact (type_updates_t_to_prop _ _ _ _ Hx).
  - eapply ForallT_map; [|exact f2].
    intros x Hx; exact (type_expr_t_to_prop _ _ _ _ _ _ Hx).
  - eapply ForallT_map; [|exact f3].
    intros x Hx; exact (type_expr_t_to_prop _ _ _ _ _ _ Hx).
  - eassumption.
Qed.
