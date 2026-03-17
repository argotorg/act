(** * Pointer Semantics
    Formalizes Section 2 of the tech report: the big-step
    operational semantics for environment references, variable
    references, expressions, mapping expressions, slot expressions,
    creates, updates, constructor/transition cases, constructors,
    and transitions. *)

From Stdlib Require Import String ZArith List Bool PeanoNat Lia.
From Act Require Import Maps Syntax Domains.
Import ListNotations.

(* ================================================================= *)
(** ** Helper functions for operators *)

Definition eval_int_binop (op : int_binop) (v1 v2 : Z) : Z :=
  match op with
  | OpAdd => (v1 + v2)%Z
  | OpSub => (v1 - v2)%Z
  | OpMul => (v1 * v2)%Z
  | OpExp => (Z.pow v1 v2)
  | OpDiv => (Z.div v1 v2)
  | OpMod => if (v2 =? 0)%Z then 0%Z else (Z.modulo v1 v2)
  end.

Definition eval_bool_binop (op : bool_binop) (b1 b2 : bool) : bool :=
  match op with
  | OpAnd  => andb b1 b2
  | OpOr   => orb b1 b2
  | OpImpl => implb b1 b2
  end.

Definition eval_cmp (op : cmp_op) (v1 v2 : Z) : bool :=
  match op with
  | CmpLt => Z.ltb v1 v2
  | CmpLe => Z.leb v1 v2
  | CmpGe => Z.leb v2 v1
  | CmpGt => Z.ltb v2 v1
  end.

(** Apply a mapping value to a key value *)
Definition apply_map (vr ve : value) : option value :=
  match vr, ve with
  | VMapZ f, VBase (BVInt n)  => Some (f n)
  | VMapB f, VBase (BVBool b) => Some (f b)
  | VMapA f, VBase (BVAddr a) => Some (f a)
  | _, _ => None
  end.

(** Convert a list of (ident * value) pairs to a partial map *)
Definition list_to_map (bindings : list (ident * value)) : partial_map value :=
  fun x => alist_lookup bindings x.

(** Build constructor environment:
    ρ' = {xᵢ ↦ vᵢ} ∪ {caller ↦ ℓ, origin ↦ ρ(origin), callvalue ↦ cv} *)
Definition build_ctor_env (iface : interface) (vals : list value)
  (caller : addr) (origin : value) (callvalue : value) : env :=
  list_to_map (combine (map fst iface) vals ++
    [("caller"%string, VAddr caller);
     ("origin"%string, origin);
     ("callvalue"%string, callvalue)]).

(** Extract origin from environment, defaulting to address 0 *)
Definition env_origin (rho : env) : value :=
  match rho "origin"%string with Some v => v | None => VAddr 0 end.

(* ================================================================= *)
(** ** Semantics of Environment References *)
(** Judgment: ρ ; env ⇓_ℓ v *)

Inductive eval_env : env -> env_var -> addr -> value -> Prop :=
  | E_Caller : forall rho l v,
      rho "caller"%string = Some v ->
      eval_env rho EnvCaller l v
  | E_Origin : forall rho l v,
      rho "origin"%string = Some v ->
      eval_env rho EnvOrigin l v
  | E_Callvalue : forall rho l v,
      rho "callvalue"%string = Some v ->
      eval_env rho EnvCallvalue l v
  | E_This : forall rho l,
      eval_env rho EnvThis l (VAddr l).

(* ================================================================= *)
(** ** Semantics of Variable References and Expressions *)
(** Judgment: s^t ; ρ ; ref ⇓_ℓ (v, t_p)
    Judgment: s ; ρ ; e ⇓_ℓ v *)

Inductive eval_ref : timed_state -> env -> ref -> addr -> value -> ref_time -> Prop :=
  (** E-Environment *)
  | E_Environment : forall ts rho ev l v,
      eval_env rho ev l v ->
      eval_ref ts rho (REnv ev) l v RTU

  (** E-Storage: untimed *)
  | E_Storage : forall s rho x l v,
      state_var s l x = Some v ->
      rho x = None ->
      eval_ref (TSUntimed s) rho (RVar x) l v RTU

  (** E-StoragePre *)
  | E_StoragePre : forall s_pre s_post rho x l v,
      state_var s_pre l x = Some v ->
      rho x = None ->
      eval_ref (TSTimed s_pre s_post) rho (RPre x) l v RTPre

  (** E-StoragePost *)
  | E_StoragePost : forall s_pre s_post rho x l v,
      state_var s_post l x = Some v ->
      rho x = None ->
      eval_ref (TSTimed s_pre s_post) rho (RPost x) l v RTPost

  (** E-Calldata: untimed *)
  | E_Calldata : forall s rho x l v,
      rho x = Some v ->
      eval_ref (TSUntimed s) rho (RVar x) l v RTU

  (** E-CalldataTimed *)
  | E_CalldataTimed : forall s_pre s_post rho x l v,
      rho x = Some v ->
      eval_ref (TSTimed s_pre s_post) rho (RVar x) l v RTPre

  (** E-Coerce *)
  | E_Coerce : forall ts rho r a l v tp,
      eval_ref ts rho r l v tp ->
      eval_ref ts rho (RCoerce r a) l v tp

  (** E-Field: untimed *)
  | E_Field : forall s rho r x l l' v,
      eval_ref (TSUntimed s) rho r l (VAddr l') RTU ->
      state_var s l' x = Some v ->
      eval_ref (TSUntimed s) rho (RField r x) l v RTU

  (** E-FieldPre *)
  | E_FieldPre : forall s_pre s_post rho r x l l' v,
      eval_ref (TSTimed s_pre s_post) rho r l (VAddr l') RTPre ->
      state_var s_pre l' x = Some v ->
      eval_ref (TSTimed s_pre s_post) rho (RField r x) l v RTPre

  (** E-FieldPost *)
  | E_FieldPost : forall s_pre s_post rho r x l l' v,
      eval_ref (TSTimed s_pre s_post) rho r l (VAddr l') RTPost ->
      state_var s_post l' x = Some v ->
      eval_ref (TSTimed s_pre s_post) rho (RField r x) l v RTPost

  (** E-RefMapping *)
  | E_RefMapping : forall ts rho r e l vr ve vres tp,
      eval_ref ts rho r l vr tp ->
      eval_expr ts rho e l ve ->
      apply_map vr ve = Some vres ->
      eval_ref ts rho (RIndex r e) l vres tp

with eval_expr : timed_state -> env -> expr -> addr -> value -> Prop :=
  (** E-Int *)
  | E_Int : forall ts rho n l,
      eval_expr ts rho (EInt n) l (VInt n)

  (** E-Bool *)
  | E_Bool : forall ts rho b l,
      eval_expr ts rho (EBool b) l (VBool b)

  (** E-Ref *)
  | E_Ref : forall ts rho r l v tp,
      eval_ref ts rho r l v tp ->
      eval_expr ts rho (ERef r) l v

  (** E-Addr *)
  | E_Addr : forall ts rho r l v tp,
      eval_ref ts rho r l v tp ->
      eval_expr ts rho (EAddr r) l v

  (** E-RangeTrue *)
  | E_RangeTrue : forall ts rho iota e l n,
      eval_expr ts rho e l (VInt n) ->
      in_range iota n ->
      eval_expr ts rho (EInRange iota e) l (VBool true)

  (** E-RangeFalse *)
  | E_RangeFalse : forall ts rho iota e l n,
      eval_expr ts rho e l (VInt n) ->
      ~ in_range iota n ->
      eval_expr ts rho (EInRange iota e) l (VBool false)

  (** E-Div *)
  | E_Div : forall ts rho e1 e2 l v1 v2,
      eval_expr ts rho e1 l (VInt v1) ->
      eval_expr ts rho e2 l (VInt v2) ->
      (v2 <> 0)%Z ->
      eval_expr ts rho (EBopI e1 OpDiv e2) l (VInt (Z.div v1 v2))

  (** E-DivZero *)
  | E_DivZero : forall ts rho e1 e2 l v1,
      eval_expr ts rho e1 l (VInt v1) ->
      eval_expr ts rho e2 l (VInt 0%Z) ->
      eval_expr ts rho (EBopI e1 OpDiv e2) l (VInt 0%Z)

  (** E-Mod *)
  | E_Mod : forall ts rho e1 e2 l v1 v2,
      eval_expr ts rho e1 l (VInt v1) ->
      eval_expr ts rho e2 l (VInt v2) ->
      (v2 <> 0)%Z ->
      eval_expr ts rho (EBopI e1 OpMod e2) l (VInt (Z.modulo v1 v2))

  (** E-ModZero *)
  | E_ModZero : forall ts rho e1 e2 l v1,
      eval_expr ts rho e1 l (VInt v1) ->
      eval_expr ts rho e2 l (VInt 0%Z) ->
      eval_expr ts rho (EBopI e1 OpMod e2) l (VInt 0%Z)

  (** E-BopI: other integer ops *)
  | E_BopI : forall ts rho e1 op e2 l v1 v2,
      eval_expr ts rho e1 l (VInt v1) ->
      eval_expr ts rho e2 l (VInt v2) ->
      op <> OpDiv -> op <> OpMod ->
      eval_expr ts rho (EBopI e1 op e2) l (VInt (eval_int_binop op v1 v2))

  (** E-BopB *)
  | E_BopB : forall ts rho e1 op e2 l b1 b2,
      eval_expr ts rho e1 l (VBool b1) ->
      eval_expr ts rho e2 l (VBool b2) ->
      eval_expr ts rho (EBopB e1 op e2) l (VBool (eval_bool_binop op b1 b2))

  (** E-Neg *)
  | E_Neg : forall ts rho e l b,
      eval_expr ts rho e l (VBool b) ->
      eval_expr ts rho (ENeg e) l (VBool (negb b))

  (** E-Cmp *)
  | E_Cmp : forall ts rho e1 op e2 l v1 v2,
      eval_expr ts rho e1 l (VInt v1) ->
      eval_expr ts rho e2 l (VInt v2) ->
      eval_expr ts rho (ECmp e1 op e2) l (VBool (eval_cmp op v1 v2))

  (** E-ITETrue *)
  | E_ITETrue : forall ts rho e1 e2 e3 l v2,
      eval_expr ts rho e1 l (VBool true) ->
      eval_expr ts rho e2 l v2 ->
      eval_expr ts rho (EITE e1 e2 e3) l v2

  (** E-ITEFalse *)
  | E_ITEFalse : forall ts rho e1 e2 e3 l v3,
      eval_expr ts rho e1 l (VBool false) ->
      eval_expr ts rho e3 l v3 ->
      eval_expr ts rho (EITE e1 e2 e3) l v3

  (** E-EqTrue *)
  | E_EqTrue : forall ts rho e1 e2 l v1 v2,
      eval_expr ts rho e1 l v1 ->
      eval_expr ts rho e2 l v2 ->
      v1 = v2 ->
      eval_expr ts rho (EEq e1 e2) l (VBool true)

  (** E-EqFalse *)
  | E_EqFalse : forall ts rho e1 e2 l v1 v2,
      eval_expr ts rho e1 l v1 ->
      eval_expr ts rho e2 l v2 ->
      v1 <> v2 ->
      eval_expr ts rho (EEq e1 e2) l (VBool false).

(** Decidable equality on base values — needed for mapping semantics *)
Definition base_value_eqb (v1 v2 : base_value) : bool :=
  match v1, v2 with
  | BVInt n1, BVInt n2 => Z.eqb n1 n2
  | BVBool b1, BVBool b2 => Bool.eqb b1 b2
  | BVAddr a1, BVAddr a2 => Nat.eqb a1 a2
  | _, _ => false
  end.

Definition value_eqb (v1 v2 : value) : bool :=
  match v1, v2 with
  | VBase bv1, VBase bv2 => base_value_eqb bv1 bv2
  | _, _ => false
  end.

(** Helper: look up a value in keys/vals list, return default if not found. *)
Fixpoint lookup_or_default (keys vals : list value) (x : value) (def : value) : value :=
  match keys, vals with
  | k :: ks, v :: vs => if value_eqb k x then v else lookup_or_default ks vs x def
  | _, _ => def
  end.

(** Helper: look up in keys/vals, fall back to applying old function *)
Fixpoint lookup_or_apply (keys vals : list value) (x : value) (f_old : value) : value :=
  match keys, vals with
  | k :: ks, v :: vs => if value_eqb k x then v else lookup_or_apply ks vs x f_old
  | _, _ => match apply_map f_old x with
            | Some v => v
            | None => VInt 0%Z
            end
  end.

(** Build a mapping value from keys, vals, wrapped in the
    appropriate value constructor based on the mapping type.
    The default for unmapped keys comes from the value sub-type. *)
Definition build_map_from_bindings (keys vals : list value)
                                   (mu : mapping_type) : option value :=
  match mu with
  | MMapping (TInt _) mu' =>
      let def := default_value mu' in
      Some (VMapZ (fun n => lookup_or_default keys vals (VInt n) def))
  | MMapping TBool mu' =>
      let def := default_value mu' in
      Some (VMapB (fun b => lookup_or_default keys vals (VBool b) def))
  | MMapping TAddress mu' =>
      let def := default_value mu' in
      Some (VMapA (fun a => lookup_or_default keys vals (VAddr a) def))
  | MBase _ => None (* not a mapping type *)
  end.

(** Update a mapping value using keys/vals, falling back to old function *)
Definition update_map_from_bindings (keys vals : list value) (f_old : value)
                                     (mu : mapping_type) : option value :=
  match mu with
  | MMapping (TInt _) _ =>
      Some (VMapZ (fun n => lookup_or_apply keys vals (VInt n) f_old))
  | MMapping TBool _ =>
      Some (VMapB (fun b => lookup_or_apply keys vals (VBool b) f_old))
  | MMapping TAddress _ =>
      Some (VMapA (fun a => lookup_or_apply keys vals (VAddr a) f_old))
  | MBase _ => None
  end.

(* ================================================================= *)
(** ** Semantics of Mapping Expressions *)
(** Judgment: s ; ρ ; m ⇓_ℓ v *)

Inductive eval_mapexpr : timed_state -> env -> map_expr -> addr -> value -> Prop :=
  (** E-Exp *)
  | E_MExp : forall ts rho e l v,
      eval_expr ts rho e l v ->
      eval_mapexpr ts rho (MExp e) l v

  (** E-Mapping: the result f is a value that encodes a function *)
  | E_Mapping : forall ts rho bindings mu l keys vals f,
      Forall2 (fun p k => eval_expr ts rho (fst p) l k) bindings keys ->
      Forall2 (fun p v => eval_mapexpr ts rho (snd p) l v) bindings vals ->
      build_map_from_bindings keys vals mu = Some f ->
      eval_mapexpr ts rho (MMap bindings mu) l f

  (** E-MappingUpd *)
  | E_MappingUpd : forall ts rho r bindings mu l f_old f_new tp keys vals,
      eval_ref ts rho r l f_old tp ->
      Forall2 (fun p k => eval_expr ts rho (fst p) l k) bindings keys ->
      Forall2 (fun p v => eval_mapexpr ts rho (snd p) l v) bindings vals ->
      update_map_from_bindings keys vals f_old mu = Some f_new ->
      eval_mapexpr ts rho (MMapUpd r bindings mu) l f_new.

(* ================================================================= *)
(** ** Insert Value *)
(** Judgment: s ; ρ ; ref ; v ⇓^ins_ℓ s' *)

Inductive eval_insert : state -> env -> ref -> value -> addr -> state -> Prop :=
  (** E-InsStorage *)
  | E_InsStorage : forall s rho x v l,
      state_var_dom s l x ->
      eval_insert s rho (RVar x) v l (state_update_var s l x v)

  (** E-InsField *)
  | E_InsField : forall s rho r x v l l',
      eval_ref (TSUntimed s) rho r l (VAddr l') RTU ->
      state_var_dom s l' x ->
      eval_insert s rho (RField r x) v l (state_update_var s l' x v).

(** Update inserts — does not depend on cmap *)
Inductive eval_update_inserts : state -> env -> list update ->
                           list value -> addr -> state -> Prop :=
  | E_UpdInsertsNil : forall s rho l,
      eval_update_inserts s rho [] [] l s
  | E_UpdInsertsCons : forall s rho r se rest v vs l s' s_final,
      eval_insert s rho r v l s' ->
      eval_update_inserts s' rho rest vs l s_final ->
      eval_update_inserts s rho ((r, se) :: rest) (v :: vs) l s_final.

(* ================================================================= *)
(** ** Semantics of Slot Expressions *)
(** Judgment: s ; ρ ; se ⇓_ℓ (v, s') *)

Section EvalCmap.
Variable cmap : partial_map constructor.

Inductive eval_slotexpr : state -> env -> slot_expr -> addr -> value -> state -> Prop :=
  (** E-MapExp *)
  | E_SlotMap : forall s rho m l v,
      eval_mapexpr (TSUntimed s) rho m l v ->
      eval_slotexpr s rho (SEMap m) l v s

  (** E-SlotRef *)
  | E_SlotRef : forall s rho r l v tp,
      eval_ref (TSUntimed s) rho r l v tp ->
      eval_slotexpr s rho (SERef r) l v s

  (** E-SlotAddr *)
  | E_SlotAddr : forall s rho se l v s',
      eval_slotexpr s rho se l v s' ->
      eval_slotexpr s rho (SEAddr se) l v s'

  (** E-Create: new Id(se₁,...,seₙ) — non-payable.
      ctor is looked up from cmap, ρ' is constructed per the tech report. *)
  | E_Create : forall s rho a ctor ses l l' vals s_final s',
      cmap a = Some ctor ->
      ctor_payable ctor = false ->
      eval_slotexpr_list s rho ses l vals s_final ->
      eval_ctor_cases s_final
        (build_ctor_env (ctor_iface ctor) vals l (env_origin rho) (VInt 0%Z))
        (ctor_cases ctor) a l' s' ->
      eval_slotexpr s rho (SENew a None ses) l (VAddr l') s'

  (** E-CreatePayable *)
  | E_CreatePayable : forall s rho a ctor se_val ses l l' vals s_final sv s_v s',
      cmap a = Some ctor ->
      ctor_payable ctor = true ->
      eval_slotexpr_list s rho ses l vals s_final ->
      eval_slotexpr s_final rho se_val l sv s_v ->
      eval_ctor_cases s_v
        (build_ctor_env (ctor_iface ctor) vals l (env_origin rho) sv)
        (ctor_cases ctor) a l' s' ->
      eval_slotexpr s rho (SENew a (Some se_val) ses) l (VAddr l') s'

(** Evaluate a list of slot expressions, threading state *)
with eval_slotexpr_list : state -> env -> list slot_expr -> addr ->
                          list value -> state -> Prop :=
  | E_SlotListNil : forall s rho l,
      eval_slotexpr_list s rho [] l [] s
  | E_SlotListCons : forall s rho se rest l v s' vs s_final,
      eval_slotexpr s rho se l v s' ->
      eval_slotexpr_list s' rho rest l vs s_final ->
      eval_slotexpr_list s rho (se :: rest) l (v :: vs) s_final

(** Constructor Cases *)
with eval_ctor_cases : state -> env -> list ctor_case -> ident ->
                       addr -> state -> Prop :=
  | E_CtorCases : forall s rho cases id j l s',
      j < length cases ->
      eval_expr (TSUntimed s) rho (fst (nth j cases (EBool false, []))) dummy_loc (VBool true) ->
      (forall i, i <> j -> i < length cases ->
        eval_expr (TSUntimed s) rho (fst (nth i cases (EBool false, []))) dummy_loc (VBool false)) ->
      eval_creates s rho (snd (nth j cases (EBool false, []))) id l s' ->
      eval_ctor_cases s rho cases id l s'

(** Creates *)
with eval_creates : state -> env -> list create -> ident ->
                    addr -> state -> Prop :=
  | E_Creates : forall s rho creates id s_n bindings,
      eval_create_list s rho creates dummy_loc s_n bindings ->
      eval_creates s rho creates id (state_next s_n)
                   (state_alloc s_n id (list_to_map bindings))

with eval_create_list : state -> env -> list create -> addr ->
                        state -> list (ident * value) -> Prop :=
  | E_CreateListNil : forall s rho l,
      eval_create_list s rho [] l s []
  | E_CreateListCons : forall s rho st x se rest l v s' s'' bs,
      eval_slotexpr s rho se l v s' ->
      eval_create_list s' rho rest l s'' bs ->
      eval_create_list s rho ((st, x, se) :: rest) l s'' ((x, v) :: bs).

(* ================================================================= *)
(** ** Semantics of Updates *)
(** Judgment: s ; ρ ; updates ⇓_ℓ s' *)

Inductive eval_update_exprs : state -> env -> list update -> addr ->
                         list value -> state -> Prop :=
  | E_UpdExprsNil : forall s rho l,
      eval_update_exprs s rho [] l [] s
  | E_UpdExprsCons : forall s rho r se rest l v s' vs s_final,
      eval_slotexpr s rho se l v s' ->
      eval_update_exprs s' rho rest l vs s_final ->
      eval_update_exprs s rho ((r, se) :: rest) l (v :: vs) s_final.

Inductive eval_updates : state -> env -> list update -> addr -> state -> Prop :=
  | E_Updates : forall s rho updates l vals s_n s',
      eval_update_exprs s rho updates l vals s_n ->
      eval_update_inserts s_n rho updates vals l s' ->
      eval_updates s rho updates l s'.

(* ================================================================= *)
(** ** Semantics of Transition Cases *)
(** Judgment: s ; ρ ; tcases ⇓_ℓ (v, s') *)

(** Accessors for trans_case components *)
Definition tc_cond (tc : trans_case) : expr := fst (fst tc).
Definition tc_updates (tc : trans_case) : list update := snd (fst tc).
Definition tc_return (tc : trans_case) : expr := snd tc.

Definition tc_default : trans_case := (EBool false, [], EBool false).

Inductive eval_trans_cases : state -> env -> list trans_case -> addr ->
                             value -> state -> Prop :=
  | E_TransCases : forall s rho cases j l v s',
      j < length cases ->
      eval_expr (TSUntimed s) rho (tc_cond (nth j cases tc_default)) l (VBool true) ->
      (forall i, i <> j -> i < length cases ->
        eval_expr (TSUntimed s) rho (tc_cond (nth i cases tc_default)) l (VBool false)) ->
      eval_updates s rho (tc_updates (nth j cases tc_default)) l s' ->
      eval_expr (TSTimed s s') rho (tc_return (nth j cases tc_default)) l v ->
      eval_trans_cases s rho cases l v s'.

(* ================================================================= *)
(** ** Semantics of Constructors *)

Inductive eval_constructor : state -> env -> constructor -> ident ->
                             addr -> state -> Prop :=
  | E_Ctor : forall s rho ctor id l s',
      Forall (fun pre => eval_expr (TSUntimed s) rho pre dummy_loc (VBool true))
             (ctor_iff ctor) ->
      eval_ctor_cases s rho (ctor_cases ctor) id l s' ->
      eval_constructor s rho ctor id l s'.

(* ================================================================= *)
(** ** Semantics of Transitions *)

Inductive eval_transition : state -> env -> transition -> addr ->
                            value -> state -> Prop :=
  | E_Trans : forall s rho tr l v s',
      Forall (fun pre => eval_expr (TSUntimed s) rho pre l (VBool true))
             (trans_iff tr) ->
      eval_trans_cases s rho (trans_cases tr) l v s' ->
      eval_transition s rho tr l v s'.

End EvalCmap.

(* ================================================================= *)
(** ** State Transitions *)

Inductive step_cnstr (Σ : contract_env) : ident -> state -> addr -> state -> Prop :=
  | E_Step_Cnstr : forall a s l s' rho ctor,
      Σ_cnstr Σ a = Some ctor ->
      eval_constructor (Σ_cnstr Σ) s rho ctor a l s' ->
      step_cnstr Σ a s l s'.

Inductive step_trans (Σ : contract_env) : ident -> state -> addr -> state -> Prop :=
  | E_Step_Trans : forall a s l s' rho tr v transs,
      Σ_trans Σ a = Some transs ->
      In tr transs ->
      eval_transition (Σ_cnstr Σ) s rho tr l v s' ->
      step_trans Σ a s l s'.

Definition step (Σ : contract_env) (s s' : state) : Prop :=
  (exists a l, step_cnstr Σ a s l s') \/
  (exists a l, step_trans Σ a s l s').

Inductive steps (Σ : contract_env) : state -> state -> Prop :=
  | Steps_refl : forall s, steps Σ s s
  | Steps_step : forall s1 s2 s3,
      step Σ s1 s2 -> steps Σ s2 s3 -> steps Σ s1 s3.

Definition possible (Σ : contract_env) (s : state) : Prop :=
  steps Σ state_empty s.

(* ================================================================= *)
(** ** Useful Tactics and Induction Schemes *)

Ltac inv H := inversion H; subst; clear H.

(** Mutual induction schemes for eval_ref / eval_expr *)
Scheme eval_ref_ind2 := Induction for eval_ref Sort Prop
  with eval_expr_ind2 := Induction for eval_expr Sort Prop.
Combined Scheme eval_ref_expr_mutind from eval_ref_ind2, eval_expr_ind2.

(** No mutual induction needed for eval_mapexpr — it is now a simple inductive. *)

(** Mutual induction schemes for eval_slotexpr family *)
Scheme eval_slotexpr_ind2 := Induction for eval_slotexpr Sort Prop
  with eval_slotexpr_list_ind2 := Induction for eval_slotexpr_list Sort Prop
  with eval_ctor_cases_ind2 := Induction for eval_ctor_cases Sort Prop
  with eval_creates_ind2 := Induction for eval_creates Sort Prop
  with eval_create_list_ind2 := Induction for eval_create_list Sort Prop.

(** eval_updates, eval_update_exprs, and eval_update_inserts are
    no longer mutual — standard induction suffices. *)

(* ================================================================= *)
(** ** Timed State Inclusion and State Inclusion Helpers *)

(** Timed state inclusion *)
Definition ts_incl (ts ts' : timed_state) : Prop :=
  match ts, ts' with
  | TSUntimed s, TSUntimed s' => state_incl s s'
  | TSTimed sp spo, TSTimed sp' spo' =>
      state_incl sp sp' /\ state_incl spo spo'
  | _, _ => False
  end.

(** Helpers for state_incl *)
Lemma state_incl_dom : forall s s' l,
  state_incl s s' -> state_dom s l -> state_dom s' l.
Proof.
  intros s s' l Hincl [ls Hls].
  exists ls. apply Hincl. exact Hls.
Qed.

Lemma state_incl_type : forall s s' l a,
  state_incl s s' -> state_type s l = Some a -> state_type s' l = Some a.
Proof.
  intros s s' l a Hincl Htype.
  unfold state_type in *.
  destruct (s l) eqn:E; [|discriminate].
  rewrite (Hincl l l0 E). exact Htype.
Qed.

Lemma state_incl_var : forall s s' l x v,
  state_incl s s' -> state_dom s l -> state_var s l x = Some v -> state_var s' l x = Some v.
Proof.
  intros s s' l x v Hincl [ls Hls] Hvar.
  unfold state_var in *.
  rewrite Hls in Hvar.
  rewrite (Hincl l ls Hls). exact Hvar.
Qed.

Lemma state_incl_var_eq : forall s s' l x,
  state_incl s s' -> state_dom s l -> state_var s' l x = state_var s l x.
Proof.
  intros s s' l x Hincl [ls Hls].
  unfold state_var.
  rewrite Hls. rewrite (Hincl l ls Hls). reflexivity.
Qed.

Lemma state_incl_var_dom : forall s s' l x,
  state_incl s s' -> state_dom s l ->
  (state_var_dom s l x <-> state_var_dom s' l x).
Proof.
  intros s s' l x Hincl Hdom. split.
  - intros [v Hv]. exists v. eapply state_incl_var; eauto.
  - intros [v Hv]. unfold state_var_dom.
    rewrite <- (state_incl_var_eq s s' l x Hincl Hdom). eauto.
Qed.

Lemma state_incl_var_force : forall s s' l x,
  state_incl s s' -> state_dom s l ->
  state_var_force s' l x = state_var_force s l x.
Proof.
  intros s s' l x Hincl Hdom.
  unfold state_var_force.
  rewrite (state_incl_var_eq s s' l x Hincl Hdom). reflexivity.
Qed.

(* ================================================================= *)
(** ** Determinism of Pointer Semantics *)

(** eval_env determinism *)
Lemma eval_env_determinism :
  forall rho ev l v1 v2,
    eval_env rho ev l v1 -> eval_env rho ev l v2 -> v1 = v2.
Proof.
  intros rho ev l v1 v2 H1 H2.
  inv H1; inv H2; congruence.
Qed.

(** Determinism tactic for stepping through inversion + IH application *)
Ltac det_step :=
  match goal with
  | [H : VAddr _ = VAddr _ |- _] => inv H
  | [H : VInt _ = VInt _ |- _] => inv H
  | [H : VBool _ = VBool _ |- _] => inv H
  | [H1 : eval_env ?rho ?ev ?l ?v1, H2 : eval_env ?rho ?ev ?l ?v2 |- _] =>
    let E := fresh in assert (E := eval_env_determinism _ _ _ _ _ H1 H2); clear H2; subst
  | [IH : forall v' tp', eval_ref ?ts ?rho ?r ?l v' tp' -> _ = v' /\ _ = tp',
     H : eval_ref ?ts ?rho ?r ?l _ _ |- _] =>
    let P := fresh in let Q := fresh in
    destruct (IH _ _ H) as [P Q]; clear H; try inv P; try subst
  | [IH : forall v', eval_expr ?ts ?rho ?e ?l v' -> _ = v',
     H : eval_expr ?ts ?rho ?e ?l _ |- _] =>
    let P := fresh in pose proof (IH _ H) as P; clear H; subst
  | [H : eval_expr _ _ (ERef _) _ _ |- _] => inv H
  | [H : eval_expr _ _ (EAddr _) _ _ |- _] => inv H
  end.

(** Determinism of Reference and Expression Evaluation *)
Lemma ref_expr_det_combined :
  (forall ts rho r l v tp,
    eval_ref ts rho r l v tp ->
    forall v' tp', eval_ref ts rho r l v' tp' -> v = v' /\ tp = tp') /\
  (forall ts rho e l v,
    eval_expr ts rho e l v ->
    forall v', eval_expr ts rho e l v' -> v = v').
Proof.
  apply eval_ref_expr_mutind; intros;
    match goal with
    | [H : eval_ref _ _ _ _ _ _ |- _] => inv H
    | [H : eval_expr _ _ _ _ _ |- _] => inv H
    end;
    try (split; congruence);
    try congruence;
    repeat det_step;
    try (split; congruence);
    try congruence;
    try discriminate;
    try contradiction;
    auto.
Qed.

Lemma expr_determinism :
  forall ts rho e l v1 v2,
    eval_expr ts rho e l v1 ->
    eval_expr ts rho e l v2 ->
    v1 = v2.
Proof. intros. eapply (proj2 ref_expr_det_combined); eauto. Qed.

Lemma ref_determinism :
  forall ts rho r l v1 tp1 v2 tp2,
    eval_ref ts rho r l v1 tp1 ->
    eval_ref ts rho r l v2 tp2 ->
    v1 = v2 /\ tp1 = tp2.
Proof. intros. eapply (proj1 ref_expr_det_combined); eauto. Qed.

(** Determinism of Forall2 with eval_expr *)
Lemma forall2_expr_det :
  forall ts rho l (bindings : list (expr * map_expr)) keys1 keys2,
    Forall2 (fun p k => eval_expr ts rho (fst p) l k) bindings keys1 ->
    Forall2 (fun p k => eval_expr ts rho (fst p) l k) bindings keys2 ->
    keys1 = keys2.
Proof.
  intros ts rho l bindings keys1 keys2 H1 H2.
  revert keys2 H2. induction H1; intros keys2 H2; inv H2; auto.
  f_equal; [eapply expr_determinism; eauto | auto].
Qed.

(** Custom induction principle for eval_mapexpr that handles nested Forall2 *)
Lemma eval_mapexpr_ind_nested
  (P : timed_state -> env -> map_expr -> addr -> value -> Prop) :
  (forall ts rho e l v,
    eval_expr ts rho e l v -> P ts rho (MExp e) l v) ->
  (forall ts rho bindings mu l keys vals f,
    Forall2 (fun p k => eval_expr ts rho (fst p) l k) bindings keys ->
    Forall2 (fun p v => eval_mapexpr ts rho (snd p) l v) bindings vals ->
    Forall2 (fun p v => P ts rho (snd p) l v) bindings vals ->
    build_map_from_bindings keys vals mu = Some f ->
    P ts rho (MMap bindings mu) l f) ->
  (forall ts rho r bindings mu l f_old f_new tp keys vals,
    eval_ref ts rho r l f_old tp ->
    Forall2 (fun p k => eval_expr ts rho (fst p) l k) bindings keys ->
    Forall2 (fun p v => eval_mapexpr ts rho (snd p) l v) bindings vals ->
    Forall2 (fun p v => P ts rho (snd p) l v) bindings vals ->
    update_map_from_bindings keys vals f_old mu = Some f_new ->
    P ts rho (MMapUpd r bindings mu) l f_new) ->
  forall ts rho m l v, eval_mapexpr ts rho m l v -> P ts rho m l v.
Proof.
  intros HExp HMapping HMappingUpd.
  fix IH 6.
  intros ts rho m l v Hm.
  destruct Hm as [? ? ? ? ? He
                  | ? ? ? ? ? ? ? ? Hk Hv Hb
                  | ? ? ? ? ? ? ? ? ? ? ? Hr Hk Hv Hu].
  - apply HExp. exact He.
  - apply HMapping with (keys := keys) (vals := vals); auto.
    clear Hk Hb. induction Hv; constructor; auto.
  - eapply HMappingUpd; eauto.
    clear Hk Hr Hu. induction Hv; constructor; auto.
Defined.

(** Determinism of Mapping Expression Evaluation *)
Lemma forall2_mapexpr_vals_det :
  forall ts rho l (bindings : list (expr * map_expr)) vals1 vals2,
    Forall2 (fun p v => eval_mapexpr ts rho (snd p) l v) bindings vals2 ->
    Forall2 (fun p v => forall v2, eval_mapexpr ts rho (snd p) l v2 -> v = v2)
      bindings vals1 ->
    vals1 = vals2.
Proof.
  intros ts rho l bindings vals1 vals2 Hv2 HIH.
  revert vals2 Hv2. induction HIH; intros vals2 Hv2; inv Hv2; auto.
  f_equal; eauto.
Qed.

Lemma mapexpr_determinism :
  forall ts rho m l v1 v2,
    eval_mapexpr ts rho m l v1 ->
    eval_mapexpr ts rho m l v2 ->
    v1 = v2.
Proof.
  intros ts rho m l v1 v2 H1.
  revert v2. induction H1 using eval_mapexpr_ind_nested; intros v2 Hm2; inv Hm2.
  - eapply expr_determinism; eauto.
  - assert (keys = keys0) by (eapply forall2_expr_det; eauto); subst.
    assert (vals = vals0) by (eapply forall2_mapexpr_vals_det; eauto).
    subst. congruence.
  - match goal with
    | [Hr1 : eval_ref _ _ ?r _ _ _, Hr2 : eval_ref _ _ ?r _ _ _ |- _] =>
      destruct (ref_determinism _ _ _ _ _ _ _ _ Hr1 Hr2); subst
    end.
    assert (keys = keys0) by (eapply forall2_expr_det; eauto); subst.
    assert (vals = vals0) by (eapply forall2_mapexpr_vals_det; eauto).
    subst. congruence.
Qed.

(** Determinism of Value Insertion *)
Lemma insert_determinism :
  forall s rho r v l s1 s2,
    eval_insert s rho r v l s1 ->
    eval_insert s rho r v l s2 ->
    s1 = s2.
Proof.
  intros s rho r v l s1 s2 H1 H2.
  inv H1; inv H2; try congruence.
  match goal with
  | [Ha : eval_ref _ _ _ _ (VAddr ?l1) _, Hb : eval_ref _ _ _ _ (VAddr ?l2) _ |- _] =>
    destruct (ref_determinism _ _ _ _ _ _ _ _ Ha Hb) as [Heq _]; inv Heq; congruence
  end.
Qed.

(** Determinism of Slot Expressions — proved with mutual Fixpoint. *)

Section SlotexprDet.

Fixpoint slotexpr_det cmap s rho se l v s'
  (H : eval_slotexpr cmap s rho se l v s') {struct H} :
  forall v' s'', eval_slotexpr cmap s rho se l v' s'' -> v = v' /\ s' = s''
with slotexpr_list_det cmap s rho ses l vals s_final
  (H : eval_slotexpr_list cmap s rho ses l vals s_final) {struct H} :
  forall vals' s_final', eval_slotexpr_list cmap s rho ses l vals' s_final' ->
  vals = vals' /\ s_final = s_final'
with ctor_cases_det cmap s rho cases id l s'
  (H : eval_ctor_cases cmap s rho cases id l s') {struct H} :
  forall l' s'', eval_ctor_cases cmap s rho cases id l' s'' -> l = l' /\ s' = s''
with creates_det cmap s rho creates id l s'
  (H : eval_creates cmap s rho creates id l s') {struct H} :
  forall l' s'', eval_creates cmap s rho creates id l' s'' -> l = l' /\ s' = s''
with create_list_det cmap s rho creates l s' bindings
  (H : eval_create_list cmap s rho creates l s' bindings) {struct H} :
  forall s'' bindings', eval_create_list cmap s rho creates l s'' bindings' ->
  s' = s'' /\ bindings = bindings'.
Proof.
  all: destruct H; intros;
    match goal with [Hx : _ |- _] =>
      inversion Hx; subst; clear Hx end.
  (* E_SlotMap *)
  all: try (split; [eapply mapexpr_determinism; eauto | auto]; fail).
  (* E_SlotRef *)
  all: try (match goal with
    | [H1 : eval_ref _ _ ?r ?l _ _, H2 : eval_ref _ _ ?r ?l _ _ |- _] =>
      destruct (ref_determinism _ _ _ _ _ _ _ _ H1 H2); auto
    end; fail).
  (* E_SlotAddr *)
  all: try (match goal with
    | [IH : forall v' s'', eval_slotexpr _ _ _ ?se ?l v' s'' -> _,
       H2 : eval_slotexpr _ _ _ ?se ?l _ _ |- _] =>
      eapply IH; eauto
    end; fail).
  (* payable/non-payable mismatch *)
  all: try discriminate.
  (* ctor unification *)
  all: try (match goal with
    | [Hcm1 : ?cm ?a = Some ?c1, Hcm2 : ?cm ?a = Some ?c2 |- _] =>
      let Heq := fresh in assert (Heq : c1 = c2) by congruence; subst
    end).
  (* E_Create: chain IH for list, then ctor_cases_det *)
  all: try (match goal with
    | [IHl : forall vals' s_final', eval_slotexpr_list _ _ _ ?ses _ vals' s_final' -> _ /\ _,
       Hl : eval_slotexpr_list _ _ _ ?ses _ _ _ |- _] =>
      destruct (IHl _ _ Hl); subst
    end).
  (* E_Create (non-payable): ctor_cases_det *)
  all: try (match goal with
    | [Hcc : eval_ctor_cases _ _ _ _ _ ?l2 ?s2 |- _ = ?l2 /\ _ = ?s2] =>
      eapply ctor_cases_det; eauto
    end; fail).
  (* E_CreatePayable: unify slotexpr for value, then ctor_cases_det *)
  all: try (match goal with
    | [IHse : forall v' s'', eval_slotexpr _ _ _ _ _ v' s'' -> _ /\ _,
       Hse : eval_slotexpr _ _ _ _ _ _ _,
       Hcc : eval_ctor_cases _ _ _ _ _ _ _ |- _] =>
      destruct (IHse _ _ Hse); subst;
      eapply ctor_cases_det; eauto
    end; fail).
  (* slotexpr_list: nil *)
  all: try (auto; fail).
  (* slotexpr_list: cons *)
  all: try (match goal with
    | [IHse : forall v' s'', eval_slotexpr _ _ _ _ _ v' s'' -> _ /\ _,
       IHtl : forall vals' s_final', eval_slotexpr_list _ _ _ _ _ vals' s_final' -> _ /\ _,
       Hse : eval_slotexpr _ _ _ _ _ _ _,
       Htl : eval_slotexpr_list _ _ _ _ _ _ _ |- _] =>
      destruct (IHse _ _ Hse); subst;
      destruct (IHtl _ _ Htl); subst; auto
    end; fail).
  all: try congruence.
  (* ctor_cases and creates remaining *)
  all: repeat match goal with
    | [H1 : eval_create_list _ _ _ _ _ _ _, H2 : eval_create_list _ _ _ _ _ _ _ |- _] =>
      destruct (create_list_det _ _ _ _ _ _ _ H1 _ _ H2); clear H2; subst
    end.
  (* ctor_cases: prove j = j0 *)
  all: try (match goal with
    | [He1 : eval_expr _ _ (fst (nth ?j1 ?cases _)) _ (VBool true),
       He2 : eval_expr _ _ (fst (nth ?j2 ?cases _)) _ (VBool true),
       Hf2 : forall i, i <> ?j2 -> i < _ -> eval_expr _ _ (fst (nth i ?cases _)) _ (VBool false),
       Hlt1 : ?j1 < _ |- _] =>
      assert (j1 = j2) by (
        destruct (Nat.eq_dec j1 j2); [auto|];
        exfalso;
        pose proof (expr_determinism _ _ _ _ _ _ He1 (Hf2 j1 n Hlt1));
        discriminate);
      subst; eapply creates_det; eauto
    end; fail).
  (* creates: l = l' by minimality *)
  all: try (match goal with
    | [Hnd1 : ~ state_dom _ ?l1,
       Hmin1 : forall l'', l'' < ?l1 -> state_dom _ l'',
       Hnd2 : ~ state_dom _ ?l2,
       Hmin2 : forall l'', l'' < ?l2 -> state_dom _ l'' |- _] =>
      assert (l1 = l2) by (
        destruct (Nat.lt_trichotomy l1 l2) as [?|[?|?]]; auto;
        [exfalso; apply Hnd1; apply Hmin2; auto
        |exfalso; apply Hnd2; apply Hmin1; auto]);
      subst; auto
    end; fail).
  (* create_list: cons *)
  all: try (match goal with
    | [IHse : forall v' s'', eval_slotexpr _ _ _ _ _ v' s'' -> _ /\ _,
       IHtl : forall s'' bindings', eval_create_list _ _ _ _ _ s'' bindings' -> _ /\ _,
       Hse : eval_slotexpr _ _ _ _ _ _ _,
       Htl : eval_create_list _ _ _ _ _ _ _ |- _] =>
      destruct (IHse _ _ Hse); subst;
      destruct (IHtl _ _ Htl); subst; auto
    end; fail).
  (* Fallback *)
  all: try (eapply slotexpr_det; eauto; fail).
  all: repeat match goal with
    | [H1 : eval_slotexpr _ _ _ _ _ _ _, H2 : eval_slotexpr _ _ _ _ _ _ _ |- _] =>
      destruct (slotexpr_det _ _ _ _ _ _ _ H1 _ _ H2); clear H2; subst
    | [H1 : eval_slotexpr_list _ _ _ _ _ _ _, H2 : eval_slotexpr_list _ _ _ _ _ _ _ |- _] =>
      destruct (slotexpr_list_det _ _ _ _ _ _ _ H1 _ _ H2); clear H2; subst
    | [H1 : eval_ctor_cases _ _ _ _ _ _ _, H2 : eval_ctor_cases _ _ _ _ _ _ _ |- _] =>
      destruct (ctor_cases_det _ _ _ _ _ _ _ H1 _ _ H2); clear H2; subst
    | [H1 : eval_creates _ _ _ _ _ _ _, H2 : eval_creates _ _ _ _ _ _ _ |- _] =>
      destruct (creates_det _ _ _ _ _ _ _ H1 _ _ H2); clear H2; subst
    | [H1 : eval_create_list _ _ _ _ _ _ _, H2 : eval_create_list _ _ _ _ _ _ _ |- _] =>
      destruct (create_list_det _ _ _ _ _ _ _ H1 _ _ H2); clear H2; subst
    end;
    try auto; try congruence; try (split; congruence); try (f_equal; congruence).
Defined.

Lemma slotexpr_determinism :
  forall cmap s rho se l v1 s1 v2 s2,
    eval_slotexpr cmap s rho se l v1 s1 ->
    eval_slotexpr cmap s rho se l v2 s2 ->
    v1 = v2 /\ s1 = s2.
Proof.
  intros. eapply slotexpr_det; eauto.
Qed.

(** Determinism of Update Inserts *)
Lemma update_inserts_det :
  forall s rho updates vals l s',
    eval_update_inserts s rho updates vals l s' ->
    forall s'', eval_update_inserts s rho updates vals l s'' -> s' = s''.
Proof.
  induction 1; intros s'' Hx; inversion Hx; subst; auto.
  match goal with [H1 : eval_insert ?s ?r ?ref ?v ?l _, H2 : eval_insert ?s ?r ?ref ?v ?l _ |- _] =>
    assert (E := insert_determinism _ _ _ _ _ _ _ H1 H2); subst end.
  eauto.
Qed.

(** Determinism of Update Exprs *)
Lemma update_exprs_det :
  forall cmap s rho updates l vals s_n,
    eval_update_exprs cmap s rho updates l vals s_n ->
    forall vals' s_n', eval_update_exprs cmap s rho updates l vals' s_n' ->
    vals = vals' /\ s_n = s_n'.
Proof.
  induction 1; intros vals' s_n' Hx; inversion Hx; subst; auto.
  match goal with [H1 : eval_slotexpr _ _ _ ?se _ _ _, H2 : eval_slotexpr _ _ _ ?se _ _ _ |- _] =>
    destruct (slotexpr_determinism _ _ _ _ _ _ _ _ _ H1 H2); subst end.
  match goal with [H2 : eval_update_exprs _ _ _ _ _ _ _ |- _] =>
    destruct (IHeval_update_exprs _ _ H2); subst end.
  auto.
Qed.

(** Determinism of Updates *)
Lemma updates_det :
  forall cmap s rho updates l s',
    eval_updates cmap s rho updates l s' ->
    forall s'', eval_updates cmap s rho updates l s'' -> s' = s''.
Proof.
  intros cmap s rho updates l s' H s'' Hx. inv H; inv Hx.
  match goal with [H1 : eval_update_exprs _ _ _ _ _ _ _, H2 : eval_update_exprs _ _ _ _ _ _ _ |- _] =>
    destruct (update_exprs_det _ _ _ _ _ _ _ H1 _ _ H2); subst end.
  eapply update_inserts_det; eauto.
Qed.

Lemma updates_determinism :
  forall cmap s rho upds l s1 s2,
    eval_updates cmap s rho upds l s1 ->
    eval_updates cmap s rho upds l s2 ->
    s1 = s2.
Proof. intros. eapply updates_det; eauto. Qed.

(** Determinism of Transition Cases *)
Lemma trans_cases_determinism :
  forall cmap s rho cases l v1 s1 v2 s2,
    eval_trans_cases cmap s rho cases l v1 s1 ->
    eval_trans_cases cmap s rho cases l v2 s2 ->
    v1 = v2 /\ s1 = s2.
Proof.
  intros. inv H; inv H0.
  assert (j = j0).
  { destruct (Nat.eq_dec j j0); auto. exfalso.
    match goal with
    | [Htrue : eval_expr _ _ (tc_cond (nth j _ _)) _ (VBool true),
       Hfalse : forall i, i <> j0 -> _ -> eval_expr _ _ (tc_cond (nth i _ _)) _ (VBool false),
       Hlt : j < length _ |- _] =>
      pose proof (expr_determinism _ _ _ _ _ _ Htrue (Hfalse j n Hlt)); discriminate
    end. }
  subst.
  match goal with
  | [Hu1 : eval_updates _ _ _ _ _ ?s1, Hu2 : eval_updates _ _ _ _ _ ?s2 |- _] =>
    assert (s1 = s2) by (eapply updates_determinism; eauto); subst
  end.
  split; auto. eapply expr_determinism; eauto.
Qed.

(** Determinism of Constructor Evaluation *)
Lemma constructor_determinism :
  forall cmap s rho ctor id l1 s1 l2 s2,
    eval_constructor cmap s rho ctor id l1 s1 ->
    eval_constructor cmap s rho ctor id l2 s2 ->
    l1 = l2 /\ s1 = s2.
Proof.
  intros. inv H; inv H0.
  eapply ctor_cases_det; eauto.
Qed.

(** Determinism of Transition Evaluation *)
Lemma transition_determinism :
  forall cmap s rho tr l v1 s1 v2 s2,
    eval_transition cmap s rho tr l v1 s1 ->
    eval_transition cmap s rho tr l v2 s2 ->
    v1 = v2 /\ s1 = s2.
Proof.
  intros. inv H; inv H0.
  eapply trans_cases_determinism; eauto.
Qed.

End SlotexprDet.

(* ================================================================= *)
(** ** Weakening of Storage for Pointer Semantics (Lemma 5.2) *)

Lemma sem_storage_weak_combined :
  (forall ts rho r l v tp,
    eval_ref ts rho r l v tp ->
    forall ts', ts_incl ts ts' -> eval_ref ts' rho r l v tp) /\
  (forall ts rho e l v,
    eval_expr ts rho e l v ->
    forall ts', ts_incl ts ts' -> eval_expr ts' rho e l v).
Proof.
  apply eval_ref_expr_mutind; intros; try (econstructor; eauto; fail).
  - (* E_Storage *) destruct ts' as [s'|]; [|contradiction].
    simpl in H. econstructor; eauto. eapply state_incl_var; eauto.
    unfold state_dom. unfold state_var in e. destruct (s l) eqn:E; [eexists; eauto|discriminate].
  - (* E_StoragePre *) destruct ts' as [|sp' spo']; [contradiction|].
    destruct H as [Hpre Hpost]. econstructor; eauto.
    eapply state_incl_var; eauto. unfold state_dom.
    unfold state_var in e. destruct (s_pre l) eqn:E; [eexists; eauto|discriminate].
  - (* E_StoragePost *) destruct ts' as [|sp' spo']; [contradiction|].
    destruct H as [Hpre Hpost]. econstructor; eauto.
    eapply state_incl_var; eauto. unfold state_dom.
    unfold state_var in e. destruct (s_post l) eqn:E; [eexists; eauto|discriminate].
  - (* E_Calldata *) destruct ts' as [s'|]; [|contradiction].
    eapply E_Calldata; eauto.
  - (* E_CalldataTimed *) destruct ts' as [|sp' spo']; [contradiction|].
    eapply E_CalldataTimed; eauto.
  - (* E_Field *) destruct ts' as [s'|]; [|contradiction]. simpl in H0.
    econstructor.
    + apply H. simpl. exact H0.
    + eapply state_incl_var; eauto. unfold state_dom.
      unfold state_var in e0. destruct (s l') eqn:E; [eexists; eauto|discriminate].
  - (* E_FieldPre *) destruct ts' as [|sp' spo']; [contradiction|].
    destruct H0 as [Hpre Hpost].
    eapply E_FieldPre.
    + apply H. simpl. split; auto.
    + eapply state_incl_var; eauto. unfold state_dom.
      unfold state_var in e0. destruct (s_pre l') eqn:E; [eexists; eauto|discriminate].
  - (* E_FieldPost *) destruct ts' as [|sp' spo']; [contradiction|].
    destruct H0 as [Hpre Hpost].
    eapply E_FieldPost.
    + apply H. simpl. split; auto.
    + eapply state_incl_var; eauto. unfold state_dom.
      unfold state_var in e0. destruct (s_post l') eqn:E; [eexists; eauto|discriminate].
Qed.

Lemma sem_storage_weak_expr :
  forall ts ts' rho e l v,
    ts_incl ts ts' ->
    eval_expr ts rho e l v ->
    eval_expr ts' rho e l v.
Proof. intros. eapply (proj2 sem_storage_weak_combined); eauto. Qed.

Lemma sem_storage_weak_ref :
  forall ts ts' rho r l v tp,
    ts_incl ts ts' ->
    eval_ref ts rho r l v tp ->
    eval_ref ts' rho r l v tp.
Proof. intros. eapply (proj1 sem_storage_weak_combined); eauto. Qed.

Lemma forall2_expr_weak :
  forall ts ts' rho l (bindings : list (expr * map_expr)) keys,
    ts_incl ts ts' ->
    Forall2 (fun p k => eval_expr ts rho (fst p) l k) bindings keys ->
    Forall2 (fun p k => eval_expr ts' rho (fst p) l k) bindings keys.
Proof.
  intros ts ts' rho l bindings keys Hincl H.
  induction H; constructor; auto. eapply sem_storage_weak_expr; eauto.
Qed.

Fixpoint sem_storage_weak_mapexpr ts ts' rho m l v
  (Hincl : ts_incl ts ts')
  (H : eval_mapexpr ts rho m l v) {struct H} :
  eval_mapexpr ts' rho m l v.
Proof.
  destruct H.
  - apply E_MExp. eapply sem_storage_weak_expr; eauto.
  - eapply E_Mapping; eauto.
    + eapply forall2_expr_weak; eauto.
    + clear H H1. induction H0; constructor; auto.
      eapply sem_storage_weak_mapexpr; eauto.
  - eapply E_MappingUpd; eauto.
    + eapply sem_storage_weak_ref; eauto.
    + eapply forall2_expr_weak; eauto.
    + clear H H0 H2. induction H1; constructor; auto.
      eapply sem_storage_weak_mapexpr; eauto.
Defined.

(* ================================================================= *)
(** ** Cmap Monotonicity *)

Combined Scheme eval_slotexpr_mutind from
  eval_slotexpr_ind2, eval_slotexpr_list_ind2,
  eval_ctor_cases_ind2, eval_creates_ind2, eval_create_list_ind2.

(** If an evaluation holds with [cmap1], and [cmap1] is included in [cmap2],
    then the same evaluation holds with [cmap2]. *)

Lemma cmap_mono_slotexpr_combined : forall cmap1,
  (forall s rho se l v s',
    eval_slotexpr cmap1 s rho se l v s' ->
    forall cmap2, includes cmap1 cmap2 ->
    eval_slotexpr cmap2 s rho se l v s') /\
  (forall s rho ses l vals s',
    eval_slotexpr_list cmap1 s rho ses l vals s' ->
    forall cmap2, includes cmap1 cmap2 ->
    eval_slotexpr_list cmap2 s rho ses l vals s') /\
  (forall s rho cases id l s',
    eval_ctor_cases cmap1 s rho cases id l s' ->
    forall cmap2, includes cmap1 cmap2 ->
    eval_ctor_cases cmap2 s rho cases id l s') /\
  (forall s rho creates id l s',
    eval_creates cmap1 s rho creates id l s' ->
    forall cmap2, includes cmap1 cmap2 ->
    eval_creates cmap2 s rho creates id l s') /\
  (forall s rho creates l s' bindings,
    eval_create_list cmap1 s rho creates l s' bindings ->
    forall cmap2, includes cmap1 cmap2 ->
    eval_create_list cmap2 s rho creates l s' bindings).
Proof.
  intro. apply eval_slotexpr_mutind; intros; try (econstructor; eauto).
Qed.

Lemma cmap_mono_update_exprs :
  forall cmap1 s rho updates l vals s',
    eval_update_exprs cmap1 s rho updates l vals s' ->
    forall cmap2, includes cmap1 cmap2 ->
    eval_update_exprs cmap2 s rho updates l vals s'.
Proof.
  induction 1; intros; econstructor; eauto.
  eapply (proj1 (cmap_mono_slotexpr_combined _)); eauto.
Qed.

Lemma cmap_mono_updates :
  forall cmap1 s rho updates l s',
    eval_updates cmap1 s rho updates l s' ->
    forall cmap2, includes cmap1 cmap2 ->
    eval_updates cmap2 s rho updates l s'.
Proof.
  intros. inv H. econstructor; eauto.
  eapply cmap_mono_update_exprs; eauto.
Qed.

Lemma cmap_mono_trans_cases :
  forall cmap1 s rho cases l v s',
    eval_trans_cases cmap1 s rho cases l v s' ->
    forall cmap2, includes cmap1 cmap2 ->
    eval_trans_cases cmap2 s rho cases l v s'.
Proof.
  intros. inv H. econstructor; eauto.
  eapply cmap_mono_updates; eauto.
Qed.
