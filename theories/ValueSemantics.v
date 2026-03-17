(** * Value Semantics — Semantic Domains
    Formalizes Section 10.1 of the tech report: the semantic domains
    of types are defined by recursion on types, mapping Act types
    to actual Rocq types.

    ⟦β⟧ and ⟦μ⟧ are defined by structural recursion on types.
    ⟦σ⟧_Σ is defined by recursion on the strictly decreasing
    measure len(Σ, σ), bounded by the size of Σ. *)

From Stdlib Require Import String ZArith List Bool PeanoNat Lia.
From Act Require Import Maps Syntax Domains Semantics ValueTyping Typing TypingT.
Import ListNotations.

(* ================================================================= *)
(** ** Semantic Domain of Base Types — ⟦β⟧ *)

Definition sem_base (bt : base_type) : Type :=
  match bt with
  | TInt it => { n : Z | in_range it n }
  | TBool => bool
  | TAddress => nat
  end.

(* ================================================================= *)
(** ** Semantic Domain of Mapping Types — ⟦μ⟧ *)

Fixpoint sem_mapping (mu : mapping_type) : Type :=
  match mu with
  | MBase bt => sem_base bt
  | MMapping bt mu' => sem_base bt -> sem_mapping mu'
  end.

(* ================================================================= *)
(** ** Semantic Domains of Slot Types — ⟦σ⟧_Σ

    Internally defined using a depth parameter [n] that bounds
    the nesting of contract references. The top-level definitions
    compute the depth from Σ (as [length (Σ_storage_list Σ)]),
    so the depth does not appear in the public interface. *)

Definition Σ_storage_or_nil (Σ : contract_env) (a : ident) : storage_layout :=
  match Σ_storage Σ a with
  | Some layout => layout
  | None => []
  end.

(** Layout domain, parameterized by the slot domain function.
    Used by both [sem_slot_aux] and [sem_layout_aux] so their
    types are definitionally equal. *)
Fixpoint sem_layout_gen (slot_dom : slot_type -> Type)
    (layout : storage_layout) : Type :=
  match layout with
  | [] => unit
  | (_, st) :: rest => prod (slot_dom st) (sem_layout_gen slot_dom rest)
  end.

(** Depth-indexed version (internal). *)
Fixpoint sem_slot_aux (n : nat) (Σ : contract_env) (st : slot_type) : Type :=
  match st with
  | SMapping mu => sem_mapping mu
  | SAbi (ABase bt) => sem_base bt
  | SAbi (AContractAddr a) =>
      match n with
      | 0 => Empty_set
      | S n' => prod nat (sem_layout_gen (sem_slot_aux n' Σ) (Σ_storage_or_nil Σ a))
      end
  | SContract a =>
      match n with
      | 0 => Empty_set
      | S n' => prod nat (sem_layout_gen (sem_slot_aux n' Σ) (Σ_storage_or_nil Σ a))
      end
  end.

Definition sem_layout_aux (n : nat) (Σ : contract_env)
    (layout : storage_layout) : Type :=
  sem_layout_gen (sem_slot_aux n Σ) layout.

(** The depth of Σ: an upper bound on the nesting of contract
    references in any well-founded Σ. *)
Definition Σ_depth (Σ : contract_env) : nat :=
  length (Σ_storage_list Σ).

(* ================================================================= *)
(** ** Public Definitions — no depth parameter *)

(** ⟦σ⟧_Σ *)
Definition sem_slot (Σ : contract_env) (st : slot_type) : Type :=
  sem_slot_aux (Σ_depth Σ) Σ st.

(** ⟦C⟧_Σ — semantic domain of a storage layout *)
Definition sem_layout (Σ : contract_env) (layout : storage_layout) : Type :=
  sem_layout_aux (Σ_depth Σ) Σ layout.

(** ⟦α⟧_Σ — semantic domain of ABI types *)
Definition sem_abi (Σ : contract_env) (alpha : abi_type) : Type :=
  sem_slot Σ (SAbi alpha).

(** ⟦σ⟧^t_Σ — timed semantic domain of slot types *)
Definition sem_slot_timed (Σ : contract_env)
    (st : slot_type) (t : time_tag) : Type :=
  match t with
  | TagU => sem_slot Σ st
  | TagT => sem_slot Σ st * sem_slot Σ st
  end.

(** ⟦?Id⟧_Σ — depth-indexed *)
Definition sem_opt_id_aux (n : nat) (Σ : contract_env) (oid : opt_id) : Type :=
  match oid with
  | ONone => unit
  | OSome a => sem_slot_aux n Σ (SContract a)
  end.

(** ⟦?Id⟧^t_Σ — depth-indexed timed version *)
Definition sem_opt_id_timed_aux (n : nat) (Σ : contract_env)
    (oid : opt_id) (t : time_tag) : Type :=
  match t with
  | TagU => sem_opt_id_aux n Σ oid
  | TagT => sem_opt_id_aux n Σ oid * sem_opt_id_aux n Σ oid
  end.

(** ⟦?Id⟧_Σ — public *)
Definition sem_opt_id (Σ : contract_env) (oid : opt_id) : Type :=
  sem_opt_id_aux (Σ_depth Σ) Σ oid.

(** ⟦?Id⟧^t_Σ — public timed version *)
Definition sem_opt_id_timed (Σ : contract_env)
    (oid : opt_id) (t : time_tag) : Type :=
  sem_opt_id_timed_aux (Σ_depth Σ) Σ oid t.

(** ⟦I⟧_Σ — semantic domain of interface fields (depth-indexed) *)
Fixpoint sem_iface_fields_aux (n : nat) (Σ : contract_env)
    (iface : interface) : Type :=
  match iface with
  | [] => unit
  | (_, alpha) :: rest =>
      sem_slot_aux n Σ (SAbi alpha) * sem_iface_fields_aux n Σ rest
  end.

(** ⟦I⟧_Σ — depth-indexed: fields × (caller, origin, callvalue)
    callvalue is stored as sem_base (TInt (UintT 256)) = {n : Z | in_range (UintT 256) n}
    to match the typing rule T_Callvalue which assigns type uint256. *)
Definition sem_iface_aux (n : nat) (Σ : contract_env)
    (iface : interface) : Type :=
  sem_iface_fields_aux n Σ iface * (nat * nat * sem_base (TInt (UintT 256))).

(** ⟦I⟧_Σ — public *)
Definition sem_iface (Σ : contract_env)
    (iface : interface) : Type :=
  sem_iface_aux (Σ_depth Σ) Σ iface.

(* ================================================================= *)
(** ** Default Semantic Values *)

(** Default semantic values require that 0 is in range for integer types.
    This holds for all int types used in practice (bitwidth > 0). *)

Lemma zero_in_range_unbounded : in_range IntUnbounded 0%Z.
Proof. exact I. Qed.

Lemma zero_in_range_uint : forall m, in_range (UintT m) 0%Z.
Proof.
  intro m. simpl. split.
  - lia.
  - assert (0 < Z.pow 2 (Z.of_nat m))%Z.
    { apply Z.pow_pos_nonneg; lia. }
    lia.
Qed.

Lemma zero_in_range_int : forall m, (m > 0)%nat -> in_range (IntT m) 0%Z.
Proof.
  intros m Hm. simpl. split.
  - assert (0 <= Z.pow 2 (Z.of_nat m - 1))%Z.
    { apply Z.pow_nonneg. lia. }
    lia.
  - assert (0 < Z.pow 2 (Z.of_nat m - 1))%Z.
    { apply Z.pow_pos_nonneg; lia. }
    lia.
Qed.

(** Well-formedness of int types: 0 is in the range.
    This excludes pathological types like [IntT 0]. *)
Definition wf_int_type (it : int_type) : Prop :=
  in_range it 0%Z.

(* ================================================================= *)
(** ** Decidable Equality on Base Semantic Values *)

Definition sem_base_eqb (bt : base_type)
    : sem_base bt -> sem_base bt -> bool :=
  match bt return sem_base bt -> sem_base bt -> bool with
  | TInt _ => fun x y => Z.eqb (proj1_sig x) (proj1_sig y)
  | TBool => Bool.eqb
  | TAddress => Nat.eqb
  end.

(* ================================================================= *)
(** ** Depth Weakening

    Accessing a field of a contract at depth [S n] yields a value at
    depth [n]. To maintain a uniform depth across denotation functions,
    we coerce from depth [n] to depth [S n]. For non-contract types
    this is the identity; for contract types it recursively weakens
    each field. *)

Fixpoint sem_layout_gen_map
    (f g : slot_type -> Type)
    (w : forall st, f st -> g st)
    (layout : storage_layout)
    : sem_layout_gen f layout -> sem_layout_gen g layout :=
  match layout with
  | [] => id
  | (_, st) :: rest => fun '(x, xs) =>
      (w st x, sem_layout_gen_map f g w rest xs)
  end.

Fixpoint sem_slot_weaken (n : nat) (Σ : contract_env) (st : slot_type)
    {struct n} : sem_slot_aux n Σ st -> sem_slot_aux (S n) Σ st.
Proof.
  destruct n as [|n']; destruct st as [mu | [bt | a] | a]; simpl;
    try exact id; try exact (fun v => match v : Empty_set with end).
  - intros [addr fields]. exact (addr,
      sem_layout_gen_map _ _ (sem_slot_weaken n' Σ) _ fields).
  - intros [addr fields]. exact (addr,
      sem_layout_gen_map _ _ (sem_slot_weaken n' Σ) _ fields).
Defined.

(* ================================================================= *)
(** ** Layout Lookup — project a field from a contract record *)

Definition Some_inj {A : Type} {a b : A} (H : Some a = Some b) : a = b :=
  match H in _ = y return match y with Some b' => a = b' | None => True end with
  | eq_refl => eq_refl
  end.

Fixpoint sem_layout_lookup (n : nat) (Σ : contract_env)
    (layout : storage_layout) (x : ident) (sty : slot_type)
    {struct layout}
    : alist_lookup layout x = Some sty ->
      sem_layout_aux n Σ layout -> sem_slot_aux n Σ sty :=
  match layout as l
    return alist_lookup l x = Some sty ->
           sem_layout_aux n Σ l -> sem_slot_aux n Σ sty
  with
  | [] => fun H _ =>
      match @eq_ind _ (None (A:=slot_type)) (fun o =>
        match o with Some _ => False | None => True end) I _ H
      with end
  | (k, st') :: rest => fun H fields =>
      match String.eqb k x as b
        return (if b then Some st' else alist_lookup rest x) = Some sty ->
               sem_slot_aux n Σ sty
      with
      | true => fun Heq =>
          eq_rect st' (fun s => sem_slot_aux n Σ s) (fst fields) sty (Some_inj Heq)
      | false => fun Heq =>
          sem_layout_lookup n Σ rest x sty Heq (snd fields)
      end H
  end.

(** Project a field from a contract value at depth [S n].
    Returns at depth [n]. Works directly with the inner fix type
    from [sem_slot_aux], avoiding the [sem_layout_aux] convertibility issue. *)
Definition sem_contract_field (n : nat) (Σ : contract_env) (a x : ident)
    (sty : slot_type)
    (Hfield : Σ_storage_var Σ a x = Some sty)
    (v : sem_slot_aux (S n) Σ (SContract a)) : sem_slot_aux n Σ sty.
Proof.
  simpl in v. destruct v as [addr fields].
  unfold Σ_storage_var in Hfield.
  destruct (Σ_storage Σ a) as [layout|] eqn:Elayout; [|discriminate].
  unfold Σ_storage_or_nil in fields. rewrite Elayout in fields.
  induction layout as [|[k st'] rest IH] in fields, Hfield |- *.
  - simpl in Hfield. discriminate.
  - simpl in Hfield, fields.
    destruct (String.eqb k x) eqn:Ekx.
    + injection Hfield as <-. exact (fst fields).
    + exact (IH Hfield (snd fields)).
Defined.

(** Same for [AContractAddr] *)
Definition sem_contractaddr_field (n : nat) (Σ : contract_env) (a x : ident)
    (sty : slot_type)
    (Hfield : Σ_storage_var Σ a x = Some sty)
    (v : sem_slot_aux (S n) Σ (SAbi (AContractAddr a))) : sem_slot_aux n Σ sty.
Proof.
  simpl in v. destruct v as [addr fields].
  unfold Σ_storage_var in Hfield.
  destruct (Σ_storage Σ a) as [layout|] eqn:Elayout; [|discriminate].
  unfold Σ_storage_or_nil in fields. rewrite Elayout in fields.
  induction layout as [|[k st'] rest IH] in fields, Hfield |- *.
  - simpl in Hfield. discriminate.
  - simpl in Hfield, fields.
    destruct (String.eqb k x) eqn:Ekx.
    + injection Hfield as <-. exact (fst fields).
    + exact (IH Hfield (snd fields)).
Defined.

(** Extract the address from a contract value *)
Definition sem_contract_addr (n : nat) (Σ : contract_env) (a : ident)
    (v : sem_slot_aux (S n) Σ (SContract a)) : nat :=
  fst v.

Definition sem_contractaddr_addr (n : nat) (Σ : contract_env) (a : ident)
    (v : sem_slot_aux (S n) Σ (SAbi (AContractAddr a))) : nat :=
  fst v.

(** Interface field lookup *)
Definition sem_iface_lookup (n : nat) (Σ : contract_env)
    (iface : interface) (x : ident) (alpha : abi_type)
    (Hlookup : alist_lookup iface x = Some alpha)
    (fields : sem_iface_fields_aux n Σ iface) : sem_slot_aux n Σ (SAbi alpha).
Proof.
  induction iface as [|[k a] rest IH] in fields, Hlookup |- *.
  - simpl in Hlookup. discriminate.
  - simpl in Hlookup, fields.
    destruct (String.eqb k x) eqn:Ekx.
    + injection Hlookup as <-. exact (fst fields).
    + exact (IH Hlookup (snd fields)).
Defined.

(* ================================================================= *)
(** ** Denotation of Environment References — Section 10.2.1 *)

Definition denote_env_ref (n : nat) (Σ : contract_env) (iface : interface)
    (oid : opt_id) (ev : env_var) (alpha : abi_type)
    (H : type_env_ref_t Σ iface oid ev alpha)
    (rho : sem_iface_aux n Σ iface)
    (v : sem_opt_id_aux n Σ oid)
    : sem_slot_aux n Σ (SAbi alpha).
Proof.
  destruct H; destruct n as [|n']; simpl.
  (* T_Caller: caller = fst (fst triple) *)
  - exact (fst (fst (snd rho))).
  - exact (fst (fst (snd rho))).
  (* T_Origin: origin = snd (fst triple) *)
  - exact (snd (fst (snd rho))).
  - exact (snd (fst (snd rho))).
  (* T_Callvalue: callvalue = snd triple *)
  - exact (snd (snd rho)).
  - exact (snd (snd rho)).
  (* T_This: return v *)
  - exact (match v : Empty_set with end).
  - exact v.
Defined.

(** Helper: combine Σ_storage and alist_lookup into Σ_storage_var *)
Lemma storage_var_from_parts : forall Σ a x sty layout,
  Σ_storage Σ a = Some layout ->
  alist_lookup layout x = Some sty ->
  Σ_storage_var Σ a x = Some sty.
Proof.
  intros Σ a x sty layout Hstor Hlook.
  unfold Σ_storage_var. rewrite Hstor. exact Hlook.
Qed.

(* ================================================================= *)
(** ** Denotation of References and Expressions — Sections 10.2.2–10.2.3

    Mutual fixpoint on the Type-valued typing derivations.
    Works at depth [n]; field access uses [sem_contract_field]
    (which drops depth by 1) followed by [sem_slot_weaken]. *)

Fixpoint denote_ref (n : nat) (Σ : contract_env) (iface : interface)
    (k : ref_tag) (oid : opt_id) (t : time_tag) (r : ref) (sty : slot_type)
    (H : type_ref_t Σ iface k oid t r sty)
    (rho : sem_iface_aux n Σ iface)
    (v : sem_opt_id_timed_aux n Σ oid t)
    {struct H} : sem_slot_aux n Σ sty
with denote_expr (n : nat) (Σ : contract_env) (iface : interface)
    (oid : opt_id) (t : time_tag) (e : expr) (bt : base_type)
    (H : type_expr_t Σ iface oid t e bt)
    (rho : sem_iface_aux n Σ iface)
    (v : sem_opt_id_timed_aux n Σ oid t)
    {struct H} : sem_base bt.
Proof.
  - (* denote_ref *)
    destruct H.

    + (* T_Calldata_t: ρ(x) where x : α ∈ I *)
      destruct n as [|n']; simpl.
      { exact (sem_iface_lookup 0 Σ iface x alpha e (fst rho)). }
      { exact (sem_iface_lookup (S n') Σ iface x alpha e (fst rho)). }

    + (* T_Storage_t: v.x, untimed *)
      destruct n as [|n'].
      { simpl in v. exact (match v : Empty_set with end). }
      { exact (sem_slot_weaken n' Σ sty
                 (sem_contract_field n' Σ a x sty
                   (storage_var_from_parts Σ a x sty layout e e0) v)). }

    + (* T_StoragePre_t: v_pre.x, timed *)
      destruct n as [|n'].
      { simpl in v. exact (match (fst v) : Empty_set with end). }
      { exact (sem_slot_weaken n' Σ sty
                 (sem_contract_field n' Σ a x sty
                   (storage_var_from_parts Σ a x sty layout e e0) (fst v))). }

    + (* T_StoragePost_t: v_post.x, timed *)
      destruct n as [|n'].
      { simpl in v. exact (match (snd v) : Empty_set with end). }
      { exact (sem_slot_weaken n' Σ sty
                 (sem_contract_field n' Σ a x sty
                   (storage_var_from_parts Σ a x sty layout e e0) (snd v))). }

    + (* T_Coerce_t: ref as A — AContractAddr a ≡ SContract a after unfolding *)
      destruct n as [|n']; simpl.
      { pose (val := denote_ref 0 Σ iface k oid t r (SAbi (AContractAddr a)) H rho v).
        simpl in val. exact (match val : Empty_set with end). }
      { exact (denote_ref (S n') Σ iface k oid t r (SAbi (AContractAddr a)) H rho v). }

    + (* T_Upcast_t: ref : address_A → address, extract addr field *)
      destruct n as [|n']; simpl.
      { pose (val := denote_ref 0 Σ iface k oid t r (SAbi (AContractAddr a)) H rho v).
        simpl in val. exact (match val : Empty_set with end). }
      { exact (fst (denote_ref (S n') Σ iface k oid t r (SAbi (AContractAddr a)) H rho v)). }

    + (* T_Field_t: ref.x where ref : A *)
      destruct n as [|n']; simpl.
      { pose (val := denote_ref 0 Σ iface k oid t r (SContract a) H rho v).
        simpl in val. exact (match val : Empty_set with end). }
      { match goal with
        | [ Hf : Σ_storage_var _ _ _ = Some _ |- _ ] =>
            exact (sem_slot_weaken n' Σ sty
                     (sem_contract_field n' Σ a x sty Hf
                       (denote_ref (S n') Σ iface k oid t r (SContract a) H rho v)))
        end. }

    + (* T_MapIndex_t: ref[e] *)
      destruct n as [|n']; simpl.
      { exact (denote_ref 0 Σ iface k oid t r
                 (SMapping (MMapping bt mu)) H rho v
                 (denote_expr 0 Σ iface oid t e bt t0 rho v)). }
      { exact (denote_ref (S n') Σ iface k oid t r
                 (SMapping (MMapping bt mu)) H rho v
                 (denote_expr (S n') Σ iface oid t e bt t0 rho v)). }

    + (* T_Environment_t: env ref — t specializes to TagU *)
      match goal with
      | [ Henv : type_env_ref_t _ _ _ _ _ |- _ ] =>
          destruct n as [|n']; simpl;
          exact (denote_env_ref _ Σ iface oid ev alpha Henv rho v)
      end.

  - (* denote_expr *)
    destruct H.

    + (* T_Int_t: integer literal *)
      match goal with
      | [ Hi : in_range _ ?z |- sem_base (TInt _) ] => exact (exist _ z Hi)
      end.

    + (* T_Bool_t: boolean literal *)
      exact b.

    + (* T_Ref_t: ref — extract base value from slot *)
      match goal with
      | [ Hr : type_ref_t _ _ ?k' _ _ _ (SAbi (ABase ?bt')) |- sem_base ?bt' ] =>
          destruct n as [|n']; simpl;
          exact (denote_ref _ Σ iface k' oid t r (SAbi (ABase bt')) Hr rho v)
      end.

    + (* T_Addr_t: addr(ref) — contract address *)
      match goal with
      | [ Hr : type_ref_t _ _ ?k' _ TagU _ (SContract ?a') |- _ ] =>
          destruct n as [|n'];
          [ simpl; pose (cv := denote_ref 0 Σ iface k' oid TagU r (SContract a') Hr rho v);
            simpl in cv; exact (match cv : Empty_set with end)
          | exact (fst (denote_ref (S n') Σ iface k' oid TagU r (SContract a') Hr rho v)) ]
      end.

    + (* T_Range_t: inrange(ι₁, e) *)
      match goal with
      | [ He : type_expr_t _ _ _ _ _ (TInt ?it2') |- _ ] =>
          pose (val := denote_expr n Σ iface oid t e (TInt it2') He rho v);
          simpl in val; destruct val as [z _];
          exact (match it1 with
                 | IntUnbounded => true
                 | _ => match int_min it1, int_max it1 with
                        | Some lo, Some hi => (lo <=? z)%Z && (z <=? hi)%Z
                        | _, _ => false
                        end
                 end)
      end.

    + (* T_BopI_t: e₁ ○ᵢ e₂ *)
      match goal with
      | [ H1 : type_expr_t _ _ _ _ ?e1' (TInt ?it1'),
          H2 : type_expr_t _ _ _ _ ?e2' (TInt ?it2') |- _ ] =>
          pose (z1v := denote_expr n Σ iface oid t e1' (TInt it1') H1 rho v);
          pose (z2v := denote_expr n Σ iface oid t e2' (TInt it2') H2 rho v);
          simpl in z1v, z2v;
          destruct z1v as [z1 _]; destruct z2v as [z2 _];
          exact (exist _ (eval_int_binop op z1 z2) I)
      end.

    + (* T_NumConv_t: e : ι → e : int (subsumption) *)
      match goal with
      | [ He : type_expr_t _ _ _ _ _ (TInt ?it') |- _ ] =>
          pose (val := denote_expr n Σ iface oid t e (TInt it') He rho v);
          simpl in val; destruct val as [z _];
          exact (exist _ z I)
      end.

    + (* T_BopB_t: e₁ ○_b e₂ *)
      match goal with
      | [ H1 : type_expr_t _ _ _ _ ?e1' TBool,
          H2 : type_expr_t _ _ _ _ ?e2' TBool |- _ ] =>
          exact (eval_bool_binop op
                   (denote_expr n Σ iface oid t e1' TBool H1 rho v)
                   (denote_expr n Σ iface oid t e2' TBool H2 rho v))
      end.

    + (* T_Neg_t: ¬e *)
      match goal with
      | [ He : type_expr_t _ _ _ _ _ TBool |- _ ] =>
          exact (negb (denote_expr n Σ iface oid t e TBool He rho v))
      end.

    + (* T_Cmp_t: e₁ ⋈ e₂ *)
      match goal with
      | [ H1 : type_expr_t _ _ _ _ ?e1' (TInt ?it'),
          H2 : type_expr_t _ _ _ _ ?e2' (TInt ?it') |- _ ] =>
          pose (z1v := denote_expr n Σ iface oid t e1' (TInt it') H1 rho v);
          pose (z2v := denote_expr n Σ iface oid t e2' (TInt it') H2 rho v);
          simpl in z1v, z2v;
          destruct z1v as [z1 _]; destruct z2v as [z2 _];
          exact (eval_cmp op z1 z2)
      end.

    + (* T_ITE_t: if e₁ then e₂ else e₃ *)
      match goal with
      | [ H1 : type_expr_t _ _ _ _ ?e1' TBool,
          H2 : type_expr_t _ _ _ _ ?e2' ?bt',
          H3 : type_expr_t _ _ _ _ ?e3' ?bt' |- sem_base ?bt' ] =>
          destruct (denote_expr n Σ iface oid t e1' TBool H1 rho v);
          [ exact (denote_expr n Σ iface oid t e2' bt' H2 rho v)
          | exact (denote_expr n Σ iface oid t e3' bt' H3 rho v) ]
      end.

    + (* T_Eq_t: e₁ = e₂ *)
      match goal with
      | [ H1 : type_expr_t _ _ _ _ ?e1' ?bt',
          H2 : type_expr_t _ _ _ _ ?e2' ?bt' |- _ ] =>
          exact (sem_base_eqb bt'
                   (denote_expr n Σ iface oid t e1' bt' H1 rho v)
                   (denote_expr n Σ iface oid t e2' bt' H2 rho v))
      end.
Defined.

(* ================================================================= *)
(** ** Default Semantic Mapping Values

    Used by the mapping denotation to fill in unmatched keys.
    Requires [default_value_typable mu] as evidence that 0 is in
    range for all integer types in the mapping chain. *)

Fixpoint sem_mapping_default (mu : mapping_type)
    : default_value_typable mu -> sem_mapping mu :=
  match mu return default_value_typable mu -> sem_mapping mu with
  | MBase (TInt it) => fun Hd => exist _ 0%Z Hd
  | MBase TBool => fun _ => false
  | MBase TAddress => fun _ => 0
  | MMapping bt mu' => fun Hd => fun _ => sem_mapping_default mu' Hd
  end.

(* ================================================================= *)
(** ** Denotation of Mapping Expressions — Section 10.2.4

    Builds a function [sem_base bt → sem_mapping mu] by iterating
    through bindings, comparing keys with [sem_base_eqb], and
    falling through to the default (or to the base reference for updates). *)

(** Build a mapping from a list of bindings with a fallback *)
Fixpoint sem_build_map (bt : base_type) (mu : mapping_type)
    (keys : list (sem_base bt)) (vals : list (sem_mapping mu))
    (fallback : sem_base bt -> sem_mapping mu)
    : sem_base bt -> sem_mapping mu :=
  match keys, vals with
  | k :: ks, v :: vs =>
      fun x => if sem_base_eqb bt x k then v else sem_build_map bt mu ks vs fallback x
  | _, _ => fallback
  end.

Fixpoint denote_mapexpr (n : nat) (Σ : contract_env) (iface : interface)
    (oid : opt_id) (m : map_expr) (mu : mapping_type)
    (H : type_mapexpr_t Σ iface oid m mu)
    (rho : sem_iface_aux n Σ iface)
    (v : sem_opt_id_aux n Σ oid)
    {struct H} : sem_mapping mu.
Proof.
  destruct H.

  - (* T_Exp_t: e → MBase bt *)
    exact (denote_expr n Σ iface oid TagU e bt t rho v).

  - (* T_Mapping_t: [e₁ => m₁, ...] : mapping(bt, mu) *)
    simpl.
    exact (sem_build_map bt mu
      ((fix go l (Hk : ForallT _ l) : list (sem_base bt) :=
        match Hk with
        | ForallT_nil => []
        | ForallT_cons he hrest =>
            denote_expr n Σ iface oid TagU (fst _) bt he rho v :: go _ hrest
        end) _ f)
      ((fix go l (Hv : ForallT _ l) : list (sem_mapping mu) :=
        match Hv with
        | ForallT_nil => []
        | ForallT_cons hm hrest =>
            denote_mapexpr n Σ iface oid (snd _) mu hm rho v :: go _ hrest
        end) _ f0)
      (fun _ => sem_mapping_default mu d)).

  - (* T_MappingUpd_t: ref[e₁ => m₁, ...] : mapping(bt, mu) *)
    simpl.
    match goal with
    | [ Hr : type_ref_t _ _ ?k' _ TagU _ (SMapping (MMapping bt mu)) |- _ ] =>
        destruct n as [|n'];
        [ exact (sem_build_map bt mu
            ((fix go l (Hk : ForallT _ l) : list (sem_base bt) :=
              match Hk with
              | ForallT_nil => []
              | ForallT_cons he hrest =>
                  denote_expr 0 Σ iface oid TagU (fst _) bt he rho v :: go _ hrest
              end) _ f)
            ((fix go l (Hv : ForallT _ l) : list (sem_mapping mu) :=
              match Hv with
              | ForallT_nil => []
              | ForallT_cons hm hrest =>
                  denote_mapexpr 0 Σ iface oid (snd _) mu hm rho v :: go _ hrest
              end) _ f0)
            (denote_ref 0 Σ iface k' oid TagU r (SMapping (MMapping bt mu)) Hr rho v))
        | exact (sem_build_map bt mu
            ((fix go l (Hk : ForallT _ l) : list (sem_base bt) :=
              match Hk with
              | ForallT_nil => []
              | ForallT_cons he hrest =>
                  denote_expr (S n') Σ iface oid TagU (fst _) bt he rho v :: go _ hrest
              end) _ f)
            ((fix go l (Hv : ForallT _ l) : list (sem_mapping mu) :=
              match Hv with
              | ForallT_nil => []
              | ForallT_cons hm hrest =>
                  denote_mapexpr (S n') Σ iface oid (snd _) mu hm rho v :: go _ hrest
              end) _ f0)
            (denote_ref (S n') Σ iface k' oid TagU r (SMapping (MMapping bt mu)) Hr rho v))
        ]
    end.
Defined.

(* ================================================================= *)
(** ** Denotation of Slot Expressions — Section 10.2.5

    For [T_SlotMap], [T_SlotRef], and [T_SlotAddr], the denotation is
    straightforward. The [T_Create] and [T_CreatePayable] cases involve
    constructor evaluation which is set-valued (Section 10.2.7) and
    requires additional infrastructure. *)

Fixpoint denote_slotexpr (n : nat) (Σ : contract_env) (iface : interface)
    (oid : opt_id) (se : slot_expr) (sty : slot_type)
    (H : type_slotexpr_t Σ iface oid se sty)
    (rho : sem_iface_aux n Σ iface)
    (v : sem_opt_id_aux n Σ oid)
    {struct H} : sem_slot_aux n Σ sty.
Proof.
  destruct H.

  - (* T_SlotMap_t: m : μ → SMapping μ *)
    match goal with
    | [ Hm : type_mapexpr_t _ _ _ _ ?mu' |- _ ] =>
        destruct n as [|n']; simpl;
        exact (denote_mapexpr _ Σ iface oid m mu' Hm rho v)
    end.

  - (* T_SlotRef_t: ref : A → SContract A *)
    match goal with
    | [ Hr : type_ref_t _ _ ?k' _ TagU _ (SContract ?a') |- _ ] =>
        exact (denote_ref n Σ iface k' oid TagU r (SContract a') Hr rho v)
    end.

  - (* T_SlotAddr_t: addr(se) : address_A *)
    match goal with
    | [ Hse : type_slotexpr_t _ _ _ _ (SContract ?a') |- _ ] =>
        destruct n as [|n']; simpl;
        [ pose (cv := denote_slotexpr 0 Σ iface oid se (SContract a') Hse rho v);
          simpl in cv; exact (match cv : Empty_set with end)
        | exact (denote_slotexpr (S n') Σ iface oid se (SContract a') Hse rho v) ]
    end.

  - (* T_Create_t: new A(se₁,...,seₙ) — constructor creation *)
    (* The denotation of creates involves constructor case selection,
       which is set-valued in the tech report (Section 10.2.7).
       To be defined once the full constructor infrastructure is in place. *)
    admit.

  - (* T_CreatePayable_t: new A{value: se_v}(se₁,...,seₙ) *)
    admit.
Admitted.

(* ================================================================= *)
(** ** Denotation of a Slot Expression List

    Evaluates a list of slot expressions, collecting results. *)

Fixpoint denote_slotexpr_list (n : nat) (Σ : contract_env) (iface : interface)
    (oid : opt_id) (ses : list slot_expr) (alphas : list abi_type)
    (H : Forall2T (fun se alpha => type_slotexpr_t Σ iface oid se (SAbi alpha))
                   ses alphas)
    (rho : sem_iface_aux n Σ iface)
    (v : sem_opt_id_aux n Σ oid)
    {struct H} : list { alpha : abi_type & sem_slot_aux n Σ (SAbi alpha) }.
Proof.
  destruct H.
  - exact [].
  - match goal with
    | [ Hse : type_slotexpr_t _ _ _ _ (SAbi ?a'),
        Hrest : Forall2T _ _ _ |- _ ] =>
        exact (existT _ a' (denote_slotexpr n Σ iface oid _ _ Hse rho v) ::
               denote_slotexpr_list n Σ iface oid _ _ Hrest rho v)
    end.
Defined.

(* ================================================================= *)
(** ** Denotation of Creates — Section 10.2.6

    Builds a contract record from a list of creates.
    Each create assigns a field of the new contract.
    The result is a value of type ⟦Id⟧_{Σ, Id:C}. *)

Fixpoint denote_creates_aux (n : nat) (Σ : contract_env) (iface : interface)
    (creates : list create)
    (H : ForallT (fun c => type_slotexpr_t Σ iface ONone (snd c) (fst (fst c))) creates)
    (rho : sem_iface_aux n Σ iface)
    (v : sem_opt_id_aux n Σ ONone)
    {struct H}
    : sem_layout_aux n Σ (map (fun c => (snd (fst c), fst (fst c))) creates).
Proof.
  destruct H.
  - exact tt.
  - simpl. split.
    + match goal with
      | [ Hse : type_slotexpr_t _ _ _ (snd ?c) (fst (fst ?c)) |- _ ] =>
          exact (denote_slotexpr n Σ iface ONone (snd c) (fst (fst c)) Hse rho v)
      end.
    + exact (denote_creates_aux n Σ iface _ H rho v).
Defined.

(* ================================================================= *)
(** ** Semantics of Constructors — Section 10.2.7

    The constructor denotation is set-valued: given an environment ρ,
    it produces the set of possible post-states of the new contract.

    ⟦Σ ⊢_Id cnstr : C⟧_ρ ⊆ ⟦Id⟧_{Σ,Id:C}

    The definition finds the unique case i whose condition evaluates
    to true (guaranteed by the exhaustivity/exclusivity premise),
    then evaluates creates_i to produce the contract record. *)

(** Evaluate a list of boolean preconditions under the denotation *)
Fixpoint denote_pres_true (n : nat) (Σ : contract_env) (iface : interface)
    (oid : opt_id) (t : time_tag) (pres : list expr)
    (Hp : ForallT (fun pre => type_expr_t Σ iface oid t pre TBool) pres)
    (rho : sem_iface_aux n Σ iface)
    (v : sem_opt_id_timed_aux n Σ oid t) : Prop :=
  match Hp with
  | ForallT_nil => True
  | ForallT_cons he hrest =>
      denote_expr n Σ iface oid t _ TBool he rho v = true /\
      denote_pres_true n Σ iface oid t _ hrest rho v
  end.

Definition sem_constructor (n : nat) (Σ : contract_env) (a : ident)
    (ctor : constructor) (layout : storage_layout)
    (H : type_constructor_t Σ a ctor layout)
    (rho : sem_iface_aux n Σ (ctor_iface ctor))
    (s : sem_layout_aux n Σ layout)
    : Prop.
Proof.
  destruct H as [? ? ? ? Hwf Hpres Hconds Hcreates Hlayout_wf Hdom Hposts Hexhaust].
  refine (exists i, i < length (ctor_cases ctor) /\ _ /\ _).
  - (* All preconditions true *)
    exact (denote_pres_true n Σ (ctor_iface ctor) ONone TagU _ Hpres rho tt).
  - (* Case i true, others false *)
    exact ((fix find (cases : list ctor_case)
      (Hc : ForallT (fun cc => type_expr_t Σ (ctor_iface ctor) ONone TagU (fst cc) TBool) cases)
      (idx : nat) : Prop :=
      match Hc with
      | ForallT_nil => True
      | ForallT_cons hcond hcrest =>
          (if Nat.eqb idx i
           then denote_expr n Σ (ctor_iface ctor) ONone TagU _ TBool hcond rho tt = true
           else denote_expr n Σ (ctor_iface ctor) ONone TagU _ TBool hcond rho tt = false) /\
          find _ hcrest (S idx)
      end) (ctor_cases ctor) Hconds 0).
Defined.

(* ================================================================= *)
(** ** Semantics of Transitions — Section 10.2.8

    The transition denotation is a relation on pre- and post-states.

    ⟦Σ ⊢_Id transition⟧_ρ ⊆ ⟦Id⟧_Σ × ⟦Id⟧_Σ *)

Definition sem_transition (n : nat) (Σ : contract_env) (a : ident)
    (tr : transition)
    (H : type_transition_t Σ a tr)
    (rho : sem_iface_aux n Σ (trans_iface tr))
    (s s' : sem_slot_aux n Σ (SContract a))
    : Prop.
Proof.
  destruct H as [? ? ? Hwf Hpres Hconds Hupds Hrets Hposts Hexhaust].
  refine (exists i, i < length (trans_cases tr) /\ _ /\ _).
  - exact (denote_pres_true n Σ (trans_iface tr) (OSome a) TagU _ Hpres rho s).
  - exact ((fix find (cases : list trans_case)
      (Hc : ForallT (fun tc => type_expr_t Σ (trans_iface tr) (OSome a) TagU (tc_cond tc) TBool) cases)
      (idx : nat) : Prop :=
      match Hc with
      | ForallT_nil => True
      | ForallT_cons hcond hcrest =>
          (if Nat.eqb idx i
           then denote_expr n Σ (trans_iface tr) (OSome a) TagU _ TBool hcond rho s = true
           else denote_expr n Σ (trans_iface tr) (OSome a) TagU _ TBool hcond rho s = false) /\
          find _ hcrest (S idx)
      end) (trans_cases tr) Hconds 0).
Defined.

(* ================================================================= *)
(** ** Type-valued Value Typing — for large elimination in Section 10.3 *)

Inductive has_base_type_t : value -> base_type -> Type :=
  | V_Int_t : forall n it, in_range it n -> has_base_type_t (VInt n) (TInt it)
  | V_Bool_t : forall b, has_base_type_t (VBool b) TBool
  | V_Addr_t : forall a, has_base_type_t (VAddr a) TAddress.

Inductive has_mapping_type_t : value -> mapping_type -> Type :=
  | V_BaseValMu_t : forall v bt,
      has_base_type_t v bt ->
      has_mapping_type_t v (MBase bt)
  | V_MappingZ_t : forall f it mu,
      (forall n, in_range it n -> has_mapping_type_t (f n) mu) ->
      has_mapping_type_t (VMapZ f) (MMapping (TInt it) mu)
  | V_MappingB_t : forall f mu,
      (forall b, has_mapping_type_t (f b) mu) ->
      has_mapping_type_t (VMapB f) (MMapping TBool mu)
  | V_MappingA_t : forall f mu,
      (forall a, has_mapping_type_t (f a) mu) ->
      has_mapping_type_t (VMapA f) (MMapping TAddress mu).

Inductive has_abi_type_t : contract_env -> value -> state -> abi_type -> Type :=
  | V_BaseValAlpha_t : forall Σ v s bt,
      has_base_type_t v bt ->
      has_abi_type_t Σ v s (ABase bt)
  | V_AddrIsContract_t : forall Σ s (l : addr) (a : ident),
      state_dom s l ->
      dom (Σ_storage Σ) a ->
      state_type s l = Some a ->
      has_fields_t Σ s l (Σ_storage_or_nil Σ a) ->
      has_abi_type_t Σ (VAddr l) s (AContractAddr a)

with has_slot_type_t : contract_env -> value -> state -> slot_type -> Type :=
  | V_MappingVal_t : forall Σ v s mu,
      has_mapping_type_t v mu ->
      has_slot_type_t Σ v s (SMapping mu)
  | V_ABIVal_t : forall Σ v s alpha,
      has_abi_type_t Σ v s alpha ->
      has_slot_type_t Σ v s (SAbi alpha)
  | V_Contract_t : forall Σ (l : addr) s (a : ident),
      has_abi_type_t Σ (VAddr l) s (AContractAddr a) ->
      has_slot_type_t Σ (VAddr l) s (SContract a)

with has_fields_t : contract_env -> state -> addr -> storage_layout -> Type :=
  | HF_nil : forall Σ s l, has_fields_t Σ s l []
  | HF_cons : forall Σ s l x sty rest,
      has_slot_type_t Σ (state_var_force s l x) s sty ->
      has_fields_t Σ s l rest ->
      has_fields_t Σ s l ((x, sty) :: rest).

(* ================================================================= *)
(** ** Denotation of Values — Section 10.3

    Flattens pointer-values into semantic values by replacing contract
    addresses with the contract records from the state. *)

(** ⟦⊢ v : β⟧ ∈ ⟦β⟧ *)
Definition denote_base_value (v : value) (bt : base_type)
    (H : has_base_type_t v bt) : sem_base bt :=
  match H with
  | V_Int_t n it Hin => exist _ n Hin
  | V_Bool_t b => b
  | V_Addr_t a => a
  end.

(** ⟦⊢ v : μ⟧ ∈ ⟦μ⟧ *)
Fixpoint denote_mapping_value (v : value) (mu : mapping_type)
    (H : has_mapping_type_t v mu) {struct H} : sem_mapping mu :=
  match H with
  | V_BaseValMu_t _ bt Hb => denote_base_value _ bt Hb
  | V_MappingZ_t f it mu' Hf => fun key =>
      denote_mapping_value (f (proj1_sig key)) mu' (Hf (proj1_sig key) (proj2_sig key))
  | V_MappingB_t f mu' Hf => fun key => denote_mapping_value (f key) mu' (Hf key)
  | V_MappingA_t f mu' Hf => fun key => denote_mapping_value (f key) mu' (Hf key)
  end.

(* ----------------------------------------------------------------- *)
(** *** Depth measure — len(Σ, σ) *)

(** Position of an identifier in a list (0-indexed from the start).
    Returns [length l] if not found. *)
Fixpoint ident_index (l : list (ident * storage_layout)) (a : ident) : nat :=
  match l with
  | [] => 0
  | (k, _) :: rest => if String.eqb k a then 0 else S (ident_index rest a)
  end.

(** len(Σ, σ) — the depth of a slot type in the store.
    For contract types, this is [S (position of A in Σ)].
    For non-contract types, 0.
    Strictly decreases for fields of a well-founded store. *)
Definition sty_depth (Σ : contract_env) (sty : slot_type) : nat :=
  match sty with
  | SMapping _ => 0
  | SAbi (ABase _) => 0
  | SAbi (AContractAddr a) => S (ident_index (Σ_storage_list Σ) a)
  | SContract a => S (ident_index (Σ_storage_list Σ) a)
  end.

(** Iterated depth weakening: coerce from depth [n] to depth [k + n]. *)
Fixpoint sem_slot_weaken_add (k n : nat) (Σ : contract_env) (st : slot_type)
    : sem_slot_aux n Σ st -> sem_slot_aux (k + n) Σ st :=
  match k with
  | 0 => id
  | S k' => fun x =>
      sem_slot_weaken (k' + n) Σ st (sem_slot_weaken_add k' n Σ st x)
  end.

(** Well-foundedness of Σ: field types have strictly smaller depth. *)
Definition wf_Σ (Σ : contract_env) : Prop :=
  forall a x sty,
    In (x, sty) (Σ_storage_or_nil Σ a) ->
    sty_depth Σ sty < sty_depth Σ (SContract a).

(** Build contract fields from a [has_fields_t] proof and a denotation function
    for each field. The [rec] callback receives an [In] proof so the caller
    can appeal to well-foundedness. *)
Fixpoint denote_fields (n : nat) (Σ : contract_env) (s : state) (l : addr)
    (a : ident) (layout : storage_layout) (F : has_fields_t Σ s l layout)
    (Hsub : incl layout (Σ_storage_or_nil Σ a))
    (rec : forall x sty,
       In (x, sty) (Σ_storage_or_nil Σ a) ->
       has_slot_type_t Σ (state_var_force s l x) s sty ->
       sem_slot_aux n Σ sty)
    {struct F} : sem_layout_aux n Σ layout.
Proof.
  destruct F.
  - exact tt.
  - simpl. match goal with
    | [Hfld : has_slot_type_t _ _ _ ?sty0,
       Frest : has_fields_t _ _ _ ?rest0 |- _] =>
        exact (rec _ sty0 (Hsub _ (or_introl eq_refl)) Hfld,
               denote_fields n Σ s l a rest0 Frest
                 (fun p Hp => Hsub p (or_intror Hp)) rec)
    end.
Defined.

(** ⟦Σ ⊢ v :_s σ⟧ ∈ ⟦σ⟧_Σ — by well-founded recursion on len(Σ, σ).

    The step function for the [Fix] combinator. At depth [d],
    the recursive call [rec d' Hlt] is available for any [d' < d].
    Requires [wf_Σ Σ] and [sty_depth Σ sty <= d]. *)
Lemma sub_add_eq : forall n m, m <= n -> n - m + m = n.
Proof. intros. lia. Qed.

Definition denote_slot_value_body
    (Σ : contract_env) (s : state) (HwfΣ : wf_Σ Σ)
    (d : nat)
    (rec : forall d', d' < d ->
           forall sty v, has_slot_type_t Σ v s sty ->
           sty_depth Σ sty <= d' -> sem_slot_aux d' Σ sty)
    (sty : slot_type) (v : value) (H : has_slot_type_t Σ v s sty)
    (Hd : sty_depth Σ sty <= d)
    : sem_slot_aux d Σ sty.
Proof.
  destruct H; destruct d as [|d']; simpl.
  - (* V_MappingVal_t, d=0 *) exact (denote_mapping_value v mu h).
  - (* V_MappingVal_t, d=S d' *) exact (denote_mapping_value v mu h).
  - (* V_ABIVal_t, d=0 *)
    destruct h; simpl.
    + exact (denote_base_value v bt h).
    + exfalso. simpl in Hd. lia.
  - (* V_ABIVal_t, d=S d' *)
    destruct h; simpl.
    + exact (denote_base_value v bt h).
    + refine (l, denote_fields d' Σ s l a _ h (incl_refl _) _).
      intros x0 sty0 Hin0 Hsty0.
      assert (Hdepth : sty_depth Σ sty0 < sty_depth Σ (SContract a)).
      { exact (HwfΣ a x0 sty0 Hin0). }
      refine (eq_rect _ (fun n => sem_slot_aux n Σ sty0)
               (sem_slot_weaken_add (d' - sty_depth Σ sty0)
                 (sty_depth Σ sty0) Σ sty0
                 (rec (sty_depth Σ sty0) _ sty0 _ Hsty0 (le_n _)))
               d' (sub_add_eq d' (sty_depth Σ sty0) _)).
      { simpl in Hd, Hdepth. lia. }
      { simpl in Hd, Hdepth. lia. }
  - (* V_Contract_t, d=0 *)
    exfalso. simpl in Hd. lia.
  - (* V_Contract_t, d=S d' *)
    simpl.
    inversion h as [? ? ? ? Hbt | ? ? ? ? Hdom HdomΣ Htype Hfields]; subst.
    { refine (l, denote_fields d' Σ s l a _ Hfields (incl_refl _) _).
      intros x0 sty0 Hin0 Hsty0.
      assert (Hdepth : sty_depth Σ sty0 < sty_depth Σ (SContract a)).
      { exact (HwfΣ a x0 sty0 Hin0). }
      refine (eq_rect _ (fun n => sem_slot_aux n Σ sty0)
               (sem_slot_weaken_add (d' - sty_depth Σ sty0)
                 (sty_depth Σ sty0) Σ sty0
                 (rec (sty_depth Σ sty0) _ sty0 _ Hsty0 (le_n _)))
               d' (sub_add_eq d' (sty_depth Σ sty0) _)).
      { simpl in Hd, Hdepth. lia. }
      { simpl in Hd, Hdepth. lia. } }
Defined.

Definition denote_slot_value (Σ : contract_env) (HwfΣ : wf_Σ Σ)
    (v : value) (s : state)
    (sty : slot_type) (H : has_slot_type_t Σ v s sty)
    : sem_slot_aux (sty_depth Σ sty) Σ sty :=
  Fix lt_wf
    (fun d => forall sty v, has_slot_type_t Σ v s sty ->
              sty_depth Σ sty <= d -> sem_slot_aux d Σ sty)
    (denote_slot_value_body Σ s HwfΣ)
    (sty_depth Σ sty) sty v H (le_n _).

Definition denote_abi_value (Σ : contract_env) (HwfΣ : wf_Σ Σ)
    (v : value) (s : state)
    (alpha : abi_type) (H : has_abi_type_t Σ v s alpha)
    : sem_slot_aux (sty_depth Σ (SAbi alpha)) Σ (SAbi alpha) :=
  denote_slot_value Σ HwfΣ v s (SAbi alpha) (V_ABIVal_t Σ v s alpha H).
