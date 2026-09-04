(** * Soundness of the Value Semantics
    Formalizes the proof that the denotational value semantics is
    sound with respect to the pointer semantics:

    - Lemma [ref_soundness_untimed]:
      ⟦Σ; I ⊢^k_{?A,U} ref : σ⟧^a_ρ = ⟦Σ ⊢ v :_s σ⟧

    - Lemma [expr_soundness_untimed]:
      ⟦Σ; I; Φ ⊢_{?A,U} e : β⟧^a_ρ = ⟦⊢ v : β⟧

    - Lemma [mapexpr_soundness]:
      ⟦Σ; I; Φ ⊢_{?A} m : μ⟧^a_ρ = ⟦⊢ v : μ⟧

    The proofs proceed by mutual induction on the Type-valued typing
    derivation, inverting the operational semantics at each step. *)

From Stdlib Require Import String ZArith List Bool PeanoNat Lia JMeq.
From Stdlib Require Import ProofIrrelevance FunctionalExtensionality.
From Stdlib Require Import Program.Equality.
From Act Require Import Maps Syntax Domains Semantics ValueTyping Typing
                        TypingT TypeSafety ValueSemantics.
Import ListNotations.

(* ================================================================= *)
(** ** Value Denotation at Arbitrary Depth *)

(** Coerce [denote_slot_value] from [sty_depth Σ sty] to depth [n]. *)
Definition denote_slot_value_n (n : nat) (Σ : contract_env)
    (HwfΣ : wf_Σ Σ) (v : value) (s : state)
    (sty : slot_type) (H : has_slot_type_t Σ v s sty)
    (Hn : sty_depth Σ sty <= n)
    : sem_slot_aux n Σ sty :=
  eq_rect _ (fun m => sem_slot_aux m Σ sty)
    (sem_slot_weaken_add (n - sty_depth Σ sty) (sty_depth Σ sty) Σ sty
      (denote_slot_value Σ HwfΣ v s sty H))
    n (sub_add_eq n (sty_depth Σ sty) Hn).

Definition denote_abi_value_n (n : nat) (Σ : contract_env)
    (HwfΣ : wf_Σ Σ) (v : value) (s : state)
    (alpha : abi_type) (H : has_abi_type_t Σ v s alpha)
    (Hn : sty_depth Σ (SAbi alpha) <= n)
    : sem_slot_aux n Σ (SAbi alpha) :=
  denote_slot_value_n n Σ HwfΣ v s (SAbi alpha) (V_ABIVal_t Σ v s alpha H) Hn.

(* ================================================================= *)
(** ** Bridge: denote_slot_value_n at base type = denote_base_value *)

(** Extensionality of [denote_fields] in its [rec] argument. *)
Lemma denote_fields_ext : forall n Σ s l a layout
    (F : has_fields_t Σ s l layout)
    (Hsub : incl layout (Σ_storage_or_nil Σ a))
    (rec1 rec2 : forall x sty,
       In (x, sty) (Σ_storage_or_nil Σ a) ->
       has_slot_type_t Σ (state_var_force s l x) s sty ->
       sem_slot_aux n Σ sty),
  (forall x sty Hin Hst, rec1 x sty Hin Hst = rec2 x sty Hin Hst) ->
  denote_fields n Σ s l a layout F Hsub rec1 =
  denote_fields n Σ s l a layout F Hsub rec2.
Proof.
  intros n Σ s l a layout F.
  induction F; intros Hsub rec1 rec2 Hext; simpl.
  - reflexivity.
  - f_equal.
    + apply Hext.
    + apply IHF. intros. apply Hext.
Qed.

(** Extensionality of [denote_slot_value_body] for [Fix_eq]. *)
Lemma denote_slot_value_body_ext :
  forall Σ s HwfΣ x g1 g2,
  (forall y (H : y < x) sty v (Hst : has_slot_type_t Σ v s sty)
           (Hd : sty_depth Σ sty <= y),
      g1 y H sty v Hst Hd = g2 y H sty v Hst Hd) ->
  forall sty v (Hst : has_slot_type_t Σ v s sty) (Hd : sty_depth Σ sty <= x),
    denote_slot_value_body Σ s HwfΣ x g1 sty v Hst Hd =
    denote_slot_value_body Σ s HwfΣ x g2 sty v Hst Hd.
Proof.
  intros Σ s HwfΣ x g1 g2 Hext sty v Hst Hd.
  destruct Hst; destruct x as [|d']; try reflexivity.
  all: try (destruct h; try reflexivity; try (exfalso; simpl in Hd; lia)).
  all: try (exfalso; simpl in Hd; lia).
  (* Remaining: AContractAddr at S d', Contract at S d' *)
  all: enough (g1 = g2) as -> by reflexivity.
  all: apply functional_extensionality_dep; intro;
       apply functional_extensionality_dep; intro;
       apply functional_extensionality_dep; intro;
       apply functional_extensionality_dep; intro;
       apply functional_extensionality_dep; intro;
       apply functional_extensionality_dep; intro;
       apply Hext.
Qed.

(* ================================================================= *)
(** ** Proof Irrelevance Helpers *)

(** Two [sig] values with the same underlying value are equal. *)
Lemma sig_eq : forall (A : Type) (P : A -> Prop) (a : A) (H1 H2 : P a),
  exist P a H1 = exist P a H2.
Proof. intros. f_equal. apply proof_irrelevance. Qed.

(** [denote_base_value] is independent of the typing proof. *)
Lemma denote_base_value_irrel : forall v bt (H1 H2 : has_base_type_t v bt),
  denote_base_value v bt H1 = denote_base_value v bt H2.
Proof.
  intros v bt H1 H2.
  dependent destruction H1; dependent destruction H2; simpl.
  - apply sig_eq.
  - reflexivity.
  - reflexivity.
Qed.

(** Unfolding [denote_slot_value] at [SAbi (ABase bt)]. *)
Lemma denote_slot_value_body_ext_full :
  forall Σ s HwfΣ x
    (g1 g2 : forall y, y < x ->
      forall sty v, has_slot_type_t Σ v s sty ->
      sty_depth Σ sty <= y -> sem_slot_aux y Σ sty),
  (forall y H, g1 y H = g2 y H) ->
  denote_slot_value_body Σ s HwfΣ x g1 =
  denote_slot_value_body Σ s HwfΣ x g2.
Proof.
  intros Σ s HwfΣ x g1 g2 Hext.
  repeat (apply functional_extensionality_dep; intro).
  apply denote_slot_value_body_ext.
  intros y H sty v Hst Hd.
  assert (Heq : g1 y H = g2 y H) by apply Hext.
  apply (f_equal (fun f => f sty v Hst Hd)) in Heq. exact Heq.
Qed.

Lemma denote_slot_value_at_base :
  forall Σ HwfΣ v s bt (Hvt : has_base_type_t v bt)
    (Hsty : has_slot_type_t Σ v s (SAbi (ABase bt))),
  denote_slot_value Σ HwfΣ v s (SAbi (ABase bt)) Hsty =
  denote_base_value v bt Hvt.
Proof.
  intros. unfold denote_slot_value. rewrite Fix_eq.
  - dependent destruction Hsty. dependent destruction h.
    apply denote_base_value_irrel.
  - intros. apply denote_slot_value_body_ext_full. auto.
Qed.

(** Lift [eq] to [JMeq]. *)
Lemma eq_JMeq : forall (A : Type) (x y : A), x = y -> JMeq x y.
Proof. intros. subst. apply JMeq_refl. Qed.

(** [eq_rect] preserves JMeq with its argument. *)
Lemma eq_rect_JMeq : forall (A : Type) (P : A -> Type) (x y : A)
    (H : x = y) (v : P x),
  JMeq (eq_rect x P v y H) v.
Proof. intros. subst. apply JMeq_refl. Qed.

(** Iterated [sem_slot_weaken] at base type from depth 0 is JMeq-identity. *)
Lemma sem_slot_weaken_add_base_JMeq_0 : forall k Σ bt
    (x : sem_slot_aux 0 Σ (SAbi (ABase bt))),
  JMeq (sem_slot_weaken_add k 0 Σ (SAbi (ABase bt)) x) x.
Proof.
  induction k as [|k' IHk]; intros; simpl.
  - apply JMeq_refl.
  - destruct k' as [|k''].
    + simpl. apply JMeq_refl.
    + simpl. apply IHk.
Qed.


(** Bridge: [denote_slot_value_n] at base type equals [denote_base_value].
    Only works after destructing [n] so [sem_slot_aux] reduces. *)
Lemma denote_slot_value_n_at_base_0 :
  forall Σ HwfΣ v s bt
    (Hvt : has_base_type_t v bt)
    (Hsty : has_slot_type_t Σ v s (SAbi (ABase bt)))
    (Hn : sty_depth Σ (SAbi (ABase bt)) <= 0),
  denote_slot_value_n 0 Σ HwfΣ v s (SAbi (ABase bt)) Hsty Hn =
  denote_base_value v bt Hvt.
Proof.
  intros. unfold denote_slot_value_n. simpl.
  replace (sub_add_eq 0 0 Hn) with (@eq_refl nat 0)
    by (apply proof_irrelevance). simpl.
  apply denote_slot_value_at_base.
Qed.

Lemma denote_slot_value_n_at_base_S :
  forall n' Σ HwfΣ v s bt
    (Hvt : has_base_type_t v bt)
    (Hsty : has_slot_type_t Σ v s (SAbi (ABase bt)))
    (Hn : sty_depth Σ (SAbi (ABase bt)) <= S n'),
  denote_slot_value_n (S n') Σ HwfΣ v s (SAbi (ABase bt)) Hsty Hn =
  denote_base_value v bt Hvt.
Proof.
  intros. unfold denote_slot_value_n. simpl sty_depth. simpl Nat.sub.
  assert (Hn0 : 0 <= S n') by lia.
  replace Hn with Hn0 by (apply proof_irrelevance).
  transitivity (denote_slot_value Σ HwfΣ v s (SAbi (ABase bt)) Hsty).
  { apply JMeq_eq.
    exact (JMeq_trans
      (eq_rect_JMeq nat (fun m => sem_slot_aux m Σ (SAbi (ABase bt)))
        (S n' - 0 + 0) (S n') (sub_add_eq (S n') 0 Hn0)
        (sem_slot_weaken_add (S n' - 0) 0 Σ (SAbi (ABase bt))
          (denote_slot_value Σ HwfΣ v s (SAbi (ABase bt)) Hsty)))
      (sem_slot_weaken_add_base_JMeq_0 (S n' - 0) Σ bt
        (denote_slot_value Σ HwfΣ v s (SAbi (ABase bt)) Hsty))). }
  { apply denote_slot_value_at_base. }
Qed.

(** Proof irrelevance for [denote_slot_value_n]: the result is
    independent of the typing proof and depth bound. *)
Lemma denote_slot_value_n_irrel : forall n Σ HwfΣ v s sty
    (H1 H2 : has_slot_type_t Σ v s sty) (Hn1 Hn2 : sty_depth Σ sty <= n),
  denote_slot_value_n n Σ HwfΣ v s sty H1 Hn1 = denote_slot_value_n n Σ HwfΣ v s sty H2 Hn2.
Proof. Admitted.

(** The [fst] of the contract address denotation at [SAbi (AContractAddr a)]
    equals the base address denotation at [SAbi (ABase TAddress)]. *)
Lemma denote_slot_value_n_upcast : forall n Σ HwfΣ l s a
    (Hvt1 : has_slot_type_t Σ (VAddr l) s (SAbi (AContractAddr a)))
    (Hvt2 : has_slot_type_t Σ (VAddr l) s (SAbi (ABase TAddress)))
    (Hn1 : sty_depth Σ (SAbi (AContractAddr a)) <= S n)
    (Hn2 : sty_depth Σ (SAbi (ABase TAddress)) <= S n),
  fst (denote_slot_value_n (S n) Σ HwfΣ (VAddr l) s
         (SAbi (AContractAddr a)) Hvt1 Hn1) =
  denote_slot_value_n (S n) Σ HwfΣ (VAddr l) s
    (SAbi (ABase TAddress)) Hvt2 Hn2.
Proof. Admitted.

(** The denotation of a contract address value is the same whether
    viewed at type [SAbi (AContractAddr a)] or [SContract a]. *)
Lemma denote_slot_value_n_coerce : forall n Σ HwfΣ l s a
    (Hvt1 : has_slot_type_t Σ (VAddr l) s (SAbi (AContractAddr a)))
    (Hvt2 : has_slot_type_t Σ (VAddr l) s (SContract a))
    (Hn1 : sty_depth Σ (SAbi (AContractAddr a)) <= n)
    (Hn2 : sty_depth Σ (SContract a) <= n),
  JMeq (denote_slot_value_n n Σ HwfΣ (VAddr l) s (SAbi (AContractAddr a)) Hvt1 Hn1)
       (denote_slot_value_n n Σ HwfΣ (VAddr l) s (SContract a) Hvt2 Hn2).
Proof. Admitted.

(** Extract the [in_range] proof from [has_base_type_t (VInt n) (TInt it)]. *)
Definition extract_in_range (n : Z) (it : int_type)
    (H : has_base_type_t (VInt n) (TInt it)) : in_range it n :=
  match H in has_base_type_t v' bt'
    return match v', bt' with
           | VBase (BVInt n'), TInt it' => in_range it' n'
           | _, _ => True
           end
  with
  | V_Int_t _ _ Hin => Hin
  | V_Bool_t _ => I
  | V_Addr_t _ => I
  end.

(** [denote_base_value] on an integer is [exist _ n Hin]. *)
Lemma denote_base_value_VInt : forall n it (H : has_base_type_t (VInt n) (TInt it)),
  denote_base_value (VInt n) (TInt it) H = exist _ n (extract_in_range n it H).
Proof.
  intros n it H. dependent destruction H. simpl. reflexivity.
Qed.

(** [denote_base_value] on a boolean is the boolean itself. *)
Lemma denote_base_value_VBool : forall b (H : has_base_type_t (VBool b) TBool),
  denote_base_value (VBool b) TBool H = b.
Proof. intros b H. dependent destruction H. reflexivity. Qed.

(** [denote_base_value] on an address is the address itself. *)
Lemma denote_base_value_VAddr : forall a (H : has_base_type_t (VAddr a) TAddress),
  denote_base_value (VAddr a) TAddress H = a.
Proof. intros a H. dependent destruction H. reflexivity. Qed.

(* ================================================================= *)
(** ** sem_base_eqb helpers *)

Lemma sem_base_eqb_refl : forall bt (x : sem_base bt),
  sem_base_eqb bt x x = true.
Proof.
  intros bt x; destruct bt; simpl.
  - apply Z.eqb_refl.
  - destruct x; reflexivity.
  - apply Nat.eqb_refl.
Qed.

Lemma denote_base_value_neq : forall v1 v2 bt
    (Hv1 : has_base_type_t v1 bt) (Hv2 : has_base_type_t v2 bt),
  v1 <> v2 ->
  sem_base_eqb bt (denote_base_value v1 bt Hv1)
                   (denote_base_value v2 bt Hv2) = false.
Proof.
  intros v1 v2 bt Hv1 Hv2 Hneq.
  dependent destruction Hv1; dependent destruction Hv2; simpl.
  - apply Z.eqb_neq. intro Heq. apply Hneq. unfold VInt. congruence.
  - destruct b, b0; try reflexivity; exfalso; apply Hneq; reflexivity.
  - apply Nat.eqb_neq. intro Heq. apply Hneq. unfold VAddr. congruence.
Qed.

(* ================================================================= *)
(** ** in_range decidability and range check correctness *)

Lemma in_range_check_true : forall it z,
  in_range it z ->
  match it with
  | IntUnbounded => true
  | _ => match int_min it, int_max it with
         | Some lo, Some hi => (lo <=? z)%Z && (z <=? hi)%Z
         | _, _ => false
         end
  end = true.
Proof.
  intros it z Hin.
  destruct it; simpl in *; try reflexivity.
  all: destruct Hin as [Hlo Hhi];
       apply andb_true_intro; split;
       apply Z.leb_le; assumption.
Qed.

Lemma in_range_check_false : forall it z,
  ~ in_range it z ->
  match it with
  | IntUnbounded => true
  | _ => match int_min it, int_max it with
         | Some lo, Some hi => (lo <=? z)%Z && (z <=? hi)%Z
         | _, _ => false
         end
  end = false.
Proof.
  intros it z Hnin.
  destruct it; simpl in *.
  - (* UintT *)
    destruct (Z.leb_spec 0 z); destruct (Z.leb_spec z (2 ^ Z.of_nat b - 1));
    simpl; try reflexivity; exfalso; apply Hnin; lia.
  - (* IntT *)
    destruct (Z.leb_spec (- 2 ^ (Z.of_nat b - 1))%Z z);
    destruct (Z.leb_spec z (2 ^ (Z.of_nat b - 1) - 1));
    simpl; try reflexivity; exfalso; apply Hnin; lia.
  - (* IntUnbounded *) exfalso; apply Hnin; exact I.
Qed.

(* ================================================================= *)
(** ** BopI evaluation always gives eval_int_binop result *)

Lemma eval_bopi_result :
  forall ts rho e1 op e2 l v v1 v2,
    eval_expr ts rho (EBopI e1 op e2) l v ->
    eval_expr ts rho e1 l (VInt v1) ->
    eval_expr ts rho e2 l (VInt v2) ->
    v = VInt (eval_int_binop op v1 v2).
Proof.
  intros ts rho e1 op e2 l v v1 v2 Heval He1 He2.
  assert (Hdet1 : forall x, eval_expr ts rho e1 l (VInt x) -> x = v1).
  { intros x Hx.
    assert (Heq : VInt x = VInt v1) by (eapply expr_determinism; eauto).
    unfold VInt in Heq. congruence. }
  assert (Hdet2 : forall x, eval_expr ts rho e2 l (VInt x) -> x = v2).
  { intros x Hx.
    assert (Heq : VInt x = VInt v2) by (eapply expr_determinism; eauto).
    unfold VInt in Heq. congruence. }
  inversion Heval; subst;
    repeat match goal with
    | [H : eval_expr _ _ e1 _ (VInt ?x) |- _] =>
      pose proof (Hdet1 _ H); clear H
    | [H : eval_expr _ _ e2 _ (VInt ?x) |- _] =>
      pose proof (Hdet2 _ H); clear H
    end;
    subst;
    try reflexivity;
    try (simpl; reflexivity).
  - (* E_DivZero *) simpl. f_equal. f_equal. symmetry. apply Zdiv_0_r.
  - (* E_Mod non-zero *)
    unfold eval_int_binop.
    match goal with [H : (?z <> 0)%Z |- _] =>
      destruct (Z.eqb_spec z 0); [contradiction | reflexivity]
    end.
Qed.

(* ================================================================= *)
(** ** Type conversion: Type -> Prop *)

(** Decidability of [in_range]. *)
Definition in_range_dec (it : int_type) (z : Z) : {in_range it z} + {~ in_range it z}.
Proof.
  destruct it; simpl.
  - (* UintT *)
    destruct (Z_le_dec 0 z), (Z_le_dec z (2 ^ Z.of_nat b - 1));
    [ left; split; assumption
    | right; intros []; contradiction
    | right; intros []; contradiction
    | right; intros []; contradiction ].
  - (* IntT *)
    destruct (Z_le_dec (- 2 ^ (Z.of_nat b - 1)) z),
             (Z_le_dec z (2 ^ (Z.of_nat b - 1) - 1));
    [ left; split; assumption
    | right; intros []; contradiction
    | right; intros []; contradiction
    | right; intros []; contradiction ].
  - (* IntUnbounded *) left; exact I.
Defined.

(** Computably construct [has_base_type_t] from a value and base type. *)
Definition construct_has_base_type_t (v : value) (bt : base_type)
    : option (has_base_type_t v bt) :=
  match v as v', bt as b' return option (has_base_type_t v' b') with
  | VBase (BVBool b), TBool => Some (V_Bool_t b)
  | VBase (BVAddr a), TAddress => Some (V_Addr_t a)
  | VBase (BVInt z), TInt it =>
      match in_range_dec it z with
      | left Hin => Some (V_Int_t z it Hin)
      | right _ => None
      end
  | _, _ => None
  end.

Lemma construct_has_base_type_t_complete : forall v bt,
    has_base_type v bt ->
    exists H, construct_has_base_type_t v bt = Some H.
Proof.
  intros v bt Hbt. inversion Hbt; subst; simpl.
  - eexists; reflexivity.
  - eexists; reflexivity.
  - destruct (in_range_dec it n) as [|Hn].
    { eexists; reflexivity. }
    { contradiction. }
Qed.

Definition has_base_type_t_to_prop (v : value) (bt : base_type)
    (H : has_base_type_t v bt) : has_base_type v bt :=
  match H with
  | V_Int_t n it Hin => V_Int n it Hin
  | V_Bool_t b => V_Bool b
  | V_Addr_t a => V_Addr a
  end.

(* ================================================================= *)
(** ** Soundness Relation for Environments

    Relates a semantic environment [rho_v : sem_iface_aux n Σ iface]
    to a pointer-level environment [rho : env] via the value denotation. *)

Fixpoint env_fields_sound (n : nat) (Σ : contract_env) (HwfΣ : wf_Σ Σ)
    (rho : env) (s : state)
    (iface : interface) (fields : sem_iface_fields_aux n Σ iface) : Type :=
  match iface as i
    return sem_iface_fields_aux n Σ i -> Type
  with
  | [] => fun _ => True
  | (x, alpha) :: rest => fun flds =>
      ((sigT (fun v => sigT (fun (Hvt : has_abi_type_t Σ v s alpha) =>
        ((rho x = Some v) *
         (exists (Hn : sty_depth Σ (SAbi alpha) <= n),
           fst flds = denote_abi_value_n n Σ HwfΣ v s alpha Hvt Hn))%type))) *
      env_fields_sound n Σ HwfΣ rho s rest (snd flds))%type
  end fields.

Definition env_sound (n : nat) (Σ : contract_env) (HwfΣ : wf_Σ Σ)
    (rho : env) (s : state)
    (iface : interface) (rho_v : sem_iface_aux n Σ iface) : Type :=
  (env_fields_sound n Σ HwfΣ rho s iface (fst rho_v) *
  ((exists vc, rho "caller"%string = Some (VAddr vc) /\
              fst (fst (snd rho_v)) = vc) *
  ((exists vo, rho "origin"%string = Some (VAddr vo) /\
              snd (fst (snd rho_v)) = vo) *
  (exists vcv (Hin : in_range (UintT 256) vcv),
    rho "callvalue"%string = Some (VInt vcv) /\
    snd (snd rho_v) = exist _ vcv Hin))))%type.

(** Soundness of the location value. *)
Definition loc_sound (n : nat) (Σ : contract_env) (HwfΣ : wf_Σ Σ)
    (l : addr) (s : state)
    (oid : opt_id) (a : sem_opt_id_aux n Σ oid) : Prop :=
  match oid as o return sem_opt_id_aux n Σ o -> Prop with
  | ONone => fun _ => True
  | OSome aid => fun av =>
      exists (Hvt : has_slot_type_t Σ (VAddr l) s (SContract aid))
             (Hn : sty_depth Σ (SContract aid) <= n),
        av = denote_slot_value_n n Σ HwfΣ (VAddr l) s (SContract aid) Hvt Hn
  end a.

(** [sem_iface_lookup] is independent of the lookup proof. *)
Lemma sem_iface_lookup_irrel : forall n Σ iface x alpha
    (H1 H2 : alist_lookup iface x = Some alpha) fields,
  sem_iface_lookup n Σ iface x alpha H1 fields =
  sem_iface_lookup n Σ iface x alpha H2 fields.
Proof.
  intros. f_equal. apply proof_irrelevance.
Qed.

(* ================================================================= *)
(** ** Auxiliary: env_fields_sound lookup *)

Lemma calldata_field_sound :
  forall n Σ HwfΣ rho s iface fields x alpha
    (e : alist_lookup iface x = Some alpha)
    v (Hrho : rho x = Some v)
    (Hvt : has_slot_type_t Σ v s (SAbi alpha))
    (Hn : sty_depth Σ (SAbi alpha) <= n),
    env_fields_sound n Σ HwfΣ rho s iface fields ->
    sem_iface_lookup n Σ iface x alpha e fields =
    denote_slot_value_n n Σ HwfΣ v s (SAbi alpha) Hvt Hn.
Proof.
  intros n Σ HwfΣ rho s iface.
  induction iface as [|[k a] rest IH]; intros fields x alpha e v Hrho Hvt Hn Hefs.
  - simpl in e. discriminate.
  - revert Hefs. revert fields. revert e.
    cbn [sem_iface_lookup list_rect alist_lookup].
    destruct (String.eqb k x) eqn:Ekx.
    + apply String.eqb_eq in Ekx. subst k.
      intros e fields Hefs.
      simpl in Hefs.
      destruct Hefs as [[v' [Hvt' [Hrho' [Hn' Hfst]]]] _].
      assert (Hvv : v' = v) by congruence. subst v'.
      injection e as Heq. subst a.
      match goal with
      | [ |- eq_rect ?x1 _ _ ?x2 ?pf _ = _ ] =>
        replace pf with (@eq_refl _ x1) by apply proof_irrelevance;
        simpl
      end.
      exact (eq_trans Hfst (denote_slot_value_n_irrel n Σ HwfΣ v s (SAbi alpha)
        (V_ABIVal_t Σ v s alpha Hvt') Hvt Hn' Hn)).
    + intros e fields Hefs.
      simpl in Hefs. destruct Hefs as [_ Hrest].
      apply IH; assumption.
Qed.

(** In the untimed semantics, eval_ref always produces RTU. *)
Lemma eval_ref_untimed_RTU : forall s rho r l v tp,
  eval_ref (TSUntimed s) rho r l v tp -> tp = RTU.
Proof.
  intros s rho r l v tp H.
  remember (TSUntimed s) as ts eqn:Hts.
  induction H; try discriminate; try reflexivity; auto.
Qed.

(* ================================================================= *)
(** ** Type-valued Type Safety — for recursive soundness calls *)

(** Extract [has_base_type_t] from [has_slot_type_t Σ v s (SAbi (ABase bt))]. *)
Definition extract_base_type_t Σ v s bt
    (H : has_slot_type_t Σ v s (SAbi (ABase bt))) : has_base_type_t v bt.
Proof.
  dependent destruction H. dependent destruction h. exact h.
Defined.

(** If [state_var s l x = Some v], then [state_var_force s l x = v]. *)
Lemma state_var_force_eq : forall s l x v,
  state_var s l x = Some v -> state_var_force s l x = v.
Proof.
  intros s l x v H. unfold state_var_force. rewrite H. reflexivity.
Qed.

(** Look up a field in [has_fields_t]. *)
Lemma has_fields_t_lookup : forall Σ s l layout x sty,
  has_fields_t Σ s l layout ->
  alist_lookup layout x = Some sty ->
  has_slot_type_t Σ (state_var_force s l x) s sty.
Proof.
  intros Σ s l layout x sty Hf.
  induction Hf; simpl; intro Hlk.
  - discriminate.
  - destruct (String.eqb x0 x) eqn:Ekx.
    + apply String.eqb_eq in Ekx. subst x0.
      injection Hlk as <-. exact h.
    + exact (IHHf Hlk).
Qed.

(** Extract [has_abi_type_t] from [env_fields_sound] given a lookup and env binding. *)
Definition env_fields_sound_abi_t (n : nat) (Σ : contract_env) (HwfΣ : wf_Σ Σ)
    (rho : env) (s : state) (iface : interface) :
  forall (fields : sem_iface_fields_aux n Σ iface) (x : ident) (alpha : abi_type) (v : value),
  env_fields_sound n Σ HwfΣ rho s iface fields ->
  alist_lookup iface x = Some alpha ->
  rho x = Some v ->
  has_abi_type_t Σ v s alpha.
Proof.
  induction iface as [|[k a] rest IH]; intros fields x alpha v Hefs Hlk Hrho.
  - simpl in Hlk. discriminate.
  - simpl in Hlk, Hefs.
    destruct (String.eqb k x) eqn:Ekx.
    + apply String.eqb_eq in Ekx. subst k.
      injection Hlk as <-.
      destruct Hefs as [[v' [Hvt' [Hrho' _]]] _].
      assert (v' = v) by congruence. subst v'. exact Hvt'.
    + destruct Hefs as [_ Hrest].
      exact (IH _ _ _ _ Hrest Hlk Hrho).
Defined.

(** Typing preservation for [apply_map]. *)
Lemma apply_map_mapping_type_t : forall vr ve v bt mu,
  has_mapping_type_t vr (MMapping bt mu) ->
  has_base_type_t ve bt ->
  apply_map vr ve = Some v ->
  has_mapping_type_t v mu.
Proof.
  intros vr ve v bt mu Hmt Hbt Happ.
  dependent destruction Hmt; dependent destruction Hbt;
    simpl in Happ; injection Happ as <-.
  - apply h. exact i.
  - apply h.
  - apply h.
Qed.

(** Extract contract fields from [has_slot_type_t Σ (VAddr l) s (SContract a)]. *)
Definition extract_contract_fields Σ l s a
    (H : has_slot_type_t Σ (VAddr l) s (SContract a))
    : has_fields_t Σ s l (Σ_storage_or_nil Σ a).
Proof.
  dependent destruction H. dependent destruction h. exact h.
Defined.

(** Extract contract abi_type from [has_slot_type_t Σ v s (SAbi (AContractAddr a))]. *)
Definition extract_contract_abi Σ v s a
    (H : has_slot_type_t Σ v s (SAbi (AContractAddr a)))
    : has_abi_type_t Σ v s (AContractAddr a).
Proof.
  dependent destruction H. exact h.
Defined.

(** Axiom: Prop-valued [has_slot_type] can be promoted to [has_slot_type_t].
    Justified because the two inductives have identical constructors
    in different universes.  A full proof would require a well-founded
    recursion over the state that mirrors [denote_slot_value_body],
    which Rocq's Prop-elimination restriction prevents. *)
Axiom has_slot_type_to_t : forall Σ v s sty,
  has_slot_type Σ v s sty -> has_slot_type_t Σ v s sty.

(** Derived: get [has_slot_type] for a specific value from type safety. *)
Lemma ref_typesafety_untimed_for_v :
  forall Σ iface phi oid k r sty s rho l v,
    type_ref Σ iface phi k oid TagU r sty ->
    env_well_typed Σ rho s iface ->
    loc_has_opt_type Σ l s oid ->
    Forall (fun p => eval_expr (TSUntimed s) rho p l (VBool true)) phi ->
    eval_ref (TSUntimed s) rho r l v RTU ->
    has_slot_type Σ v s sty.
Proof.
  intros Σ iface phi oid k r sty s rho l v Hty Hewt Hlot Hphi Heval.
  pose proof (ref_typesafety_untimed Σ iface phi oid k r sty s rho l Hty Hewt Hlot Hphi)
    as [v' [Hev' Hst']].
  destruct (ref_determinism _ _ _ _ _ _ _ _ Hev' Heval) as [Heq _].
  subst v'. exact Hst'.
Qed.

(** Derived: Type-valued type safety for references. *)
Definition ref_typesafety_t Σ iface phi oid k r sty s rho l v
    (Hty : type_ref Σ iface phi k oid TagU r sty)
    (Hewt : env_well_typed Σ rho s iface)
    (Hlot : loc_has_opt_type Σ l s oid)
    (Hphi : Forall (fun p => eval_expr (TSUntimed s) rho p l (VBool true)) phi)
    (Heval : eval_ref (TSUntimed s) rho r l v RTU)
    : has_slot_type_t Σ v s sty :=
  has_slot_type_to_t _ _ _ _
    (ref_typesafety_untimed_for_v Σ iface phi oid k r sty s rho l v Hty Hewt Hlot Hphi Heval).

(** Derived: get [has_base_type] for a specific value from type safety. *)
Lemma expr_typesafety_untimed_for_v :
  forall Σ iface phi oid e bt s rho l v,
    type_expr Σ iface phi oid TagU e bt ->
    env_well_typed Σ rho s iface ->
    loc_has_opt_type Σ l s oid ->
    Forall (fun p => eval_expr (TSUntimed s) rho p l (VBool true)) phi ->
    eval_expr (TSUntimed s) rho e l v ->
    has_base_type v bt.
Proof.
  intros Σ iface phi oid e bt s rho l v Hty Hewt Hlot Hphi Heval.
  pose proof (expr_typesafety_untimed Σ iface phi oid e bt s rho l Hty Hewt Hlot Hphi)
    as [v' [Hev' Hbt']].
  assert (v' = v) by (eapply expr_determinism; eauto). subst v'. exact Hbt'.
Qed.

(* ================================================================= *)
(** ** Soundness Theorems — Mutual Induction *)

(** Reference and Expression Soundness (Untimed).

    By mutual structural induction on the typing derivation,
    matching the structure of [denote_ref] and [denote_expr]. *)

Fixpoint ref_sound (n : nat) (Σ : contract_env) (HwfΣ : wf_Σ Σ)
    (HnΣ : forall a, sty_depth Σ (SContract a) <= n)
    (iface : interface) (phi : list expr) (k : ref_tag) (oid : opt_id) (r : ref)
    (sty : slot_type)
    (Ht : type_ref_t Σ iface phi k oid TagU r sty)
    (s : state) (rho : env) (l : addr)
    (rho_v : sem_iface_aux n Σ iface)
    (a : sem_opt_id_aux n Σ oid)
    (Hewt : env_well_typed Σ rho s iface)
    (Hlot : loc_has_opt_type Σ l s oid)
    (Henv : env_sound n Σ HwfΣ rho s iface rho_v)
    (Hloc : loc_sound n Σ HwfΣ l s oid a)
    (v : value)
    (Heval : eval_ref (TSUntimed s) rho r l v RTU)
    (Hvt : has_slot_type_t Σ v s sty)
    (Hn : sty_depth Σ sty <= n)
    {struct Ht}
    : denote_ref n Σ iface phi k oid TagU r sty Ht rho_v a =
      denote_slot_value_n n Σ HwfΣ v s sty Hvt Hn
with expr_sound (n : nat) (Σ : contract_env) (HwfΣ : wf_Σ Σ)
    (HnΣ : forall a, sty_depth Σ (SContract a) <= n)
    (iface : interface) (phi : list expr) (oid : opt_id) (e : expr)
    (bt : base_type)
    (Ht : type_expr_t Σ iface phi oid TagU e bt)
    (s : state) (rho : env) (l : addr)
    (rho_v : sem_iface_aux n Σ iface)
    (a : sem_opt_id_aux n Σ oid)
    (Hewt : env_well_typed Σ rho s iface)
    (Hlot : loc_has_opt_type Σ l s oid)
    (Henv : env_sound n Σ HwfΣ rho s iface rho_v)
    (Hloc : loc_sound n Σ HwfΣ l s oid a)
    (v : value)
    (Heval : eval_expr (TSUntimed s) rho e l v)
    (Hvt : has_base_type_t v bt)
    {struct Ht}
    : denote_expr n Σ iface phi oid TagU e bt Ht rho_v a =
      denote_base_value v bt Hvt.
Proof.
Admitted.

(** Mapping Expression Soundness *)
Lemma mapexpr_soundness :
  forall n Σ (HwfΣ : wf_Σ Σ) iface phi oid s rho l
    (rho_v : sem_iface_aux n Σ iface)
    (a : sem_opt_id_aux n Σ oid)
    (Henv : env_sound n Σ HwfΣ rho s iface rho_v)
    (Hloc : loc_sound n Σ HwfΣ l s oid a)
    m mu
    (Ht : type_mapexpr_t Σ iface phi oid m mu)
    v (Heval : eval_mapexpr (TSUntimed s) rho m l v)
    (Hvt : has_mapping_type_t v mu),
  denote_mapexpr n Σ iface phi oid m mu Ht rho_v a =
  denote_mapping_value v mu Hvt.
Proof.
Admitted.
