(** * Partial Maps
    Lightweight partial-map library used throughout the development. *)

From Stdlib Require Import String List.
Import ListNotations.

Definition ident := string.

Definition partial_map (A : Type) := ident -> option A.

Definition empty {A : Type} : partial_map A := fun _ => None.

Definition update {A : Type} (m : partial_map A) (x : ident) (v : A) : partial_map A :=
  fun y => if String.eqb x y then Some v else m y.

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).
Notation "x '|->' v" := (update empty x v)
  (at level 100).

Definition dom {A : Type} (m : partial_map A) (x : ident) : Prop :=
  exists v, m x = Some v.

Definition includes {A : Type} (m1 m2 : partial_map A) : Prop :=
  forall x v, m1 x = Some v -> m2 x = Some v.

Lemma update_eq : forall A (m : partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros. unfold update. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma update_neq : forall A (m : partial_map A) x1 x2 v,
  x1 <> x2 -> (update m x1 v) x2 = m x2.
Proof.
  intros. unfold update.
  destruct (String.eqb_spec x1 x2); [contradiction | reflexivity].
Qed.

(** Association-list maps for finite environments *)
Definition alist (A : Type) := list (ident * A).

Fixpoint alist_lookup {A : Type} (l : alist A) (x : ident) : option A :=
  match l with
  | [] => None
  | (k, v) :: rest => if String.eqb k x then Some v else alist_lookup rest x
  end.

Definition alist_dom {A : Type} (l : alist A) (x : ident) : Prop :=
  exists v, alist_lookup l x = Some v.

Definition alist_to_map {A : Type} (l : alist A) : partial_map A :=
  alist_lookup l.

Lemma alist_lookup_In : forall A (l : alist A) x v,
  alist_lookup l x = Some v ->
  exists p, In p l /\ snd p = v.
Proof.
  intros A l. induction l as [|h t IH]; intros x v Hlook.
  - discriminate.
  - simpl in Hlook. destruct h as [k w].
    destruct (String.eqb_spec k x).
    + injection Hlook as ->. exists (k, v). split; [left; auto|auto].
    + destruct (IH x v Hlook) as [p [Hin Hp]].
      exists p. split; [right; auto|auto].
Qed.

Lemma includes_refl : forall A (m : partial_map A), includes m m.
Proof. intros A m x v H. exact H. Qed.

Lemma includes_trans : forall A (m1 m2 m3 : partial_map A),
  includes m1 m2 -> includes m2 m3 -> includes m1 m3.
Proof. intros A m1 m2 m3 H12 H23 x v Hx. apply H23. apply H12. exact Hx. Qed.

Lemma includes_update_fresh : forall A (m : partial_map A) x v,
  ~ dom m x -> includes m (update m x v).
Proof.
  intros A m x v Hfresh y w Hy.
  unfold update. destruct (String.eqb_spec x y).
  - subst. exfalso. apply Hfresh. exists w. exact Hy.
  - exact Hy.
Qed.

(** alist_lookup of a cons is definitionally Maps.update *)
Lemma alist_cons_update : forall A (x : ident) (v : A) (l : alist A),
  alist_lookup ((x, v) :: l) = update (alist_lookup l) x v.
Proof. reflexivity. Qed.

Lemma alist_cons_eq : forall A (x : ident) (v : A) (l : alist A),
  alist_lookup ((x, v) :: l) x = Some v.
Proof. intros. simpl. rewrite String.eqb_refl. reflexivity. Qed.

Lemma alist_cons_neq : forall A (x y : ident) (v : A) (l : alist A),
  x <> y -> alist_lookup ((x, v) :: l) y = alist_lookup l y.
Proof.
  intros. simpl. destruct (String.eqb_spec x y); [contradiction|reflexivity].
Qed.

Lemma alist_empty_lookup : forall A (x : ident),
  @alist_lookup A [] x = None.
Proof. reflexivity. Qed.

(** alist_lookup on app *)
Lemma alist_lookup_app_some : forall A (l1 l2 : alist A) x v,
  alist_lookup l1 x = Some v ->
  alist_lookup (l1 ++ l2) x = Some v.
Proof.
  intros A l1. induction l1 as [|[k w] t IH]; intros l2 x v H.
  - discriminate.
  - simpl in *. destruct (String.eqb k x); auto.
Qed.

Lemma alist_lookup_app_none : forall A (l1 l2 : alist A) x,
  alist_lookup l1 x = None ->
  alist_lookup (l1 ++ l2) x = alist_lookup l2 x.
Proof.
  intros A l1. induction l1 as [|[k w] t IH]; intros l2 x H.
  - reflexivity.
  - simpl in *. destruct (String.eqb k x); [discriminate | auto].
Qed.

Lemma alist_lookup_app : forall A (l1 l2 : alist A) x,
  alist_lookup (l1 ++ l2) x =
  match alist_lookup l1 x with Some v => Some v | None => alist_lookup l2 x end.
Proof.
  intros A l1. induction l1 as [|[k w] t IH]; intros l2 x; simpl.
  - reflexivity.
  - destruct (String.eqb k x); auto.
Qed.

(** alist_lookup on combine *)
Lemma alist_lookup_combine : forall A B (ks : list ident) (vs : list A)
  (iface : list (ident * B)) x b,
  ks = map fst iface ->
  length vs = length iface ->
  alist_lookup iface x = Some b ->
  exists v, alist_lookup (combine ks vs) x = Some v.
Proof.
  intros A B ks vs iface x b Hks Hlen.
  subst ks. generalize dependent vs.
  induction iface as [|[k w] t IH]; intros vs Hlen Hlk.
  - discriminate.
  - destruct vs as [|v vt]; [simpl in Hlen; discriminate|].
    simpl in *. injection Hlen as Hlen.
    destruct (String.eqb k x).
    + eexists; reflexivity.
    + eauto.
Qed.

(** dom on alist_lookup app *)
Lemma alist_dom_app_l : forall A (l1 l2 : alist A) x,
  alist_dom l1 x -> alist_dom (l1 ++ l2) x.
Proof.
  intros A l1 l2 x [v Hv]. exists v. apply alist_lookup_app_some. exact Hv.
Qed.

Lemma alist_dom_app_r : forall A (l1 l2 : alist A) x,
  alist_dom l2 x ->
  alist_dom (l1 ++ l2) x.
Proof.
  intros A l1 l2 x [v Hv].
  destruct (alist_lookup l1 x) eqn:E.
  - exists a. apply alist_lookup_app_some. exact E.
  - exists v. rewrite alist_lookup_app_none; auto.
Qed.
