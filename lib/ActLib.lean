-- Library to be included with user Lean developments
-- Translated from ActLib.v

import Mathlib.Data.Int.Basic
import Mathlib.Logic.Relation

namespace ActLib

-- * Type definitions
abbrev address : Type := ℤ

-- * Environment record
structure Env where
  Callvalue : ℤ
  Caller : address
  Origin : address

def CallEnv (value : ℤ) (caller : address) (ENV : Env) : Env :=
  { Callvalue := value
    Caller := caller
    Origin := ENV.Origin }

-- * Integer bounds
def UINT_MIN (n : ℤ) : ℤ := 0
def UINT_MAX (n : ℤ) : ℤ := 2^n.toNat - 1
def INT_MIN (n : ℤ) : ℤ := 0 - 2^(n.toNat - 1)
def INT_MAX (n : ℤ) : ℤ := 2^(n.toNat - 1) - 1

-- * Notations
-- Note: bool_eq would be == in Lean
def range256 (n : ℤ) : Prop := 0 ≤ n ∧ n ≤ UINT_MAX 256

-- * Predicates
-- Multistep is the reflexive transitive closure
def multistep {A : Type} (step : A → A → Prop) : A → A → Prop :=
  Relation.ReflTransGen step

-- * Lemmas

theorem step_multi_step {A : Type} (step : A → A → Prop) (P : A → A → Prop) :
  (∀ s s', step s s' → P s s') →
  Reflexive P →
  Transitive P →
  (∀ s s', multistep step s s' → P s s') := by
  intro Hstep Hrefl Htrans s s' Hmulti
  induction Hmulti with
  | refl => exact Hrefl s
  | tail _ Hstep' IH =>
    apply Htrans
    exact IH
    exact Hstep _ _ Hstep'

theorem ite_true {A : Type} : ∀ (b : Bool) (x y z : A),
  ((if b then x else y) = z) → (z ≠ y) → (b = true) := by
  intro b x y z Heq Hneq
  cases b with
  | true => rfl
  | false =>
    simp at Heq
    rw [Heq] at Hneq
    contradiction

theorem ite_false {A : Type} : ∀ (b : Bool) (x y z : A),
  ((if b then x else y) = z) → (z ≠ x) → (b = false) := by
  intro b x y z Heq Hneq
  cases b with
  | true =>
    simp at Heq
    rw [Heq] at Hneq
    contradiction
  | false => rfl

theorem ite_dec {A : Type} : ∀ (b : Bool) (x y : A),
  let ite := if b then x else y
  ite = x ∨ ite = y := by
  intro b x y
  cases b <;> simp

end ActLib
