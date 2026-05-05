import Mathlib.Data.Int.Basic
import ActLib
import admin


open Int
open ActLib
open Asset


theorem no_admin_no_change :
  ∀ (state : State) (state' : State),
  reachable state ->
  reachable state' ->
  (∃ (ENV : Env) (NextAddr : address) (NextAddr' : address),
  transition ENV state NextAddr state' NextAddr' ∧ ENV.Caller ≠ state.admins.admin1 ∧ ENV.Caller ≠ state.admins.admin2) ->
  state = state'

  := by
  intro state state' h_reachable_state h_reachable_state' h_transition
  obtain ⟨ENV, NextAddr, NextAddr', h_trans, h_caller_ne_1, h_caller_ne_2⟩ := h_transition
  cases h_trans
  · sorry
  · sorry

lemma admins_transition_same
  {env : Env} {state state' : Admins.State}
  {NextAddr NextAddr' : address}
  (h : Admins.transition env state NextAddr state' NextAddr') :
  state = state' := by
  cases h with
  | transition_Admins h =>
    cases h with
    | admin1_Admins_transition h =>
      cases h; rfl
    | admin2_Admins_transition h =>
      cases h; rfl

-- I think that this also expresses what you want to prove. If not hopefully the structure can remain similar.
-- Not too familiar with how to shorten stuff in lean though
theorem no_admin_no_change' :
  ∀ (state : State) (state' : State) (ENV : Env) (NextAddr NextAddr' : address),
  reachable state ->
  ENV.Caller ≠ state.admins.admin1 ->
  ENV.Caller ≠ state.admins.admin2 ->
  transition ENV state NextAddr state' NextAddr' ->
  state = state'
  := by
  intro state state' env _ _ h_reachable_state h_caller_adm1 h_caller_adm2 h_transition
  cases h_transition with
  | transition_Asset h_Asset_transition =>
    cases h_Asset_transition with
    -- Lean seems to help with figuring out the constructors names for the relations in its errors,
    -- as well as give the pre-exisitng names for hypotheses as we are typing them
    | assetTransfer_Asset_transition _ _ h_assetTransfer =>
      cases h_assetTransfer with
      | assetTransfer_case0 H_conds =>
        cases H_conds with
        | assetTransfer_condsC _ H_iff2 _ _ =>
          cases H_iff2 <;> contradiction
      | assetTransfer_case1 H_conds =>
        cases H_conds with
        | assetTransfer_condsC _ H_iff2 _ _ =>
          cases H_iff2 <;> contradiction
    | setAdmins_Asset_transition _ _ h_setAdmins => 
      cases h_setAdmins with
      | setAdmins_case0 _ _ _ H_case_cond => 
        cases H_case_cond <;> contradiction
      | setAdmins_case1 =>
        rfl
    | balanceOf_Asset_transition _ h_balanceOf =>
      cases h_balanceOf with
      | balanceOf_case0 H_conds => rfl 
  | transition_admins _ h_Admins_transition h_addr h_balance h_balanceOf =>
    have h_admins_eq : state.admins = state'.admins :=
      admins_transition_same h_Admins_transition
    cases state
    cases state'
    simp at h_addr h_balance h_admins_eq h_balanceOf
    subst_vars
    rfl
