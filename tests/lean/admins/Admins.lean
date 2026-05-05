import Mathlib.Data.Int.Basic
import ActLib
import Admin


open Int
open ActLib
open Asset

theorem no_admin_no_change :
  ∀ (state : State) (state' : State),
  reachable state ->
  reachable state' ->
  (∃ (ENV : Env) (NextAddr : address) (NextAddr' : address),
  transition ENV state NextAddr state' NextAddr' ∧ ENV.Caller != state.admins.admin1 ∧ ENV.Caller != state.admins.admin2) ->
  state = state'

  := by
  intro state state' h_reachable_state h_reachable_state' h_transition
  obtain ⟨ENV, NextAddr, NextAddr', h_trans, h_caller_ne_1, h_caller_ne_2⟩ := h_transition
  cases h_trans
  · sorry
  · sorry
