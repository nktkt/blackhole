import BlackHole.QuadraticGravity
import Mathlib.Computability.Halting

/-!
# Exact classification when theory parameters are given by computable reals

Fix the Schwarzschild radius at 4 and the Lagrangian at R−2Λ+αR². A finite
program describes α by dyadic approximations with a proved error bound. There
is no total computable decision for (51) on all such descriptions. The
representation of α matters. In particular, the conclusion does not apply to
the special input format of a rational numerator and denominator.
-/

set_option autoImplicit false

namespace BlackHole.ComputableCouplings

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval evaln evaln_complete primrec_evaln)
open BlackHole.StaticSpherical (flatVolume Hierarchy)
open BlackHole.QuadraticGravity (area mass massAtEntropy flat_hierarchy_iff)

private def seen (c : Code) (k : ℕ) : Bool := (evaln k c 0).isSome

private def step (c : Code) (z : ℕ × Option ℕ) : Option ℕ :=
  Option.casesOn z.2 (bif seen c z.1 then some z.1 else none) some

/-- Returns the first successful simulation among the first N cutoffs. -/
def dyadicCode (c : Code) : ℕ → Option ℕ :=
  Nat.rec none fun k prev => step c (k, prev)

theorem dyadicCode_primrec : Primrec₂ dyadicCode := by
  apply Primrec.nat_rec (Primrec.const none)
  change Primrec fun a : Code × (ℕ × Option ℕ) =>
    (Option.casesOn a.2.2 (bif seen a.1 a.2.1 then some a.2.1 else none) some : Option ℕ)
  have hk : Primrec fun a : Code × (ℕ × Option ℕ) => a.2.1 := Primrec.fst.comp Primrec.snd
  have hseen := Primrec.option_isSome.comp (primrec_evaln.comp
    ((hk.pair Primrec.fst).pair (Primrec.const 0)))
  exact Primrec.option_casesOn (Primrec.snd.comp Primrec.snd)
    (hseen.cond (Primrec.option_some.comp hk) (Primrec.const none))
    (Primrec.option_some.comp Primrec.snd)

def dyadicValue : Option ℕ → ℚ
  | none => 0
  | some k => (1 / 2 : ℚ) ^ (k + 1)

private theorem dyadicCode_seen (c : Code) (h : ∃ k, seen c k = true) (N : ℕ) :
    dyadicCode c N = if Nat.find h < N then some (Nat.find h) else none := by
  induction N with
  | zero => simp [dyadicCode]
  | succ N ih =>
    change step c (N, dyadicCode c N) = _
    rw [ih]
    by_cases hearly : Nat.find h < N
    · simp [step, hearly, Nat.lt_succ_of_lt hearly]
    · by_cases hnow : Nat.find h = N
      · have hs : seen c N = true := hnow ▸ Nat.find_spec h
        simp [step, hnow, hs]
      · have hlt : N < Nat.find h := by omega
        have hs : seen c N = false := Bool.eq_false_iff.mpr (Nat.find_min h hlt)
        simp [step, hearly, hs, show ¬Nat.find h < N + 1 by omega]

private theorem dyadicCode_unseen (c : Code) (h : ¬∃ k, seen c k = true) (N : ℕ) :
    dyadicCode c N = none := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change step c (N, dyadicCode c N) = none
    simp [step, ih, Bool.eq_false_iff.mpr (fun hs => h ⟨N, hs⟩)]

noncomputable def coupling (c : Code) : ℝ := by
  classical
  exact if h : ∃ k, seen c k = true then (1 / 2 : ℝ) ^ (Nat.find h + 1) else 0

/-- Explicit fast Cauchy name, uniform in the finite theory description. -/
theorem approximation_error (c : Code) (N : ℕ) :
    |coupling c - (dyadicValue (dyadicCode c N) : ℝ)| ≤ (1 / 2 : ℝ) ^ N := by
  by_cases h : ∃ k, seen c k = true
  · rw [coupling, dif_pos h, dyadicCode_seen c h]
    by_cases hk : Nat.find h < N
    · simp [hk, dyadicValue]
    · simp only [if_neg hk, dyadicValue, Rat.cast_zero, sub_zero, abs_of_pos (by positivity :
        0 < (1 / 2 : ℝ) ^ (Nat.find h + 1))]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  · rw [coupling, dif_neg h, dyadicCode_unseen c h]
    simp [dyadicValue]

private theorem coupling_properties (c : Code) :
    0 ≤ coupling c ∧ coupling c ≤ 1 ∧ (coupling c = 0 ↔ ¬(eval c 0).Dom) := by
  have halts : (eval c 0).Dom ↔ ∃ k, seen c k = true := by
    rw [Part.dom_iff_mem]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨k, hk⟩ := evaln_complete.mp hv
      exact ⟨k, Option.isSome_iff_exists.mpr ⟨v, hk⟩⟩
    · rintro ⟨k, hk⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
      exact ⟨v, evaln_complete.mpr ⟨k, hv⟩⟩
  rw [halts, coupling]
  split_ifs with h
  · exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num),
      iff_of_false (by positivity) (not_not.mpr h)⟩
  · simp [h]

/-- The yes/no input contains the code for the coupling, as well as the
fixed polynomial action form and the completely specified flat black hole. -/
def obeys (c : Code) : Prop :=
  Hierarchy 1 (4 * Real.pi) (area 4) (mass (coupling c) 4 0)
    (flatVolume (massAtEntropy (coupling c) 4))

theorem obeys_iff_nonhalting (c : Code) : obeys c ↔ ¬(eval c 0).Dom := by
  obtain ⟨_, hu, hz⟩ := coupling_properties c
  exact (flat_hierarchy_iff (by norm_num) (by linarith only [hu] : 12 * coupling c ≤ (4 : ℝ) ^ 2)).trans hz

/-- All encoded cases have strictly positive thermodynamic volume. -/
theorem positive_volume (c : Code) : 0 < flatVolume (massAtEntropy (coupling c) 4) := by
  rw [BlackHole.QuadraticGravity.flat_volume, BlackHole.QuadraticGravity.euclideanVolume]
  have hu := (coupling_properties c).2.1
  have hπ := mul_le_mul_of_nonneg_left hu Real.pi_pos.le
  linarith only [hπ, Real.pi_pos]

theorem no_total_classifier : ¬ComputablePred obeys := by
  intro h
  apply ComputablePred.halting_problem 0
  exact h.not.of_eq fun c => by rw [obeys_iff_nonhalting, not_not]

end BlackHole.ComputableCouplings
