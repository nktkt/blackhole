import BlackHole.StaticSpherical
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Testing the mass–volume–area hierarchy at zero pressure

The constraint map can include the stationary field equations, boundary
conditions, entropy, and conserved charges. Only its differential and the
differential of the mass enter the test. The existence of a differentiable
branch with these data is an explicit hypothesis.
-/

set_option autoImplicit false

namespace BlackHole.PressureResponse

open Filter Topology
open BlackHole.StaticSpherical (Hierarchy flatVolume referenceVolume)
open BlackHole.MyersPerry (radius)

noncomputable def areaVolume (n : ℕ) (Ω A : ℝ) : ℝ :=
  referenceVolume n Ω (radius (n + 1) (A / Ω))

noncomputable def massVolume (n : ℕ) (Ω M : ℝ) : ℝ :=
  referenceVolume n Ω (radius n (16 * Real.pi * M / ((n + 1 : ℝ) * Ω)))

/-- The two endpoint volumes depend only on the geometric area and ADM mass. -/
theorem hierarchy_iff_volume_interval {n : ℕ} (hn : 0 < n) {Ω A M V : ℝ}
    (hΩ : 0 < Ω) (hA : 0 ≤ A) (hM : 0 ≤ M) (hV : 0 ≤ V) :
    Hierarchy n Ω A M V ↔ areaVolume n Ω A ≤ V ∧ V ≤ massVolume n Ω M := by
  let rm := radius n (16 * Real.pi * M / ((n + 1 : ℝ) * Ω))
  let rv := radius (n + 2) ((n + 2 : ℝ) * V / Ω)
  let ra := radius (n + 1) (A / Ω)
  have hm : 0 ≤ rm := Real.rpow_nonneg (by positivity) _
  have hv : 0 ≤ rv := Real.rpow_nonneg (by positivity) _
  have ha : 0 ≤ ra := Real.rpow_nonneg (by positivity) _
  have hN : 0 < (n + 2 : ℝ) := by positivity
  have pow_eq : rv ^ (n + 2) = (n + 2 : ℝ) * V / Ω :=
    Real.rpow_inv_natCast_pow (by positivity) (by omega)
  have vol_eq : referenceVolume n Ω rv = V := by
    rw [referenceVolume, pow_eq]
    field_simp [hΩ.ne', hN.ne']
  have mono {a b : ℝ} (ha' : 0 ≤ a) (hb' : 0 ≤ b) :
      referenceVolume n Ω a ≤ referenceVolume n Ω b ↔ a ≤ b := by
    unfold referenceVolume
    rw [div_le_div_iff_of_pos_right hN, mul_le_mul_iff_right₀ hΩ,
      pow_le_pow_iff_left₀ ha' hb' (by omega : n + 2 ≠ 0)]
  change (rv ≤ rm ∧ ra ≤ rv) ↔
    referenceVolume n Ω ra ≤ V ∧ V ≤ referenceVolume n Ω rm
  rw [← vol_eq, mono ha hv, mono hv hm, and_comm]

/-- Includes the real, nonnegative domain of the volume radius in the
proposition, so the test can be applied before the sign of V is known. -/
theorem physical_hierarchy_iff {n : ℕ} (hn : 0 < n) {Ω A M V : ℝ}
    (hΩ : 0 < Ω) (hA : 0 ≤ A) (hM : 0 ≤ M) :
    (0 ≤ V ∧ Hierarchy n Ω A M V) ↔ areaVolume n Ω A ≤ V ∧ V ≤ massVolume n Ω M := by
  have ha : 0 ≤ areaVolume n Ω A := by
    unfold areaVolume referenceVolume
    have := Real.rpow_nonneg (div_nonneg hA hΩ.le) (((n + 1 : ℕ) : ℝ)⁻¹)
    change 0 ≤ Ω * ((A / Ω) ^ (((n + 1 : ℕ) : ℝ)⁻¹)) ^ (n + 2) / (n + 2 : ℝ)
    positivity
  constructor
  · rintro ⟨hV, h⟩
    exact (hierarchy_iff_volume_interval hn hΩ hA hM hV).mp h
  · intro h
    exact ⟨ha.trans h.1, (hierarchy_iff_volume_interval hn hΩ hA hM (ha.trans h.1)).mpr h⟩

section Linear

variable {E Y : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup Y] [Module ℝ Y]

/-- An adjoint multiplier exists exactly when every homogeneous linearized
deformation preserves the mass. In infinite dimensions the multiplier here is
algebraic. The proof does not assert its continuity. -/
theorem multiplier_iff (L : E →ₗ[ℝ] Y) (ℓ : E →ₗ[ℝ] ℝ) :
    (∃ η : Y →ₗ[ℝ] ℝ, η.comp L = ℓ) ↔ LinearMap.ker L ≤ LinearMap.ker ℓ := by
  constructor
  · rintro ⟨η, rfl⟩ k hk
    change L k = 0 at hk
    change η (L k) = 0
    simp [hk]
  · intro h
    let g := ((LinearMap.ker L).liftQ ℓ h).comp L.quotKerEquivRange.symm.toLinearMap
    obtain ⟨η, hη⟩ := g.exists_extend
    refine ⟨η, ?_⟩
    ext x
    have h' := LinearMap.congr_fun hη (L.rangeRestrict x)
    change η (L x) = g (L.rangeRestrict x) at h'
    change η (L x) = ℓ x
    rw [h']
    change (LinearMap.ker L).liftQ ℓ h
      (L.quotKerEquivRange.symm ⟨L x, _⟩) = ℓ x
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl

/-- On a nonempty fiber, this is exactly the condition for the pressure
response to be independent of the choice of a linearized solution. -/
theorem tangent_independence_iff (L : E →ₗ[ℝ] Y) (ℓ : E →ₗ[ℝ] ℝ) (v₀ : E) :
    (∀ v, L v = L v₀ → ℓ v = ℓ v₀) ↔ LinearMap.ker L ≤ LinearMap.ker ℓ := by
  constructor
  · intro h k hk
    change L k = 0 at hk
    have heq := h (k + v₀) (by rw [map_add, hk, zero_add])
    simpa using heq
  · intro h v hv
    have hk : v - v₀ ∈ LinearMap.ker L := by
      change L (v - v₀) = 0
      rw [map_sub, hv, sub_self]
    have hout : ℓ (v - v₀) = 0 := h hk
    rwa [map_sub, sub_eq_zero] at hout

/-- If one homogeneous deformation changes the mass, its scalar multiples
realize every real mass response in the linearized fiber. -/
theorem all_tangent_values (L : E →ₗ[ℝ] Y) (ℓ : E →ₗ[ℝ] ℝ) (v₀ : E)
    (h : ¬LinearMap.ker L ≤ LinearMap.ker ℓ) (y : ℝ) :
    ∃ v, L v = L v₀ ∧ ℓ v = y := by
  have bad : ∃ k, L k = 0 ∧ ℓ k ≠ 0 := by
    by_contra! hall
    exact h (fun k hk => hall k hk)
  obtain ⟨k, hk, hℓ⟩ := bad
  refine ⟨v₀ + ((y - ℓ v₀) / ℓ k) • k, by simp [hk], ?_⟩
  rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hℓ]
  ring

/-- Complete test for the two bounds to follow from the linearized equations
alone. A nonempty fiber is required. Whether every tangent integrates to an
exact solution is a separate property of the nonlinear equations. -/
theorem all_tangents_in_interval_iff (L : E →ₗ[ℝ] Y) (ℓ : E →ₗ[ℝ] ℝ)
    (b : Y) (m lower upper : ℝ) (consistent : ∃ v, L v = -b) :
    (∀ v, L v = -b → lower ≤ m + ℓ v ∧ m + ℓ v ≤ upper) ↔
      ∃ η : Y →ₗ[ℝ] ℝ, η.comp L = ℓ ∧ lower ≤ m - η b ∧ m - η b ≤ upper := by
  obtain ⟨v₀, hv₀⟩ := consistent
  have formula {η : Y →ₗ[ℝ] ℝ} (adj : η.comp L = ℓ) {v : E} (hv : L v = -b) :
      m + ℓ v = m - η b := by simp [← adj, hv, sub_eq_add_neg]
  constructor
  · intro hall
    have hk : LinearMap.ker L ≤ LinearMap.ker ℓ := by
      by_contra h
      obtain ⟨v, hv, hm⟩ := all_tangent_values L ℓ v₀ h (lower - m - 1)
      have hlo := (hall v (hv.trans hv₀)).1
      linarith only [hlo, hm]
    obtain ⟨η, adj⟩ := (multiplier_iff L ℓ).mpr hk
    exact ⟨η, adj, by simpa only [formula adj hv₀] using hall v₀ hv₀⟩
  · rintro ⟨η, adj, bounds⟩ v hv
    rwa [formula adj hv]

end Linear

section Derivative

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A stationary solution continued from the flat endpoint into P ≥ 0.
All constraints are measured relative to their prescribed values. -/
structure Branch (E Y : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] where
  state : ℝ → E
  tangent : E
  constraint : ℝ × E → Y
  mass : ℝ × E → ℝ
  dConstraint : (ℝ × E) →L[ℝ] Y
  dMass : (ℝ × E) →L[ℝ] ℝ
  hasTangent : HasDerivWithinAt state tangent (Set.Ici 0) 0
  onShell : ∀ᶠ p in 𝓝[Set.Ici 0] 0, constraint (p, state p) = 0
  hasDConstraint : HasFDerivWithinAt constraint dConstraint (Set.Ici 0 ×ˢ Set.univ) (0, state 0)
  hasDMass : HasFDerivWithinAt mass dMass (Set.Ici 0 ×ˢ Set.univ) (0, state 0)

variable (s : Branch E Y)

/-- Every differentiable physical branch supplies one compatible tangent. -/
theorem branch_differentials : s.dConstraint (1, s.tangent) = 0 ∧
    flatVolume (fun p => s.mass (p, s.state p)) = s.dMass (1, s.tangent) := by
  let γ := fun p : ℝ => (p, s.state p)
  have hγ : HasDerivWithinAt γ (1, s.tangent) (Set.Ici 0) 0 :=
    (hasDerivAt_id 0).hasDerivWithinAt.prodMk s.hasTangent
  have hmaps : Set.MapsTo γ (Set.Ici 0) (Set.Ici 0 ×ˢ Set.univ) :=
    fun _ hp => ⟨hp, Set.mem_univ _⟩
  have hF := s.hasDConstraint.comp_hasDerivWithinAt 0 hγ hmaps
  have hm := s.hasDMass.comp_hasDerivWithinAt 0 hγ hmaps
  have hzero : HasDerivWithinAt (s.constraint ∘ γ) 0 (Set.Ici 0) 0 :=
    (hasDerivWithinAt_const 0 (Set.Ici 0) (0 : Y)).congr_of_eventuallyEq_of_mem
      s.onShell (by simp)
  have huniq := uniqueDiffOn_Ici (0 : ℝ) 0 (Set.mem_Ici.mpr le_rfl)
  exact ⟨(hF.derivWithin huniq).symm.trans (hzero.derivWithin huniq), hm.derivWithin huniq⟩

/-- Evaluate the isentropic mass derivative using just the two explicit
pressure derivatives and an adjoint multiplier for the state variation. -/
theorem flat_volume_from_adjoint (η : Y →ₗ[ℝ] ℝ)
    (adjoint : ∀ x : E, s.dMass (0, x) = η (s.dConstraint (0, x))) :
    flatVolume (fun p => s.mass (p, s.state p)) =
      s.dMass (1, 0) - η (s.dConstraint (1, 0)) := by
  obtain ⟨hDF, hm⟩ := branch_differentials s
  have split : ((1 : ℝ), s.tangent) = (1, 0) + (0, s.tangent) := by simp
  rw [split, map_add] at hDF
  have hstate : s.dConstraint (0, s.tangent) = -s.dConstraint (1, 0) :=
    eq_neg_of_add_eq_zero_right hDF
  rw [hm, split, map_add, adjoint, hstate, map_neg, sub_eq_add_neg]

/-- The test uses the theory's local derivatives as input. The unknown volume
and the branch tangent do not occur on the right-hand side. -/
theorem hierarchy_from_adjoint {n : ℕ} (hn : 0 < n) {Ω A : ℝ} (hΩ : 0 < Ω)
    (hA : 0 ≤ A) (hM : 0 ≤ s.mass (0, s.state 0)) (η : Y →ₗ[ℝ] ℝ)
    (adjoint : ∀ x : E, s.dMass (0, x) = η (s.dConstraint (0, x))) :
    (0 ≤ flatVolume (fun p => s.mass (p, s.state p)) ∧
      Hierarchy n Ω A (s.mass (0, s.state 0)) (flatVolume (fun p => s.mass (p, s.state p)))) ↔
      areaVolume n Ω A ≤ s.dMass (1, 0) - η (s.dConstraint (1, 0)) ∧
      s.dMass (1, 0) - η (s.dConstraint (1, 0)) ≤ massVolume n Ω (s.mass (0, s.state 0)) := by
  rw [flat_volume_from_adjoint s η adjoint, physical_hierarchy_iff hn hΩ hA hM]

end Derivative

end BlackHole.PressureResponse
