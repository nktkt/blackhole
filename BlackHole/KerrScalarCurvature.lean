import BlackHole.ScalarCurvatureGravity

/-!
# An explicit coupling interval for four-dimensional Kerr black holes

The uncharged Kerr–AdS enthalpy is [Dolan, Eq. (19)](https://arxiv.org/html/1106.6260#S2.E19).
We use coordinates s=S/π and j=2J. At the flat endpoint ρ=√s is the area
radius and χ=j/s is the signed dimensionless spin a/r₊. Subextremal outer
horizons have |χ|<1. The polynomial and radical identities below also extend
to the boundary of that domain.
-/

set_option autoImplicit false

namespace BlackHole.KerrScalarCurvature

open Filter Topology
open BlackHole.PressureResponse (areaVolume massVolume)
open BlackHole.StaticSpherical (Hierarchy flatVolume referenceVolume)
open BlackHole.MyersPerry (radius)
open BlackHole.ScalarCurvatureGravity (Action)
open BlackHole.ScalarCurvatureGravity.Action (shiftCoefficient)

private noncomputable def b : ℝ := 8 * Real.pi / 3

private noncomputable def radicand (z : ℝ × (ℝ × ℝ)) : ℝ :=
  let s := z.2.1
  let j := z.2.2
  let u := 1 + b * z.1 * s
  s * u ^ 2 + j ^ 2 / s * u

noncomputable def einsteinEnthalpy (z : ℝ × (ℝ × ℝ)) : ℝ := Real.sqrt (radicand z) / 2

private theorem rad_flat (s j : ℝ) : radicand (0, (s, j)) = s + j ^ 2 / s := by simp [radicand]

private theorem chart_deriv {s j : ℝ} (hs : 0 < s) :
    DifferentiableAt ℝ einsteinEnthalpy (0, (s, j)) := by
  have hpos : 0 < radicand (0, (s, j)) := by rw [rad_flat]; positivity
  have hrad : DifferentiableAt ℝ radicand (0, (s, j)) := by
    unfold radicand
    fun_prop (disch := exact hs.ne')
  unfold einsteinEnthalpy
  simp only [div_eq_mul_inv]
  exact (hrad.sqrt hpos.ne').mul (differentiableAt_const (c := (2 : ℝ)⁻¹))

private theorem chart_smarr {s j : ℝ} (hs : 0 < s)
    {dH : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ} (hH : HasFDerivAt einsteinEnthalpy dH (0, (s, j))) :
    2 * dH (0, (s, j)) = einsteinEnthalpy (0, (s, j)) := by
  let x := (s, j)
  have hom : (fun t : ℝ => einsteinEnthalpy (0, t • x)) =ᶠ[𝓝 1]
      (fun t => Real.sqrt t * einsteinEnthalpy (0, x)) := by
    filter_upwards [lt_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    have scale : (t * s) + (t * j) ^ 2 / (t * s) = t * (s + j ^ 2 / s) := by
      field_simp [ht.ne', hs.ne']
    change Real.sqrt (radicand (0, (t * s, t * j))) / 2 =
      Real.sqrt t * (Real.sqrt (radicand (0, (s, j))) / 2)
    rw [rad_flat, rad_flat, scale, Real.sqrt_mul ht.le]
    ring
  have hc := (hasDerivAt_const (1 : ℝ) (0 : ℝ)).prodMk ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have hh := hH.comp_hasDerivAt_of_eq 1 hc (by simp [x])
  have hleft : HasDerivAt (fun t : ℝ => einsteinEnthalpy (0, t • x)) (dH (0, x)) 1 := by
    simpa [Function.comp_def] using hh
  have hright := (Real.hasDerivAt_sqrt (by norm_num : (1 : ℝ) ≠ 0)).mul_const
    (einsteinEnthalpy (0, x))
  have deriv_eq := hleft.deriv.symm.trans (hom.deriv_eq.trans hright.deriv)
  norm_num [x] at deriv_eq
  linarith only [deriv_eq]

private theorem chart_volume {s j : ℝ} (hs : 0 < s) :
    flatVolume (fun P => einsteinEnthalpy (P, (s, j))) =
      Real.pi * (2 * s ^ 2 + j ^ 2) / (3 * einsteinEnthalpy (0, (s, j))) := by
  let u := fun P : ℝ => 1 + b * P * s
  have hu : HasDerivAt u (b * s) 0 := by
    simpa [u] using ((((hasDerivAt_id (0 : ℝ)).const_mul b).mul_const s).const_add 1)
  have hrad := ((hu.fun_pow 2).const_mul s).add (hu.const_mul (j ^ 2 / s))
  have hpos : 0 < s + j ^ 2 / s := by positivity
  have hh := (hrad.sqrt (by simpa [u] using hpos.ne')).div_const 2
  have hder := hh.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 0 (Set.mem_Ici.mpr le_rfl))
  change flatVolume (fun P => einsteinEnthalpy (P, (s, j))) = _ at hder
  rw [hder]
  simp [u, b, einsteinEnthalpy, rad_flat]
  field_simp [hs.ne', (Real.sqrt_pos.mpr hpos).ne']
  ring

noncomputable def spinFactor (χ : ℝ) : ℝ := Real.sqrt (1 + χ ^ 2)

private theorem spinFactor_one_le (χ : ℝ) : 1 ≤ spinFactor χ := by
  unfold spinFactor
  exact (Real.one_le_sqrt).mpr (by linarith [sq_nonneg χ])

noncomputable def physicalMass (a : Action) (ρ χ : ℝ) : ℝ → ℝ :=
  a.enthalpy (d := 4) (by norm_num) einsteinEnthalpy (ρ ^ 2, ρ ^ 2 * χ)

/-- Both ends of the allowed interval are explicit functions of area and spin.
In particular, the theorem has no assumed black-hole Smarr identity, volume
formula, or derivative. They were evaluated from the Kerr enthalpy above. -/
theorem kerr_iff (a : Action) {ρ : ℝ} (hρ : 0 < ρ) (χ : ℝ) :
    let t := spinFactor χ
    let m := physicalMass a ρ χ
    (0 ≤ flatVolume m ∧ Hierarchy 1 (4 * Real.pi) (4 * Real.pi * ρ ^ 2) (m 0) (flatVolume m)) ↔
      -(ρ ^ 2 * (t ^ 2 - 1) * (2 * t ^ 2 + 1)) / (12 * t ^ 2) ≤ a.second ∧
      a.second ≤ ρ ^ 2 * (t - 1) ^ 2 / (12 * t ^ 2) := by
  let t := spinFactor χ
  let x := (ρ ^ 2, ρ ^ 2 * χ)
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one (spinFactor_one_le χ)
  have ht2 : t ^ 2 = 1 + χ ^ 2 := Real.sq_sqrt (by positivity)
  have hmass : einsteinEnthalpy (0, x) = ρ * t / 2 := by
    have hrad : ρ ^ 2 + (ρ ^ 2 * χ) ^ 2 / ρ ^ 2 = (ρ * t) ^ 2 := by
      rw [mul_pow ρ t, ht2]
      field_simp [hρ.ne']
    rw [einsteinEnthalpy, rad_flat, hrad, Real.sqrt_sq (mul_pos hρ ht).le]
  have hM : 0 < einsteinEnthalpy (0, x) := by rw [hmass]; positivity
  have hH := (chart_deriv (j := ρ ^ 2 * χ) (sq_pos_of_pos hρ)).hasFDerivAt
  have hsm := chart_smarr (sq_pos_of_pos hρ) hH
  have test := a.hierarchy_iff_second (n := 1) (by decide) (Ω := 4 * Real.pi)
    (A := 4 * Real.pi * ρ ^ 2) (by positivity) (by positivity) hH hM (by norm_num; exact hsm)
  have hVE : flatVolume (fun P => einsteinEnthalpy (P, x)) =
      2 * Real.pi * ρ ^ 3 * (1 + t ^ 2) / (3 * t) := by
    rw [chart_volume (sq_pos_of_pos hρ), hmass]
    field_simp [hρ.ne', ht.ne']
    rw [ht2]
    ring
  have hVA : areaVolume 1 (4 * Real.pi) (4 * Real.pi * ρ ^ 2) = 4 * Real.pi * ρ ^ 3 / 3 := by
    have hr : radius 2 (ρ ^ 2) = ρ := Real.pow_rpow_inv_natCast hρ.le (by decide : 2 ≠ 0)
    norm_num [areaVolume, referenceVolume, Real.pi_ne_zero, hr]
  have hVM : massVolume 1 (4 * Real.pi) (einsteinEnthalpy (0, x)) =
      4 * Real.pi * (ρ * t) ^ 3 / 3 := by
    rw [hmass]
    have hm : 16 * Real.pi * (ρ * t / 2) / ((1 + 1 : ℝ) * (4 * Real.pi)) = ρ * t := by
      field_simp [Real.pi_ne_zero]
      norm_num
    simp [massVolume, referenceVolume, radius, hm]
    norm_num
  have hC : shiftCoefficient 4 (einsteinEnthalpy (0, x)) = 8 * Real.pi * ρ * t := by
    rw [hmass]
    unfold shiftCoefficient
    ring
  dsimp only at test ⊢
  have mass_at_four {d : ℝ} (hd : 2 < d) (he : d = 4) :
      a.enthalpy hd einsteinEnthalpy x = physicalMass a ρ χ := by
    subst d
    rfl
  rw [mass_at_four _ (by norm_num)] at test
  norm_num only [Nat.cast_one, show (1 + 3 : ℝ) = 4 by norm_num] at test
  rw [hVE, hVA, hVM, hC] at test
  apply test.trans
  have hlo : (2 * Real.pi * ρ ^ 3 * (1 + t ^ 2) / (3 * t) - 4 * Real.pi * (ρ * t) ^ 3 / 3) /
      (8 * Real.pi * ρ * t) = -(ρ ^ 2 * (t ^ 2 - 1) * (2 * t ^ 2 + 1)) / (12 * t ^ 2) := by
    field_simp [hρ.ne', ht.ne', Real.pi_ne_zero]
    ring
  have hhi : (2 * Real.pi * ρ ^ 3 * (1 + t ^ 2) / (3 * t) - 4 * Real.pi * ρ ^ 3 / 3) /
      (8 * Real.pi * ρ * t) = ρ ^ 2 * (t - 1) ^ 2 / (12 * t ^ 2) := by
    field_simp [hρ.ne', ht.ne', Real.pi_ne_zero]
    ring
  rw [hlo, hhi]

/-- The action satisfies the chain throughout the entire subextremal Kerr
family, including its nonrotating members, exactly when f''(0)=0. -/
theorem all_kerr_iff (a : Action) :
    (∀ ρ : ℝ, 0 < ρ → ∀ χ : ℝ, |χ| < 1 →
      let m := physicalMass a ρ χ
      0 ≤ flatVolume m ∧ Hierarchy 1 (4 * Real.pi) (4 * Real.pi * ρ ^ 2) (m 0) (flatVolume m)) ↔
      a.second = 0 := by
  constructor
  · intro h
    have hz := (kerr_iff a (ρ := 1) (by norm_num) 0).mp (h 1 (by norm_num) 0 (by norm_num))
    norm_num [spinFactor] at hz
    exact le_antisymm hz.2 hz.1
  · intro h ρ hρ χ _
    apply (kerr_iff a hρ χ).mpr
    rw [h]
    have ht := spinFactor_one_le χ
    have hsq : 0 ≤ spinFactor χ ^ 2 - 1 := by nlinarith only [ht, sq_nonneg (spinFactor χ - 1)]
    constructor
    · apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      exact neg_nonpos.mpr (by positivity)
    · positivity

theorem all_kerr_polynomial_iff (α β : ℝ) :
    (∀ ρ : ℝ, 0 < ρ → ∀ χ : ℝ, |χ| < 1 →
      let m := physicalMass (Action.polynomial α β) ρ χ
      0 ≤ flatVolume m ∧ Hierarchy 1 (4 * Real.pi) (4 * Real.pi * ρ ^ 2) (m 0) (flatVolume m)) ↔
      α = 0 := by
  rw [all_kerr_iff]
  change 2 * α = 0 ↔ α = 0
  norm_num

end BlackHole.KerrScalarCurvature
