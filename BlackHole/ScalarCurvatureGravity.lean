import BlackHole.PressureResponse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# The volume shift on the constant-curvature Einstein branch of f(R) gravity

We use G=1, vary the bare cosmological constant in f(R)−2Λ, and put
P=−Λ/(8π). For an Einstein metric with constant scalar curvature R,
the conserved mass, each angular momentum, and the Wald entropy are the
Einstein values multiplied by f'(R). See
[Koga, Eqs. (6) and (47)–(48)](https://arxiv.org/html/hep-th/0505219).

The input is an Einstein enthalpy chart in pressure and the extensive variables
(S,J₁,…), with the uncharged vacuum Smarr relation at zero pressure. We keep
the physical extensive variables fixed. The trace equation supplies the
curvature near P=0 by the inverse function theorem.
-/

set_option autoImplicit false

namespace BlackHole.ScalarCurvatureGravity

open Filter Topology
open BlackHole.StaticSpherical (Hierarchy flatVolume)
open BlackHole.PressureResponse (areaVolume massVolume physical_hierarchy_iff)

/-- Flat-vacuum normalization of the action, with two derivatives at R=0.
Every C² action near zero with f(0)=0 and f'(0)=1 has these properties. -/
structure Action where
  f : ℝ → ℝ
  flat : f 0 = 0
  slope : HasStrictDerivAt f 1 0
  second : ℝ
  hasSecond : HasStrictDerivAt (deriv f) second 0

namespace Action

variable (a : Action)

private theorem polynomial_slope (α β r : ℝ) :
    HasStrictDerivAt (fun R : ℝ => R + α * R ^ 2 + β * R ^ 3)
      (1 + (2 * α) * r + (3 * β) * r ^ 2) r := by
  have h := ((hasStrictDerivAt_id r).add ((hasStrictDerivAt_pow 2 r).const_mul α)).add
    ((hasStrictDerivAt_pow 3 r).const_mul β)
  convert h using 1
  norm_num
  ring

/-- The normalized polynomial f(R)=R+αR²+βR³ realizes every value of f''(0). -/
noncomputable def polynomial (α β : ℝ) : Action where
  f R := R + α * R ^ 2 + β * R ^ 3
  flat := by simp
  slope := by simpa using polynomial_slope α β 0
  second := 2 * α
  hasSecond := by
    rw [show deriv (fun R : ℝ => R + α * R ^ 2 + β * R ^ 3) =
      (fun r => 1 + (2 * α) * r + (3 * β) * r ^ 2) from
        funext fun r => (polynomial_slope α β r).hasDerivAt.deriv]
    have h := (((hasStrictDerivAt_id (0 : ℝ)).const_mul (2 * α)).const_add 1).add
      ((hasStrictDerivAt_pow 2 (0 : ℝ)).const_mul (3 * β))
    simpa using h

noncomputable def barePressure (d R : ℝ) : ℝ :=
  ((2 / d) * (R * deriv a.f R) - a.f R) / (16 * Real.pi)

/-- P_E = pSlope D * R is the pressure in the Einstein theory for the
same Einstein metric. This slope is also the bare pressure derivative at R=0. -/
noncomputable def pSlope (d : ℝ) : ℝ := (2 - d) / (16 * Real.pi * d)

theorem trace_iff {d : ℝ} (hd : 2 < d) (R P : ℝ) :
    deriv a.f R * R - d / 2 * (a.f R + 16 * Real.pi * P) = 0 ↔
      a.barePressure d R = P := by
  have hd0 : d ≠ 0 := by linarith
  unfold barePressure
  field_simp [hd0, Real.pi_ne_zero]
  constructor <;> intro h <;> linarith only [h]

private theorem bare_zero (d : ℝ) : a.barePressure d 0 = 0 := by simp [barePressure, a.flat]

private theorem pSlope_ne {d : ℝ} (hd : 2 < d) : pSlope d ≠ 0 := by
  have hd0 : 0 < d := by linarith
  exact div_ne_zero (sub_ne_zero.mpr hd.ne) (by positivity)

private theorem bare_slope {d : ℝ} (hd : 2 < d) :
    HasStrictDerivAt (a.barePressure d) (pSlope d) 0 := by
  have h := ((((hasStrictDerivAt_id (0 : ℝ)).mul a.hasSecond).const_mul
    (2 / d)).sub a.slope).div_const (16 * Real.pi)
  convert h using 1
  simp [pSlope, a.slope.hasDerivAt.deriv]
  field_simp [Real.pi_ne_zero, show d ≠ 0 by linarith]

noncomputable def curvature {d : ℝ} (hd : 2 < d) : ℝ → ℝ :=
  (a.bare_slope hd).localInverse (a.barePressure d) (pSlope d) 0 (pSlope_ne hd)

/-- The regular flat vacuum uniquely continues locally as a scalar curvature
branch. Both inverse identities and its derivative are supplied. -/
theorem curvature_at_flat {d : ℝ} (hd : 2 < d) :
    a.curvature hd 0 = 0 ∧
    (∀ᶠ P in 𝓝 0, a.barePressure d (a.curvature hd P) = P) ∧
    (∀ᶠ R in 𝓝 0, a.curvature hd (a.barePressure d R) = R) ∧
    HasDerivAt (a.curvature hd) (pSlope d)⁻¹ 0 := by
  have hl := (a.bare_slope hd).eventually_left_inverse (pSlope_ne hd)
  have hr := (a.bare_slope hd).eventually_right_inverse (pSlope_ne hd)
  have hder := ((a.bare_slope hd).to_localInverse (pSlope_ne hd)).hasDerivAt
  rw [a.bare_zero d] at hr hder
  refine ⟨?_, hr, hl, hder⟩
  simpa [curvature, a.bare_zero d] using hl.self_of_nhds

section Enthalpy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Change from Einstein charges to physical f(R) charges before taking
the pressure derivative. x can include arbitrarily many angular momenta. -/
noncomputable def enthalpy {d : ℝ} (hd : 2 < d) (H : ℝ × E → ℝ) (x : E) (P : ℝ) : ℝ :=
  let R := a.curvature hd P
  let F := deriv a.f R
  F * H (pSlope d * R, F⁻¹ • x)

theorem flat_mass {d : ℝ} (hd : 2 < d) (H : ℝ × E → ℝ) (x : E) :
    a.enthalpy hd H x 0 = H (0, x) := by
  simp [enthalpy, (a.curvature_at_flat hd).1, a.slope.hasDerivAt.deriv]

noncomputable def shiftCoefficient (d M : ℝ) : ℝ := 16 * Real.pi * d * M / (d - 2) ^ 2

theorem shiftCoefficient_pos {d M : ℝ} (hd : 2 < d) (hM : 0 < M) :
    0 < shiftCoefficient d M := by
  have hd0 : 0 < d := by linarith
  have hden : 0 < d - 2 := sub_pos.mpr hd
  unfold shiftCoefficient
  positivity

variable {d : ℝ} {H : ℝ × E → ℝ} {dH : (ℝ × E) →L[ℝ] ℝ} {x : E}

private theorem einstein_volume (hH : HasFDerivAt H dH (0, x)) :
    flatVolume (fun P => H (P, x)) = dH (1, 0) := by
  have hpair := (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 x)
  exact (hH.comp_hasDerivAt 0 hpair).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Ici 0 0 (Set.mem_Ici.mpr le_rfl))

/-- The action dependence of the physical flat volume is exactly linear in
f''(0). The hypothesis on dH is the ordinary vacuum Einstein Smarr identity
(D−2)(TS+ΣΩᵢJᵢ)=(D−3)M at the flat solution. -/
theorem volume_shift (hd : 2 < d) (hH : HasFDerivAt H dH (0, x))
    (smarr : (d - 2) * dH (0, x) = (d - 3) * H (0, x)) :
    flatVolume (a.enthalpy hd H x) =
      flatVolume (fun P => H (P, x)) - shiftCoefficient d (H (0, x)) * a.second := by
  let R := a.curvature hd
  let F := fun P => deriv a.f (R P)
  let k := a.second * (pSlope d)⁻¹
  obtain ⟨hR0, _, _, hR⟩ := a.curvature_at_flat hd
  have hF0 : F 0 = 1 := by simp [F, R, hR0, a.slope.hasDerivAt.deriv]
  have ha' : HasDerivAt (deriv a.f) a.second (R 0) := by
    simpa [R, hR0] using a.hasSecond.hasDerivAt
  have hF : HasDerivAt F k 0 := ha'.comp 0 hR
  have hFinv : HasDerivAt (fun p => (F p)⁻¹) (-k) 0 := by
    simpa [hF0] using hF.inv (by simp [hF0])
  have hP : HasDerivAt (fun p => pSlope d * R p) 1 0 := by
    simpa [pSlope_ne hd] using hR.const_mul (pSlope d)
  have hpair := hP.prodMk (hFinv.smul_const x)
  have hstart : (0, x) = (pSlope d * R 0, (F 0)⁻¹ • x) := by simp [R, hR0, hF0]
  have he := hF.mul (hH.comp_hasDerivAt_of_eq 0 hpair hstart)
  have hV := he.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 0 (Set.mem_Ici.mpr le_rfl))
  change flatVolume (a.enthalpy hd H x) =
    k * H (pSlope d * R 0, (F 0)⁻¹ • x) + F 0 * dH (1, -k • x) at hV
  have split : ((1 : ℝ), -k • x) = (1, 0) + -k • ((0 : ℝ), x) := by simp
  rw [← hstart, hF0, one_mul, split, map_add, map_smul] at hV
  rw [hV, einstein_volume hH]
  have hsm : H (0, x) - dH (0, x) = H (0, x) / (d - 2) := by
    apply (eq_div_iff (by linarith : d - 2 ≠ 0)).mpr
    linarith only [smarr]
  change k * H (0, x) + (dH (1, 0) + -k * dH (0, x)) = _
  calc
    _ = dH (1, 0) + k * (H (0, x) - dH (0, x)) := by ring
    _ = _ := by
      rw [hsm]
      unfold k shiftCoefficient pSlope
      field_simp [show d - 2 ≠ 0 by linarith, show 2 - d ≠ 0 by linarith]
      ring

/-- Every prescribed flat volume is attained by a quadratic correction at
the same positive-mass Einstein seed. β can independently be held fixed. -/
theorem realize_volume (hd : 2 < d) (hH : HasFDerivAt H dH (0, x)) (hM : 0 < H (0, x))
    (smarr : (d - 2) * dH (0, x) = (d - 3) * H (0, x)) (β target : ℝ) :
    ∃ α : ℝ, flatVolume ((polynomial α β).enthalpy hd H x) = target := by
  let C := shiftCoefficient d (H (0, x))
  let VE := flatVolume (fun P => H (P, x))
  have hC : 0 < C := shiftCoefficient_pos hd hM
  refine ⟨(VE - target) / (2 * C), ?_⟩
  rw [volume_shift _ hd hH smarr]
  change VE - C * (2 * ((VE - target) / (2 * C))) = target
  field_simp [hC.ne']
  ring

/-- For a fixed theory, each solution has a closed admissible interval for
f''(0), determined entirely by its Einstein mass, area, and Einstein volume. -/
theorem hierarchy_iff_second {n : ℕ} (hn : 0 < n) {Ω A : ℝ} (hΩ : 0 < Ω)
    (hA : 0 ≤ A) (hH : HasFDerivAt H dH (0, x)) (hM : 0 < H (0, x))
    (smarr : ((n : ℝ) + 3 - 2) * dH (0, x) = ((n : ℝ) + 3 - 3) * H (0, x)) :
    let hd : (2 : ℝ) < n + 3 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    let M := H (0, x)
    let VE := flatVolume (fun P => H (P, x))
    let C := shiftCoefficient (n + 3) M
    (0 ≤ flatVolume (a.enthalpy hd H x) ∧
      Hierarchy n Ω A (a.enthalpy hd H x 0) (flatVolume (a.enthalpy hd H x))) ↔
      (VE - massVolume n Ω M) / C ≤ a.second ∧ a.second ≤ (VE - areaVolume n Ω A) / C := by
  have hd : (2 : ℝ) < n + 3 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hC := shiftCoefficient_pos hd hM
  dsimp only
  rw [a.flat_mass, a.volume_shift hd hH smarr, physical_hierarchy_iff hn hΩ hA hM.le,
    div_le_iff₀ hC, le_div_iff₀ hC]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith only [h₁, h₂]

end Enthalpy

end Action

end BlackHole.ScalarCurvatureGravity
