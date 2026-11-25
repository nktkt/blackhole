import BlackHole.MyersPerry
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The mass–volume–area ordering for round static horizons

Equation (51) of [Mann, Pourhassan and Dehghani](https://arxiv.org/html/2609.14108v1#S5.E51)
uses ADM mass, thermodynamic volume and geometric horizon area. We take G=1,
D=n+3, and denote the unit (D−2)-sphere area by Ω.

The geometric inputs for the Lovelock–Maxwell family are the mass and entropy
in [Frassino et al., Eqs. (19)–(21)](https://arxiv.org/html/1406.7015#S2.E19).
The radius and the higher-curvature couplings are held fixed when varying
pressure. On a regular branch the Wald entropy fixes the radius locally.
The minus-branch metric, temperature and Wald entropy of the concrete example
come from [Cai, Eqs. (8), (11) and (13)](https://arxiv.org/html/hep-th/0109133#S2.E8).
-/

set_option autoImplicit false

namespace BlackHole.StaticSpherical

open BlackHole.MyersPerry (radius radius_le_iff)
open scoped BigOperators

noncomputable def massUnit (n : ℕ) (Ω : ℝ) : ℝ := (n + 1 : ℝ) * Ω / (16 * Real.pi)
noncomputable def referenceMass (n : ℕ) (Ω r : ℝ) : ℝ := massUnit n Ω * r ^ n
noncomputable def referenceVolume (n : ℕ) (Ω r : ℝ) : ℝ := Ω * r ^ (n + 2) / (n + 2 : ℝ)

/-- Equation (48), equivalently (51), with the original normalizations. -/
def Hierarchy (n : ℕ) (Ω A M V : ℝ) : Prop :=
  let rm := radius n (16 * Real.pi * M / ((n + 1 : ℝ) * Ω))
  let rv := radius (n + 2) ((n + 2 : ℝ) * V / Ω)
  let ra := radius (n + 1) (A / Ω)
  rv ≤ rm ∧ ra ≤ rv

private theorem scaled_radius {k : ℕ} (hk : k ≠ 0) {r u : ℝ} (hr : 0 ≤ r) (hu : 0 ≤ u) :
    radius k (r ^ k * u) = r * radius k u := by
  unfold radius
  rw [Real.mul_rpow (pow_nonneg hr _) hu, Real.pow_rpow_inv_natCast hr hk]

private theorem scaled_hierarchy {n : ℕ} (hn : 0 < n) {Ω r u w : ℝ}
    (hΩ : 0 < Ω) (hr : 0 < r) (hu : 0 ≤ 1 + u) (hw : 0 ≤ 1 + w) :
    Hierarchy n Ω (Ω * r ^ (n + 1)) (referenceMass n Ω r * (1 + u))
      (referenceVolume n Ω r * (1 + w)) ↔
      (1 + w) ^ n ≤ (1 + u) ^ (n + 2) ∧ 0 ≤ w := by
  have hmass : 16 * Real.pi * (referenceMass n Ω r * (1 + u)) / ((n + 1 : ℝ) * Ω)
      = r ^ n * (1 + u) := by
    unfold referenceMass massUnit
    field_simp [Real.pi_ne_zero, hΩ.ne', show (n + 1 : ℝ) ≠ 0 by positivity]
  have hvol : (n + 2 : ℝ) * (referenceVolume n Ω r * (1 + w)) / Ω =
      r ^ (n + 2) * (1 + w) := by
    unfold referenceVolume
    field_simp [hΩ.ne', show (n + 2 : ℝ) ≠ 0 by positivity]
  have harea : Ω * r ^ (n + 1) / Ω = r ^ (n + 1) := by field_simp
  have hra : radius (n + 1) (r ^ (n + 1)) = r :=
    Real.pow_rpow_inv_natCast hr.le (by omega : n + 1 ≠ 0)
  dsimp only [Hierarchy]
  rw [hmass, hvol, harea, scaled_radius hn.ne' hr.le hu, scaled_radius (by omega) hr.le hw, hra]
  change (r * radius (n + 2) (1 + w) ≤ r * radius n (1 + u) ∧
    r ≤ r * radius (n + 2) (1 + w)) ↔ _
  rw [mul_le_mul_iff_right₀ hr, radius_le_iff (by omega) hn.ne' hw hu]
  apply and_congr_right
  intro _
  calc
    r ≤ r * radius (n + 2) (1 + w) ↔ 1 ≤ radius (n + 2) (1 + w) := by
      simpa using (show r * 1 ≤ r * radius (n + 2) (1 + w) ↔ 1 ≤ radius (n + 2) (1 + w)
        from mul_le_mul_iff_right₀ hr)
    _ ↔ 1 ≤ 1 + w := by
      simpa only [radius, Real.one_rpow] using
        (Real.rpow_le_rpow_iff zero_le_one hw
          (by positivity : 0 < ((n + 2 : ℕ) : ℝ)⁻¹))
    _ ↔ 0 ≤ w := by constructor <;> intro h <;> linarith

/-- Pressure is nonnegative in the AdS family. Its derivative at the flat end
is taken from the right, with entropy, charges and other couplings fixed. -/
noncomputable def flatVolume (M : ℝ → ℝ) : ℝ := derivWithin M (Set.Ici 0) 0

private theorem flatVolume_affine (b v : ℝ) :
    flatVolume (fun P => b + P * v) = v := by
  apply HasDerivWithinAt.derivWithin _ (uniqueDiffOn_Ici 0 0 (Set.mem_Ici.mpr (le_refl (0 : ℝ))))
  simpa using (((hasDerivAt_id 0).mul_const v).const_add b).hasDerivWithinAt

/-- The radial mass balance at fixed horizon radius: C is a pressure-independent
horizon mass correction and E(P) is the exterior mass. For minimally coupled
spherical Einstein matter C=0 and E is the integral of the energy density in
areal coordinates whenever the integral gives the ADM mass outside the horizon. -/
noncomputable def sphericalEnthalpy (n : ℕ) (Ω r C : ℝ) (E : ℝ → ℝ) (P : ℝ) : ℝ :=
  referenceMass n Ω r + C + P * referenceVolume n Ω r + E P

theorem exterior_volume (n : ℕ) (Ω r C : ℝ) {E : ℝ → ℝ} {dE : ℝ}
    (hE : HasDerivWithinAt E dE (Set.Ici 0) 0) :
    flatVolume (sphericalEnthalpy n Ω r C E) = referenceVolume n Ω r + dE := by
  have hlin : HasDerivWithinAt
      (fun P : ℝ => referenceMass n Ω r + C + P * referenceVolume n Ω r)
      (referenceVolume n Ω r) (Set.Ici 0) 0 := by
    simpa using (((hasDerivAt_id 0).mul_const (referenceVolume n Ω r)).const_add
      (referenceMass n Ω r + C)).hasDerivWithinAt
  exact (hlin.add hE).derivWithin (uniqueDiffOn_Ici 0 0 (Set.mem_Ici.mpr (le_refl (0 : ℝ))))

/-- A test in terms of exterior mass and its pressure response for every
family with the radial balance above. No constancy of the matter profile as
pressure varies is assumed. -/
theorem exterior_response_iff {n : ℕ} (hn : 0 < n) {Ω r C dE : ℝ} {E : ℝ → ℝ}
    (hΩ : 0 < Ω) (hr : 0 < r) (hE : HasDerivWithinAt E dE (Set.Ici 0) 0)
    (hM : 0 ≤ referenceMass n Ω r + C + E 0) (hV : 0 ≤ referenceVolume n Ω r + dE) :
    Hierarchy n Ω (Ω * r ^ (n + 1)) (sphericalEnthalpy n Ω r C E 0)
      (flatVolume (sphericalEnthalpy n Ω r C E)) ↔
      (1 + dE / referenceVolume n Ω r) ^ n ≤
        (1 + (C + E 0) / referenceMass n Ω r) ^ (n + 2) ∧ 0 ≤ dE := by
  let m := referenceMass n Ω r
  let v := referenceVolume n Ω r
  have hm : 0 < m := by dsimp [m, referenceMass, massUnit]; positivity
  have hv : 0 < v := by dsimp [v, referenceVolume]; positivity
  have hem : m * (1 + (C + E 0) / m) = m + C + E 0 := by field_simp; ring
  have hev : v * (1 + dE / v) = v + dE := by field_simp
  have hum := (mul_nonneg_iff_of_pos_left hm).mp (hem.symm ▸ hM)
  have huw := (mul_nonneg_iff_of_pos_left hv).mp (hev.symm ▸ hV)
  rw [exterior_volume n Ω r C hE]
  simp only [sphericalEnthalpy, zero_mul, add_zero]
  change Hierarchy n Ω _ (m + C + E 0) (v + dE) ↔ _
  rw [← hem, ← hev, scaled_hierarchy hn hΩ hr hum huw]
  apply and_congr_right
  intro _
  change 0 ≤ dE / v ↔ 0 ≤ dE
  rw [le_div_iff₀ hv, zero_mul]

/-- At Lovelock order j+2 the mass correction has radial power n−2(j+1).
The rescaled Maxwell charge satisfies q²=8πQ²/((D−2)(D−3)) in Eq. (19).
Physical coefficients occur only up to floor((D−1)/2). -/
noncomputable def lovelockCorrection {k : ℕ} (n : ℕ) (r : ℝ) (α : Fin k → ℝ) (q : ℝ) : ℝ :=
  (∑ j, α j * (r ^ n / r ^ (2 * (j.val + 1)))) + q ^ 2 / r ^ n

noncomputable def lovelockMass {k : ℕ} (n : ℕ) (Ω r : ℝ) (α : Fin k → ℝ) (q P : ℝ) : ℝ :=
  massUnit n Ω * (r ^ n + lovelockCorrection n r α q) + P * referenceVolume n Ω r

theorem lovelock_volume {k : ℕ} (n : ℕ) (Ω r : ℝ) (α : Fin k → ℝ) (q : ℝ) :
    flatVolume (lovelockMass n Ω r α q) = referenceVolume n Ω r := flatVolume_affine _ _

/-- Exact classification for the static spherical Lovelock–Maxwell solutions,
on each physical branch having positive radius and nonnegative ADM mass. -/
theorem lovelock_hierarchy_iff {n k : ℕ} (hn : 0 < n) {Ω r : ℝ} (hΩ : 0 < Ω)
    (hr : 0 < r) (α : Fin k → ℝ) (q : ℝ) (hM : 0 ≤ r ^ n + lovelockCorrection n r α q) :
    Hierarchy n Ω (Ω * r ^ (n + 1)) (lovelockMass n Ω r α q 0)
      (flatVolume (lovelockMass n Ω r α q)) ↔ 0 ≤ lovelockCorrection n r α q := by
  let c := lovelockCorrection n r α q
  have hp : 0 < r ^ n := by positivity
  have he : r ^ n * (1 + c / r ^ n) = r ^ n + c := by field_simp
  have hu := (mul_nonneg_iff_of_pos_left hp).mp (he.symm ▸ hM)
  have hm : referenceMass n Ω r * (1 + c / r ^ n) = lovelockMass n Ω r α q 0 := by
    rw [referenceMass, mul_assoc, he]
    simp [lovelockMass, c]
  rw [← hm, lovelock_volume]
  have h := scaled_hierarchy hn (u := c / r ^ n) (w := 0) hΩ hr hu (by norm_num)
  simp only [add_zero, mul_one, one_pow, le_refl, and_true] at h
  rw [h]
  have hle := pow_le_pow_iff_left₀ (n := n + 2) (a := (1 : ℝ)) zero_le_one hu (by omega)
  rw [one_pow] at hle
  rw [hle, le_add_iff_nonneg_right, le_div_iff₀ hp, zero_mul]

namespace GaussBonnetFive

/-- In five dimensions the horizon equation is μ = r² + α for a neutral hole.
Here α is the rescaled Gauss–Bonnet coupling, not the coefficient of the
Gauss–Bonnet density in the Lagrangian. -/
theorem hierarchy_iff_coupling {Ω r α : ℝ} (hΩ : 0 < Ω) (hr : 0 < r) (hM : 0 ≤ r ^ 2 + α) :
    Hierarchy 2 Ω (Ω * r ^ 3) (lovelockMass 2 Ω r (fun _ : Fin 1 => α) 0 0)
      (flatVolume (lovelockMass 2 Ω r (fun _ : Fin 1 => α) 0)) ↔ 0 ≤ α := by
  have hc : lovelockCorrection 2 r (fun _ : Fin 1 => α) 0 = α := by
    simp [lovelockCorrection, hr.ne']
  simpa only [hc] using (lovelock_hierarchy_iff (n := 2) (by decide) hΩ hr
    (fun _ : Fin 1 => α) 0 (by rwa [hc]))

/-- Flat, asymptotically Einstein branch, α = −1 and μ = 15. The square root
is real on the whole exterior. This is Cai's Eq. (8) at zero pressure. -/
noncomputable def lapse (s : ℝ) : ℝ := 1 - (s ^ 2 - Real.sqrt (s ^ 4 - 60)) / 2

theorem lapse_published_form {s : ℝ} (hs : 4 ≤ s) :
    lapse s = 1 - s ^ 2 / 2 * (1 - Real.sqrt (1 - 60 / s ^ 4)) := by
  have hpos : 0 < s := by linarith
  have h4 : (4 : ℝ) ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ (by norm_num) hs _
  have hrad : 0 ≤ s ^ 4 - 60 := by linarith
  have hr : 1 - 60 / s ^ 4 = (s ^ 4 - 60) / (s ^ 2) ^ 2 := by field_simp
  rw [hr, Real.sqrt_div hrad, Real.sqrt_sq (sq_nonneg s)]
  unfold lapse
  field_simp

private theorem sqrt_196 : Real.sqrt 196 = 14 :=
  (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)

theorem exterior_regular : lapse 4 = 0 ∧
    (∀ s : ℝ, 4 ≤ s → 0 < s ^ 4 - 60) ∧ (∀ s : ℝ, 4 < s → 0 < lapse s) := by
  refine ⟨by norm_num [lapse, sqrt_196], ?_, ?_⟩
  · intro s hs
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hs 4
    linarith
  · intro s hs
    have h2 := (pow_lt_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 4)
      (show 0 ≤ s by linarith) (by decide : 2 ≠ 0)).mpr hs
    have hineq : s ^ 2 - 2 < Real.sqrt (s ^ 4 - 60) :=
      (Real.lt_sqrt (by linarith)).mpr (by nlinarith only [h2])
    unfold lapse
    linarith

open Filter Topology in
theorem asymptotically_flat_lapse : Tendsto lapse atTop (𝓝 1) := by
  let den : ℝ → ℝ := fun s => s ^ 2 + Real.sqrt (s ^ 4 - 60)
  have hden : Tendsto den atTop atTop :=
    tendsto_atTop_mono (fun s => le_add_of_nonneg_right (Real.sqrt_nonneg _))
      (tendsto_pow_atTop (by decide : 2 ≠ 0))
  have hlim : Tendsto (fun s => 1 - 30 / den s) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hden.const_div_atTop 30)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with s hs
  have hrad := exterior_regular.2.1 s hs
  have hpos : 0 < den s := by dsimp [den]; positivity
  have hroot := Real.sq_sqrt hrad.le
  have hrat : 30 / den s = (s ^ 2 - Real.sqrt (s ^ 4 - 60)) / 2 := by
    rw [div_eq_iff hpos.ne']
    dsimp [den]
    nlinarith only [hroot]
  rw [hrat, lapse]

/-- Surface gravity check using the derivative of the metric itself. -/
theorem horizon_derivative : HasDerivAt lapse (4 / 7) 4 := by
  have hpow := ((hasDerivAt_id (4 : ℝ)).fun_pow 4).sub_const 60
  have hsqrt := hpow.sqrt (by norm_num : (4 : ℝ) ^ 4 - 60 ≠ 0)
  have h := ((((hasDerivAt_id (4 : ℝ)).fun_pow 2).sub hsqrt).div_const 2).const_sub 1
  convert h using 1
  norm_num [sqrt_196]

/-- Wald entropy for α=−1, independent of pressure. -/
noncomputable def entropy (Ω r : ℝ) : ℝ := Ω / 4 * (r ^ 3 - 6 * r)

theorem fixed_entropy_radius {Ω s : ℝ} (hΩ : 0 < Ω) :
    entropy Ω s = entropy Ω 4 ↔ s = 4 := by
  unfold entropy
  rw [mul_right_inj' (by positivity : Ω / 4 ≠ 0)]
  constructor
  · intro h
    have hf : (s - 4) * (s ^ 2 + 4 * s + 10) = 0 := by nlinarith only [h]
    have hp : 0 < s ^ 2 + 4 * s + 10 := by nlinarith only [sq_nonneg (s + 2)]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hp.ne')
  · rintro rfl
    rfl

/-- The geometric RII is saturated while the Einstein-normalized PII (46)
is strictly violated. This uses the actual pressure derivative, Wald entropy,
and the temperature computed from the surface gravity. -/
theorem five_dimensional_counterexample {Ω : ℝ} (hΩ : 0 < Ω) :
    let A := Ω * (4 : ℝ) ^ 3
    let M := lovelockMass 2 Ω 4 (fun _ : Fin 1 => -1) 0 0
    let V := flatVolume (lovelockMass 2 Ω 4 (fun _ : Fin 1 => -1) 0)
    0 < M ∧ 0 < entropy Ω 4 ∧ 0 < deriv lapse 4 / (4 * Real.pi) ∧
      radius 4 (4 * V / Ω) = radius 3 (A / Ω) ∧
      radius 2 (16 * Real.pi * M / (3 * Ω)) < radius 3 (A / Ω) := by
  have hm : lovelockMass 2 Ω 4 (fun _ : Fin 1 => -1) 0 0 = 45 * Ω / (16 * Real.pi) := by
    norm_num [lovelockMass, lovelockCorrection, massUnit]
    ring
  have hv : flatVolume (lovelockMass 2 Ω 4 (fun _ : Fin 1 => -1) 0) = 64 * Ω := by
    rw [lovelock_volume]
    norm_num [referenceVolume]
    ring
  have hra : radius 3 (Ω * (4 : ℝ) ^ 3 / Ω) = 4 := by
    rw [show Ω * (4 : ℝ) ^ 3 / Ω = 4 ^ 3 by field_simp]
    exact Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 4) (by decide : 3 ≠ 0)
  dsimp only
  rw [hm, hv, hra, horizon_derivative.deriv]
  refine ⟨by positivity, ?_, by positivity, ?_, ?_⟩
  · norm_num [entropy]
    positivity
  · rw [show 4 * (64 * Ω) / Ω = (4 : ℝ) ^ 4 by field_simp; ring]
    exact Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 4) (by decide : 4 ≠ 0)
  · rw [show 16 * Real.pi * (45 * Ω / (16 * Real.pi)) / (3 * Ω) = 15 by
      field_simp [Real.pi_ne_zero]; norm_num]
    change (15 : ℝ) ^ (↑(2 : ℕ) : ℝ)⁻¹ < 4
    have h := Real.rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 15) (by decide : 2 ≠ 0)
    exact (pow_lt_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _)
      (by norm_num : (0 : ℝ) ≤ 4) (by decide : 2 ≠ 0)).mp (by rw [h]; norm_num)

end GaussBonnetFive

end BlackHole.StaticSpherical
