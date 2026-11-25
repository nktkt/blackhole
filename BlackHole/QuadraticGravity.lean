import BlackHole.StaticSpherical

/-!
# A flat Schwarzschild metric with theory-dependent thermodynamic volume

In four dimensions take the action density R−2Λ+αR², with G=1, α held fixed
and P=−Λ/(8π). The vacuum constant-scalar-curvature trace equation gives R=4Λ.
The Schwarzschild–AdS metric is unchanged. Its conserved mass and Wald entropy
both carry the factor 1+8αΛ, relative to Einstein gravity. These are the
general coupling expressions in [Lü and Pope, Eqs. (29), (31)](https://arxiv.org/html/1101.1971v3#S0.E29).
We use the Einstein-Hilbert plus Ricci-scalar-squared specialization of their
action, with the Ricci-tensor-squared coupling zero.

Following [Mann et al., Eqs. (9) and (10)](https://arxiv.org/html/2609.14108v1#S1.E9)
we differentiate the physical mass at fixed Wald entropy and compare the
resulting volume with the *geometric* area. These are essential choices.
-/

set_option autoImplicit false

namespace BlackHole.QuadraticGravity

open BlackHole.StaticSpherical (Hierarchy flatVolume)
open BlackHole.MyersPerry (radius)

theorem constant_curvature_trace (α Λ R : ℝ) :
    (1 + 2 * α * R) * R - 2 * (R - 2 * Λ + α * R ^ 2) = 0 ↔ R = 4 * Λ := by
  constructor <;> intro h <;> nlinarith only [h]

noncomputable def factor (α P : ℝ) : ℝ := 1 - 64 * Real.pi * α * P
noncomputable def metricMass (r P : ℝ) : ℝ := r / 2 + (4 * Real.pi / 3) * P * r ^ 3
noncomputable def mass (α r P : ℝ) : ℝ := factor α P * metricMass r P
noncomputable def area (r : ℝ) : ℝ := 4 * Real.pi * r ^ 2
noncomputable def entropy (α r P : ℝ) : ℝ := Real.pi * r ^ 2 * factor α P
noncomputable def temperature (r P : ℝ) : ℝ := (1 + 8 * Real.pi * P * r ^ 2) / (4 * Real.pi * r)
noncomputable def euclideanVolume (r : ℝ) : ℝ := 4 * Real.pi * r ^ 3 / 3

/-- s is the fixed entropy coordinate, S=πs²; the areal radius is s/√factor. -/
noncomputable def massAtEntropy (α s P : ℝ) : ℝ :=
  s / 2 * Real.sqrt (factor α P) + (4 * Real.pi / 3) * P * s ^ 3 / Real.sqrt (factor α P)

theorem entropy_coordinate {α r P : ℝ} (hF : 0 < factor α P) :
    entropy α r P = Real.pi * (r * Real.sqrt (factor α P)) ^ 2 ∧
    massAtEntropy α (r * Real.sqrt (factor α P)) P = mass α r P := by
  let t := Real.sqrt (factor α P)
  have ht : 0 < t := Real.sqrt_pos.mpr hF
  have ht2 : t ^ 2 = factor α P := Real.sq_sqrt hF.le
  constructor
  · change Real.pi * r ^ 2 * factor α P = Real.pi * (r * t) ^ 2
    rw [← ht2]
    ring
  · change r * t / 2 * t + (4 * Real.pi / 3) * P * (r * t) ^ 3 / t =
      factor α P * (r / 2 + (4 * Real.pi / 3) * P * r ^ 3)
    rw [← ht2]
    field_simp [ht.ne']

/-- The derivative is taken at fixed s. After differentiation the result
is expressed in the physical areal radius r of the evaluation point. -/
theorem isentropic_derivative {α r P : ℝ} (hF : 0 < factor α P) :
    HasDerivAt (massAtEntropy α (r * Real.sqrt (factor α P)))
      (euclideanVolume r * (1 - 32 * Real.pi * α * P) - 16 * Real.pi * α * r) P := by
  let t := Real.sqrt (factor α P)
  let d := -(64 * Real.pi * α)
  have ht : 0 < t := Real.sqrt_pos.mpr hF
  have ht2 : t ^ 2 = 1 - 64 * Real.pi * α * P := Real.sq_sqrt hF.le
  have hf : HasDerivAt (factor α) d P := by
    simpa [factor, d] using ((hasDerivAt_id P).const_mul (64 * Real.pi * α)).const_sub 1
  have ht' := hf.sqrt hF.ne'
  have h := (ht'.const_mul (r * t / 2)).add
    ((((hasDerivAt_id P).const_mul (4 * Real.pi / 3)).mul_const ((r * t) ^ 3)).div ht' ht.ne')
  have hexp : euclideanVolume r * (1 - 32 * Real.pi * α * P) - 16 * Real.pi * α * r =
      r * d / 4 + (4 * Real.pi / 3) * r ^ 3 * (t ^ 2 - P * d / 2) := by
    rw [ht2]
    dsimp [euclideanVolume, d]
    ring
  rw [hexp]
  convert h using 1
  change r * d / 4 + (4 * Real.pi / 3) * r ^ 3 * (t ^ 2 - P * d / 2) =
    r * t / 2 * (d / (2 * t)) +
    (((4 * Real.pi / 3 * 1) * (r * t) ^ 3) * t -
      ((4 * Real.pi / 3) * P * (r * t) ^ 3) * (d / (2 * t))) / t ^ 2
  field_simp [ht.ne']
  ring

noncomputable def volume (α r P : ℝ) : ℝ :=
  deriv (massAtEntropy α (r * Real.sqrt (factor α P))) P

theorem volume_formula {α r P : ℝ} (hF : 0 < factor α P) :
    volume α r P = euclideanVolume r * (1 - 32 * Real.pi * α * P) - 16 * Real.pi * α * r :=
  (isentropic_derivative hF).deriv

theorem flat_volume (α r : ℝ) :
    flatVolume (massAtEntropy α r) = euclideanVolume r - 16 * Real.pi * α * r := by
  have h := isentropic_derivative (α := α) (r := r) (P := 0) (by simp [factor])
  simp only [factor, mul_zero, sub_zero, Real.sqrt_one, mul_one] at h
  exact h.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 0 (Set.mem_Ici.mpr (le_refl (0 : ℝ))))

/-- Ratio cubed is V divided by the volume of a Euclidean ball of areal radius r. -/
theorem reverse_ratio_cubed {α r P : ℝ} (hr : 0 < r) (hF : 0 < factor α P) :
    volume α r P / euclideanVolume r = 1 - 12 * α / r ^ 2 - 32 * Real.pi * α * P := by
  rw [volume_formula hF]
  unfold euclideanVolume
  field_simp [Real.pi_ne_zero, hr.ne']
  ring

/-- In ingoing coordinates the only pressure-dependent metric coefficient is
−lapse. The cross term is 2 dv ds and the sphere has its usual areal metric. -/
noncomputable def lapse (r P s : ℝ) : ℝ := 1 - 2 * metricMass r P / s + 8 * Real.pi / 3 * P * s ^ 2

theorem lapse_smooth {r s P : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ ⊤ (fun z : ℝ × ℝ => lapse r z.1 z.2) (P, s) := by
  unfold lapse metricMass
  fun_prop (disch := exact hs.ne')

theorem flat_metric (r s : ℝ) : lapse r 0 s = 1 - r / s := by
  unfold lapse metricMass
  ring

/-- The two independent mixed Ricci components in Schwarzschild areal gauge
are −f''/2−f'/s and (1−f−sf')/s². Both equal Λ for the published metric.
With constant R=4Λ the derivative terms in the f(R) equations vanish. -/
theorem radial_vacuum_equations {r P s α : ℝ} (hs : 0 < s) :
    let f := lapse r P
    let Λ := -8 * Real.pi * P
    let R := 4 * Λ
    (-(deriv (deriv f) s) / 2 - deriv f s / s = Λ) ∧
      (1 - f s - s * deriv f s) / s ^ 2 = Λ ∧
      (1 + 2 * α * R) * Λ - (R - 2 * Λ + α * R ^ 2) / 2 = 0 := by
  let m := metricMass r P
  let k := 8 * Real.pi / 3 * P
  let fp := fun u : ℝ => 2 * m / u ^ 2 + 2 * k * u
  have hd (u : ℝ) (hu : 0 < u) : HasDerivAt (lapse r P) (fp u) u := by
    have hq := (hasDerivAt_const u (2 * m)).div (hasDerivAt_id u) hu.ne'
    have hh := (hq.const_sub 1).add (((hasDerivAt_id u).fun_pow 2).const_mul k)
    convert hh using 1
    dsimp [fp]
    field_simp [hu.ne']
    ring
  have hd2 : HasDerivAt fp (-4 * m / s ^ 3 + 2 * k) s := by
    have hq := (hasDerivAt_const s (2 * m)).div ((hasDerivAt_id s).fun_pow 2) (by simpa using hs.ne')
    have hh := hq.add ((hasDerivAt_id s).const_mul (2 * k))
    convert hh using 1
    dsimp only [id_eq]
    field_simp [hs.ne']
    ring
  have heq : deriv (lapse r P) =ᶠ[nhds s] fp := by
    filter_upwards [lt_mem_nhds hs] with u hu using (hd u hu).deriv
  dsimp only
  rw [heq.deriv_eq, hd2.deriv, (hd s hs).deriv]
  dsimp [fp, lapse, m, k]
  constructor
  · field_simp [hs.ne']
    ring
  constructor
  · field_simp [hs.ne']
    ring
  · ring

theorem outer_horizon {r P : ℝ} (hr : 0 < r) (hP : 0 ≤ P) :
    lapse r P r = 0 ∧ ∀ s : ℝ, r < s → 0 < lapse r P s := by
  have fac (s : ℝ) (hs : 0 < s) : lapse r P s =
      (s - r) / s * (1 + 8 * Real.pi / 3 * P * (s ^ 2 + s * r + r ^ 2)) := by
    unfold lapse metricMass
    field_simp [hs.ne']
    ring
  constructor
  · simp [fac r hr]
  · intro s hrs
    have hs := hr.trans hrs
    rw [fac s hs]
    exact mul_pos (div_pos (sub_pos.mpr hrs) hs) (by positivity)

/-- For α=1, r=4 the entire positive-pressure interval has a regular horizon,
positive mass, Wald entropy, temperature and volume, and R_rii < 1. At P=0
the volume ratio is still strictly below one. -/
theorem superentropic_branch {P : ℝ} (hP : 0 ≤ P) (hbound : P < 1 / (128 * Real.pi)) :
    lapse 4 P 4 = 0 ∧ (∀ s : ℝ, 4 < s → 0 < lapse 4 P s) ∧
    0 < mass 1 4 P ∧ 0 < entropy 1 4 P ∧ 0 < temperature 4 P ∧
    0 < volume 1 4 P ∧ volume 1 4 P < euclideanVolume 4 := by
  have hlim := (lt_div_iff₀ (by positivity : 0 < 128 * Real.pi)).mp hbound
  have hF : 0 < factor 1 P := by unfold factor; linarith only [hlim]
  obtain ⟨hh, he⟩ := outer_horizon (r := 4) (by norm_num) hP
  have hv : 0 < euclideanVolume 4 := by unfold euclideanVolume; positivity
  have hrat := reverse_ratio_cubed (α := 1) (r := 4) (by norm_num) hF
  norm_num at hrat
  have hlo : 0 < volume 1 4 P / euclideanVolume 4 := by linarith only [hrat, hlim]
  have hhi : volume 1 4 P / euclideanVolume 4 < 1 := by
    nlinarith only [hrat, mul_nonneg Real.pi_pos.le hP]
  refine ⟨hh, he, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_pos hF (by unfold metricMass; positivity)
  · unfold entropy
    positivity
  · unfold temperature
    positivity
  · simpa using (lt_div_iff₀ hv).mp hlo
  · simpa using (div_lt_iff₀ hv).mp hhi

/-- Four-dimensional quotient in Eq. (10), with the geometric horizon area. -/
noncomputable def reverseRatio (α r P : ℝ) : ℝ :=
  radius 3 (3 * volume α r P / (4 * Real.pi)) / radius 2 (area r / (4 * Real.pi))

theorem geometric_ratio_eq {α r P : ℝ} (hr : 0 < r) (hV : 0 ≤ volume α r P) :
    reverseRatio α r P ^ 3 = volume α r P / euclideanVolume r := by
  have ha : area r / (4 * Real.pi) = r ^ 2 := by unfold area; field_simp [Real.pi_ne_zero]
  have hra : radius 2 (r ^ 2) = r := Real.pow_rpow_inv_natCast hr.le (by decide : 2 ≠ 0)
  have hrv : (radius 3 (3 * volume α r P / (4 * Real.pi))) ^ 3 =
      3 * volume α r P / (4 * Real.pi) :=
    Real.rpow_inv_natCast_pow (by positivity) (by decide : 3 ≠ 0)
  rw [reverseRatio, ha, hra, div_pow, hrv, euclideanVolume]
  field_simp [Real.pi_ne_zero, hr.ne']

private theorem witness_ratio {P : ℝ} (hP : 0 ≤ P) (hbound : P < 1 / (128 * Real.pi)) :
    reverseRatio 1 4 P ^ 3 = 1 / 4 - 32 * Real.pi * P := by
  obtain ⟨_, _, _, _, _, hvol, _⟩ := superentropic_branch hP hbound
  have hlim := (lt_div_iff₀ (by positivity : 0 < 128 * Real.pi)).mp hbound
  have hF : 0 < factor 1 P := by unfold factor; linarith only [hlim]
  rw [geometric_ratio_eq (by norm_num) hvol.le, reverse_ratio_cubed (by norm_num) hF]
  norm_num

open Filter Topology in
/-- Counterexample to the theory-independent wording of Conjecture 2.
The quotient is strictly below one on an AdS interval and has a strictly
sub-unit flat limit. The metric is smooth through the horizon in ingoing
coordinates. The limiting lapse tends to one at spatial infinity. -/
theorem smooth_flat_superentropic_limit :
    (∀ P : ℝ, 0 ≤ P → P < 1 / (128 * Real.pi) → 0 < reverseRatio 1 4 P ∧ reverseRatio 1 4 P < 1) ∧
    reverseRatio 1 4 0 ^ 3 = 1 / 4 ∧
    Tendsto (fun P => reverseRatio 1 4 P ^ 3) (𝓝[>] 0) (𝓝 (1 / 4)) ∧
    (∀ s : ℝ, 0 < s → ContDiffAt ℝ ⊤ (fun z : ℝ × ℝ => lapse 4 z.1 z.2) (0, s)) ∧
    Tendsto (lapse 4 0) atTop (𝓝 1) := by
  have hcut : (0 : ℝ) < 1 / (128 * Real.pi) := by positivity
  refine ⟨?_, by simpa using witness_ratio (P := 0) le_rfl hcut, ?_, fun _ hs => lapse_smooth hs, ?_⟩
  · intro P hP hp
    have h := witness_ratio hP hp
    have hlim := (lt_div_iff₀ (by positivity : 0 < 128 * Real.pi)).mp hp
    have hpos : 0 < reverseRatio 1 4 P := by
      by_contra! hn
      have hneg : reverseRatio 1 4 P ^ 3 ≤ 0 := by
        rw [pow_succ]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hn
      linarith only [hneg, h, hlim]
    refine ⟨hpos, (pow_lt_pow_iff_left₀ hpos.le zero_le_one (by decide : 3 ≠ 0)).mp ?_⟩
    rw [h, one_pow]
    nlinarith only [mul_nonneg Real.pi_pos.le hP]
  · have hlin : Continuous (fun P : ℝ => 1 / 4 - 32 * Real.pi * P) := by fun_prop
    have ht : Tendsto (fun P : ℝ => 1 / 4 - 32 * Real.pi * P) (𝓝[>] 0) (𝓝 (1 / 4)) := by
      simpa using (hlin.continuousWithinAt (s := Set.Ioi 0) (x := 0)).tendsto
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hcut)] with P hP hp
    exact (witness_ratio (Set.mem_Ioi.mp hP).le (Set.mem_Iio.mp hp)).symm
  · change Tendsto (fun s => lapse 4 0 s) atTop (𝓝 1)
    simpa only [flat_metric, sub_zero, id_eq] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id.const_div_atTop (4 : ℝ))

theorem flat_hierarchy_iff {α r : ℝ} (hr : 0 < r) (hV : 12 * α ≤ r ^ 2) :
    Hierarchy 1 (4 * Real.pi) (area r) (mass α r 0) (flatVolume (massAtEntropy α r)) ↔ α = 0 := by
  have hm : 16 * Real.pi * mass α r 0 / ((↑(1 : ℕ) + 1) * (4 * Real.pi)) = r := by
    simp [mass, factor, metricMass]
    field_simp [Real.pi_ne_zero]
    ring
  have ha : area r / (4 * Real.pi) = r ^ 2 := by unfold area; field_simp [Real.pi_ne_zero]
  have hv : (↑(1 : ℕ) + 2) * flatVolume (massAtEntropy α r) / (4 * Real.pi) =
      r ^ 3 - 12 * α * r := by
    rw [flat_volume]
    unfold euclideanVolume
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  have hra : radius 2 (r ^ 2) = r := Real.pow_rpow_inv_natCast hr.le (by decide : 2 ≠ 0)
  have hrm : radius 1 r = r := by simp [radius]
  have hv0 : 0 ≤ r ^ 3 - 12 * α * r := by nlinarith only [mul_nonneg (sub_nonneg.mpr hV) hr.le]
  dsimp only [Hierarchy]
  rw [hm, ha, hv, hrm, hra]
  change (radius 3 (r ^ 3 - 12 * α * r) ≤ r ∧ r ≤ radius 3 (r ^ 3 - 12 * α * r)) ↔ α = 0
  constructor
  · rintro ⟨h₁,h₂⟩
    have hroot := congrArg (fun t : ℝ => t ^ 3) (le_antisymm h₁ h₂)
    change (radius 3 (r ^ 3 - 12 * α * r)) ^ 3 = r ^ 3 at hroot
    rw [radius, Real.rpow_inv_natCast_pow hv0 (by decide)] at hroot
    exact (mul_eq_zero.mp (show α * r = 0 by linarith only [hroot])).resolve_right hr.ne'
  · rintro rfl
    rw [mul_zero, zero_mul, sub_zero]
    have hroot : radius 3 (r ^ 3) = r := Real.pow_rpow_inv_natCast hr.le (by decide : 3 ≠ 0)
    simp [hroot]

/-- In areal ingoing coordinates the lapse determines the whole flat metric.
All the usual uncharged, nonrotating thermodynamic data are recorded as well. -/
structure FlatData where
  radialLapse : ℝ → ℝ
  admMass : ℝ
  horizonArea : ℝ
  waldEntropy : ℝ
  hawkingTemperature : ℝ

noncomputable def flatData (α r : ℝ) : FlatData :=
  ⟨lapse r 0, mass α r 0, area r, entropy α r 0, temperature r 0⟩

theorem same_flat_data (α β r : ℝ) : flatData α r = flatData β r := by
  simp [flatData, mass, factor, entropy]

/-- Two actions with identical flat Schwarzschild data, including the entire
metric, and explicitly different positive thermodynamic volumes. -/
theorem same_geometry_opposite_order :
    flatData 0 4 = flatData 1 4 ∧
    flatVolume (massAtEntropy 0 4) = 256 * Real.pi / 3 ∧
    flatVolume (massAtEntropy 1 4) = 64 * Real.pi / 3 ∧
    Hierarchy 1 (4 * Real.pi) (area 4) (mass 0 4 0) (flatVolume (massAtEntropy 0 4)) ∧
    ¬ Hierarchy 1 (4 * Real.pi) (area 4) (mass 1 4 0) (flatVolume (massAtEntropy 1 4)) := by
  refine ⟨same_flat_data .., ?_, ?_, (flat_hierarchy_iff (by norm_num) (by norm_num)).mpr rfl, ?_⟩
  · rw [flat_volume, euclideanVolume]
    ring
  · rw [flat_volume, euclideanVolume]
    ring
  · rw [flat_hierarchy_iff (by norm_num) (by norm_num)]
    norm_num

/-- Any candidate classifier that only sees the flat spacetime and the listed
flat charges takes the same input at (α,r)=(0,4) and (1,4), but the hierarchy
has opposite truth values. Both actions have nonnegative fixed α. -/
theorem no_flat_geometry_classifier :
    ¬ ∃ rule : FlatData → Prop, ∀ (α r : ℝ), 0 ≤ α → 0 < r → 12 * α < r ^ 2 →
      (rule (flatData α r) ↔
        Hierarchy 1 (4 * Real.pi) (area r) (mass α r 0) (flatVolume (massAtEntropy α r))) := by
  rintro ⟨rule, h⟩
  have h₀ := (h 0 4 (by norm_num) (by norm_num) (by norm_num)).trans
    (flat_hierarchy_iff (by norm_num) (by norm_num))
  have h₁ := (h 1 4 (by norm_num) (by norm_num) (by norm_num)).trans
    (flat_hierarchy_iff (by norm_num) (by norm_num))
  have hg := h₀.mpr rfl
  rw [same_flat_data 0 1 4] at hg
  exact (by norm_num : (1 : ℝ) ≠ 0) (h₁.mp hg)

end BlackHole.QuadraticGravity
