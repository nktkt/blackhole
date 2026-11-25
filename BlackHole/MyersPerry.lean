import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The mass–volume inequality for asymptotically flat Myers–Perry black holes

We use the asymptotically flat, uncharged family in spacetime dimension
`D = n + 3`, in units `G = 1`. The length scales compared in (48) of
[Mann, Pourhassan and Dehghani](https://arxiv.org/html/2609.14108v1#S5.E48)
are computed from their mass, horizon area and thermodynamic volume in
(49)–(50). For independent spins the corresponding inputs are the flat limits
of the mass, area and volume in [Altamirano et al.](https://arxiv.org/abs/1401.2586)
and the horizon equation in [Myers](https://arxiv.org/abs/1111.1903).
-/

set_option autoImplicit false

namespace BlackHole.MyersPerry

noncomputable def spinRatio (r a : ℝ) : ℝ := (a / r) ^ 2

/-- The mass parameter μ = 16π M / ((D−2) Ω), where Ω is the unit sphere area. -/
noncomputable def reducedMass (n : ℕ) (r a : ℝ) : ℝ := r ^ n * (1 + spinRatio r a)

/-- The horizon area divided by Ω. -/
noncomputable def reducedArea (n : ℕ) (r a : ℝ) : ℝ := r ^ (n + 1) * (1 + spinRatio r a)

/-- (D−1) V / Ω with the thermodynamic volume V of Eq. (50). -/
noncomputable def reducedVolume (n : ℕ) (r a : ℝ) : ℝ :=
  r ^ (n + 2) * (1 + spinRatio r a) * (1 + spinRatio r a / (n + 1 : ℝ))

/-- Recover the three normalized observables from the unscaled Eqs. (49)–(50).
Writing the radial factor in the mass as rⁿ/r² includes D=4. -/
theorem paper_normalization (n : ℕ) {Ω r : ℝ} (hΩ : 0 < Ω) (hr : 0 < r) (a : ℝ) :
    let M := (n + 1 : ℝ) * Ω / (16 * Real.pi) * (r ^ 2 + a ^ 2) * (r ^ n / r ^ 2)
    let A := Ω * (r ^ 2 + a ^ 2) * (r ^ (n + 1) / r ^ 2)
    let V := A * r / (n + 2 : ℝ) * (1 + a ^ 2 / ((n + 1 : ℝ) * r ^ 2))
    16 * Real.pi * M / ((n + 1 : ℝ) * Ω) = reducedMass n r a ∧
      A / Ω = reducedArea n r a ∧ (n + 2 : ℝ) * V / Ω = reducedVolume n r a := by
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
  dsimp only [reducedMass, reducedArea, reducedVolume, spinRatio]
  simp only [pow_succ r (n + 1), pow_succ r n]
  constructor
  · field_simp [hΩ.ne', hr.ne', hn1, Real.pi_ne_zero]
  constructor
  · field_simp [hΩ.ne', hr.ne']
  · field_simp [hΩ.ne', hr.ne', hn1, hn2]

noncomputable def radius (degree : ℕ) (value : ℝ) : ℝ := value ^ (degree : ℝ)⁻¹

def ThermoVolumetric (n : ℕ) (r a : ℝ) : Prop :=
  radius (n + 2) (reducedVolume n r a) ≤ radius n (reducedMass n r a)

def ReverseIsoperimetric (n : ℕ) (r a : ℝ) : Prop :=
  radius (n + 1) (reducedArea n r a) ≤ radius (n + 2) (reducedVolume n r a)

theorem radius_le_iff {j k : ℕ} (hj : j ≠ 0) (hk : k ≠ 0)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    radius j u ≤ radius k v ↔ u ^ k ≤ v ^ j := by
  have hleft : (radius j u) ^ (j * k) = u ^ k := by
    rw [pow_mul, radius, Real.rpow_inv_natCast_pow hu hj]
  have hright : (radius k v) ^ (j * k) = v ^ j := by
    rw [Nat.mul_comm, pow_mul, radius, Real.rpow_inv_natCast_pow hv hk]
  calc
    radius j u ≤ radius k v ↔ (radius j u) ^ (j * k) ≤ (radius k v) ^ (j * k) :=
      (pow_le_pow_iff_left₀ (Real.rpow_nonneg hu _) (Real.rpow_nonneg hv _)
        (Nat.mul_ne_zero hj hk)).symm
    _ ↔ _ := by rw [hleft, hright]

private theorem volume_mass_iff {n : ℕ} (hn : 0 < n) {r p v : ℝ}
    (hr : 0 < r) (hp : 0 < p) (hv : 0 < v) :
    radius (n + 2) (r ^ (n + 2) * p * v) ≤ radius n (r ^ n * p) ↔ v ^ n ≤ p ^ 2 := by
  rw [radius_le_iff (by omega) hn.ne' (by positivity) (by positivity)]
  have hpow : (r ^ (n + 2)) ^ n = (r ^ n) ^ (n + 2) := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  simp only [mul_pow, hpow]
  rw [pow_add p n 2, ← mul_assoc]
  exact mul_le_mul_iff_right₀ (by positivity)

private theorem area_volume_iff (n : ℕ) {r p v : ℝ} (hr : 0 < r) (hp : 0 < p) (hv : 0 < v) :
    radius (n + 1) (r ^ (n + 1) * p) ≤ radius (n + 2) (r ^ (n + 2) * p * v) ↔
      p ≤ v ^ (n + 1) := by
  rw [radius_le_iff (by omega) (by omega) (by positivity) (by positivity)]
  have hpow : (r ^ (n + 2)) ^ (n + 1) = (r ^ (n + 1)) ^ (n + 2) := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  simp only [mul_pow, hpow]
  rw [pow_succ p (n + 1), ← mul_assoc]
  exact mul_le_mul_iff_right₀ (by positivity)

/-- Exact criterion for the left inequality of (48), with arbitrary positive horizon radius. -/
theorem thermoVolumetric_iff {n : ℕ} (hn : 0 < n) {r a : ℝ} (hr : 0 < r) :
    ThermoVolumetric n r a ↔
      (1 + spinRatio r a / (n + 1 : ℝ)) ^ n ≤ (1 + spinRatio r a) ^ 2 := by
  have hx : 0 ≤ spinRatio r a := sq_nonneg _
  exact volume_mass_iff hn hr (by positivity) (by positivity)

/-- The right inequality of (48) holds throughout the single-spin family, by Bernoulli. -/
theorem reverseIsoperimetric (n : ℕ) {r a : ℝ} (hr : 0 < r) :
    ReverseIsoperimetric n r a := by
  let x := spinRatio r a
  have hx : 0 ≤ x := sq_nonneg _
  change radius (n + 1) (r ^ (n + 1) * (1 + x)) ≤
    radius (n + 2) (r ^ (n + 2) * (1 + x) * (1 + x / (n + 1 : ℝ)))
  rw [area_volume_iff n hr (by positivity) (by positivity)]
  have hb := one_add_mul_le_pow (show -2 ≤ x / (n + 1 : ℝ) by
    have : 0 ≤ x / (n + 1 : ℝ) := by positivity
    linarith) (n + 1)
  have he : (↑(n + 1) : ℝ) * (x / (n + 1 : ℝ)) = x := by
    push_cast
    field_simp
  rwa [he] at hb

/-- Exactly the full chain (51) for this family, in terms of the spin alone. -/
theorem hierarchy_iff {n : ℕ} (hn : 0 < n) {r a : ℝ} (hr : 0 < r) :
    (ThermoVolumetric n r a ∧ ReverseIsoperimetric n r a) ↔
      (1 + spinRatio r a / (n + 1 : ℝ)) ^ n ≤ (1 + spinRatio r a) ^ 2 :=
  (and_iff_left (reverseIsoperimetric n hr)).trans (thermoVolumetric_iff hn hr)

/-- In D=4 and D=5 every allowed single-spin solution satisfies (51). -/
theorem low_dimensional_hierarchy {n : ℕ} (hn : n = 1 ∨ n = 2) {r a : ℝ} (hr : 0 < r) :
    ThermoVolumetric n r a ∧ ReverseIsoperimetric n r a := by
  have hx : 0 ≤ spinRatio r a := sq_nonneg _
  rcases hn with rfl | rfl
  · rw [hierarchy_iff (by decide) hr]
    norm_num
    nlinarith [sq_nonneg (spinRatio r a)]
  · rw [hierarchy_iff (by decide) hr]
    norm_num
    nlinarith [sq_nonneg (spinRatio r a)]

private noncomputable def powerRatio (n : ℕ) (x : ℝ) : ℝ :=
  (1 + x / (n + 1 : ℝ)) ^ n / (1 + x) ^ 2

private theorem powerRatio_hasDerivAt {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (powerRatio n)
      ((1 + x / (n + 1 : ℝ)) ^ (n - 1) * (((n : ℝ) - 2) * x - (n + 2 : ℝ)) /
        ((n + 1 : ℝ) * (1 + x) ^ 3)) x := by
  let d : ℝ := n + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hx1 : 0 < 1 + x := by positivity
  have ha : HasDerivAt (fun t : ℝ => 1 + t / d) (1 / d) x :=
    ((hasDerivAt_id x).div_const d).const_add 1
  have hb : HasDerivAt (fun t : ℝ => 1 + t) 1 x := (hasDerivAt_id x).const_add 1
  have h := (ha.fun_pow n).div (hb.fun_pow 2) (by simpa using hx1.ne')
  have hpow : (1 + x / d) ^ n = (1 + x / d) ^ (n - 1) * (1 + x / d) := by
    simpa only [Nat.sub_add_cancel hn] using pow_succ (1 + x / d) (n - 1)
  change HasDerivAt (powerRatio n)
    ((1 + x / d) ^ (n - 1) * (((n : ℝ) - 2) * x - (n + 2 : ℝ)) / (d * (1 + x) ^ 3)) x
  convert h using 1
  dsimp only
  rw [hpow]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp [hd.ne', hx1.ne']
  dsimp [d]
  ring

/-- A finite spin with ratio greater than one, to bracket the nonzero crossing. -/
private theorem exists_large_ratio {n : ℕ} (hn : 3 ≤ n) :
    ∃ x : ℝ, 0 < x ∧ 1 < powerRatio n x := by
  let d : ℝ := n + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hdn : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd1 : 1 ≤ d := by dsimp [d]; linarith
  have hd3 : 1 ≤ d ^ 3 := one_le_pow₀ hd1
  let x := 8 * d ^ 3
  have hx : 1 < x := by dsimp [x]; linarith
  have hdiv : x / d = 8 * d ^ 2 := by dsimp [x]; field_simp
  refine ⟨x, by linarith, ?_⟩
  change 1 < (1 + x / d) ^ n / (1 + x) ^ 2
  rw [lt_div_iff₀ (by positivity), one_mul]
  calc
    (1 + x) ^ 2 < (2 * x) ^ 2 := (pow_lt_pow_iff_left₀ (by positivity) (by positivity)
      (by decide : 2 ≠ 0)).2 (by linarith)
    _ < (x / d) ^ 3 := by
      rw [hdiv]
      dsimp [x]
      nlinarith only [show 0 < d ^ 6 by positivity]
    _ ≤ (1 + x / d) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    _ ≤ (1 + x / d) ^ n := pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hn

/-- For every D≥6 the set of spins satisfying the full hierarchy is exactly
one interval. Its positive endpoint is the unique positive root of the stated
algebraic equation (the nonrotating solution is also an equality). -/
theorem higher_dimensional_threshold {n : ℕ} (hn : 3 ≤ n) :
    ∃ c : ℝ, 0 < c ∧
      (∀ x : ℝ, 0 < x →
        ((1 + x / (n + 1 : ℝ)) ^ n = (1 + x) ^ 2 ↔ x = c)) ∧
      ∀ (r a : ℝ), 0 < r →
        ((ThermoVolumetric n r a ∧ ReverseIsoperimetric n r a) ↔ spinRatio r a ≤ c) := by
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) - 2 := by linarith
  let t : ℝ := (n + 2 : ℝ) / ((n : ℝ) - 2)
  have ht : 0 < t := div_pos (by positivity) hden
  have hzero : powerRatio n 0 = 1 := by simp [powerRatio]
  have hder := fun (x : ℝ) (hx : 0 ≤ x) =>
    powerRatio_hasDerivAt (n := n) (by omega) hx
  have hcont : ContinuousOn (powerRatio n) (Set.Ici 0) := fun x hx =>
    (hder x hx).continuousAt.continuousWithinAt
  have hdec : StrictAntiOn (powerRatio n) (Set.Icc 0 t) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc ..) (hcont.mono Set.Icc_subset_Ici_self)
    intro x hx
    rw [interior_Icc] at hx
    rw [(hder x hx.1.le).deriv]
    have hsign := (lt_div_iff₀ hden).mp hx.2
    apply div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg _ _) _
    · have hx0 := hx.1
      positivity
    · linarith only [hsign]
    · have hx0 := hx.1
      positivity
  have hinc : StrictMonoOn (powerRatio n) (Set.Ici t) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici t) (hcont.mono (Set.Ici_subset_Ici.mpr ht.le))
    intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    have hx0 := ht.trans hx
    rw [(hder x hx0.le).deriv]
    have hsign := (div_lt_iff₀ hden).mp hx
    exact div_pos (mul_pos (by positivity) (by linarith only [hsign])) (by positivity)
  have hbelow (x : ℝ) (hx : 0 < x) (hxt : x ≤ t) : powerRatio n x < 1 := by
    rw [← hzero]
    exact hdec ⟨le_rfl, ht.le⟩ ⟨hx.le, hxt⟩ hx
  obtain ⟨b, hb, hhigh⟩ := exists_large_ratio hn
  have htb : t < b := by
    by_contra! h
    exact (hbelow b hb h).not_gt hhigh
  obtain ⟨c, hc, hc1⟩ := intermediate_value_Icc htb.le
    (hcont.mono (fun _ hx => ht.le.trans hx.1))
    (show (1 : ℝ) ∈ Set.Icc (powerRatio n t) (powerRatio n b) from
      ⟨(hbelow t ht le_rfl).le, hhigh.le⟩)
  have htc : t < c := lt_of_le_of_ne hc.1 (by
    rintro rfl
    exact (hbelow t ht le_rfl).ne hc1)
  refine ⟨c, ht.trans htc, ?_, ?_⟩
  · intro x hx
    have hroot : (1 + x / (n + 1 : ℝ)) ^ n = (1 + x) ^ 2 ↔ powerRatio n x = 1 := by
      unfold powerRatio
      rw [div_eq_iff (by positivity), one_mul]
    rw [hroot, ← hc1]
    constructor
    · intro he
      by_cases hxt : x ≤ t
      · exact ((hbelow x hx hxt).ne (he.trans hc1)).elim
      · exact hinc.injOn (le_of_not_ge hxt) hc.1 he
    · rintro rfl
      rfl
  · intro r a hr
    rw [hierarchy_iff (by omega) hr]
    let x := spinRatio r a
    have hx : 0 ≤ x := sq_nonneg _
    change (1 + x / (n + 1 : ℝ)) ^ n ≤ (1 + x) ^ 2 ↔ x ≤ c
    have hle : (1 + x / (n + 1 : ℝ)) ^ n ≤ (1 + x) ^ 2 ↔ powerRatio n x ≤ 1 := by
      unfold powerRatio
      rw [div_le_iff₀ (by positivity), one_mul]
    rw [hle]
    by_cases hxt : x ≤ t
    · have hval := hdec.antitoneOn ⟨le_rfl, ht.le⟩ ⟨hx, hxt⟩ hx
      rw [hzero] at hval
      exact iff_of_true hval (hxt.trans hc.1)
    · rw [← hc1]
      exact hinc.le_iff_le (le_of_not_ge hxt) hc.1

/-- Sharp threshold in six spacetime dimensions. -/
theorem six_dimensional_iff {r a : ℝ} (hr : 0 < r) :
    ThermoVolumetric 3 r a ↔ spinRatio r a ≤ 26 + 6 * Real.sqrt 21 := by
  rw [thermoVolumetric_iff (by decide) hr]
  let x := spinRatio r a
  change (1 + x / (↑(3 : ℕ) + 1 : ℝ)) ^ 3 ≤ (1 + x) ^ 2 ↔ x ≤ _
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) + 1 = 4 by norm_num]
  have hx : 0 ≤ x := sq_nonneg _
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hlarge : (13 / 3 : ℝ) < Real.sqrt 21 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  rcases eq_or_lt_of_le hx with hzero | hpos
  · rw [← hzero]
    constructor <;> intro h <;> first | positivity | norm_num
  have hfac : (1 + x) ^ 2 - (1 + x / 4) ^ 3 =
      (x / 64 * (x - (26 - 6 * Real.sqrt 21))) * (26 + 6 * Real.sqrt 21 - x) := by
    linear_combination (-9 / 16 * x) * hs
  have hpositive : 0 < x / 64 * (x - (26 - 6 * Real.sqrt 21)) :=
    mul_pos (by positivity) (by linarith)
  rw [← sub_nonneg, hfac, mul_nonneg_iff_of_pos_left hpositive, sub_nonneg]

/-- Hawking temperature from Emparan–Myers (hep-th/0308056), Eq. (14),
written in terms of r and a using the horizon equation. -/
noncomputable def temperature (n : ℕ) (r a : ℝ) : ℝ :=
  ((n : ℝ) * r ^ 2 + ((n : ℝ) - 2) * a ^ 2) / (4 * Real.pi * r * (r ^ 2 + a ^ 2))

/-- At D=6 the horizon equation is s(s²+a²)=μ. The witness has exactly one
positive horizon root, positive mass and temperature, and strictly reversed
mass–volume ordering. The reverse isoperimetric inequality itself holds. -/
theorem six_dimensional_counterexample :
    reducedMass 3 1 8 = 65 ∧ reducedVolume 3 1 8 = 1105 ∧
    (∀ s : ℝ, 0 < s → (s * (s ^ 2 + (8 : ℝ) ^ 2) = reducedMass 3 1 8 ↔ s = 1)) ∧
    0 < reducedMass 3 1 8 ∧ 0 < temperature 3 1 8 ∧
    radius 3 (reducedMass 3 1 8) < radius 5 (reducedVolume 3 1 8) ∧
    ReverseIsoperimetric 3 1 8 := by
  have hm : reducedMass 3 1 8 = 65 := by norm_num [reducedMass, spinRatio]
  have hv : reducedVolume 3 1 8 = 1105 := by norm_num [reducedVolume, spinRatio]
  refine ⟨hm, hv, ?_, by rw [hm]; norm_num, ?_, ?_, reverseIsoperimetric 3 (by norm_num)⟩
  · intro s hs
    rw [hm]
    constructor
    · intro h
      have hf : (s - 1) * (s ^ 2 + s + 65) = 0 := by nlinarith [h]
      have hp : 0 < s ^ 2 + s + 65 := by positivity
      exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hp.ne')
    · rintro rfl
      norm_num
  · norm_num [temperature]
    positivity
  · apply lt_of_not_ge
    change ¬ ThermoVolumetric 3 1 8
    rw [thermoVolumetric_iff (by decide) (by norm_num)]
    norm_num [spinRatio]

section IndependentSpins

open scoped BigOperators

/-- The full (51) for independent spins. Write xᵢ = (aᵢ/r)², padding by zeros
to D−2 slots. At an outer horizon the reduced mass, area and volume are
rⁿ P, rⁿ⁺¹ P and rⁿ⁺² P v, with P and v as below. -/
def SpinHierarchy (n : ℕ) (r : ℝ) (x : Fin (n + 1) → ℝ) : Prop :=
  let p := ∏ i, (1 + x i)
  let v := 1 + (∑ i, x i) / (n + 1 : ℝ)
  radius (n + 2) (r ^ (n + 2) * p * v) ≤ radius n (r ^ n * p) ∧
    radius (n + 1) (r ^ (n + 1) * p) ≤ radius (n + 2) (r ^ (n + 2) * p * v)

/-- Necessary and sufficient spin-only test, including the right inequality
of (51). AM–GM is applied to 1+xᵢ, with zeros in unused spin slots. -/
theorem independent_spins_iff {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (x : Fin (n + 1) → ℝ) (hx : ∀ i, 0 ≤ x i) :
    SpinHierarchy n r x ↔ (1 + (∑ i, x i) / (n + 1 : ℝ)) ^ n ≤ (∏ i, (1 + x i)) ^ 2 := by
  have hp : 0 < ∏ i, (1 + x i) := Finset.prod_pos fun i _ => by have := hx i; positivity
  have hs : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
  let p := ∏ i, (1 + x i)
  let v := 1 + (∑ i, x i) / (n + 1 : ℝ)
  change (radius (n + 2) (r ^ (n + 2) * p * v) ≤ radius n (r ^ n * p) ∧
    radius (n + 1) (r ^ (n + 1) * p) ≤ radius (n + 2) (r ^ (n + 2) * p * v)) ↔ _
  have hv : 0 < v := by dsimp [v]; positivity
  rw [volume_mass_iff hn hr hp hv, area_volume_iff n hr hp hv]
  apply and_iff_left _
  have ham := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin (n + 1)))
    (fun _ => (1 : ℝ)) (fun i => 1 + x i) (by simp) (by simp; positivity)
    (fun i _ => le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_add_of_nonneg_right (hx i)))
  simp only [Real.rpow_one, one_mul, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one] at ham
  rw [add_div, div_self (by positivity : (n + 1 : ℝ) ≠ 0)] at ham
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hp.le _) ham (n + 1)
  have hroot := Real.rpow_inv_natCast_pow hp.le (by omega : n + 1 ≠ 0)
  push_cast at hroot
  rwa [hroot] at hpow

/-- Fix the total of two squared spins and every other spin. The square of the
difference of the pair has an explicit upper bound. A negative bound makes
the allowed interval empty and a bound at least (u+v)² allows every split. -/
theorem pair_imbalance_iff {m : ℕ} {r u v : ℝ} (hr : 0 < r) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (rest : Fin m → ℝ) (hrest : ∀ i, 0 ≤ rest i) :
    SpinHierarchy (m + 1) r (Fin.cons u (Fin.cons v rest)) ↔
      (u - v) ^ 2 ≤ (2 + (u + v)) ^ 2 -
        4 * Real.sqrt ((1 + (u + v + ∑ i, rest i) / (m + 2 : ℝ)) ^ (m + 1)) /
          (∏ i, (1 + rest i)) := by
  have hnonneg : ∀ i, 0 ≤ (Fin.cons u (Fin.cons v rest) : Fin (m + 2) → ℝ) i := by
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    exact ⟨hu, hv, hrest⟩
  rw [independent_spins_iff (by omega) hr _ hnonneg]
  simp only [Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Nat.cast_add,
    Nat.cast_one, ← add_assoc, ← mul_assoc]
  have hdim : (m : ℝ) + 1 + 1 = m + 2 := by ring
  rw [hdim, add_assoc (2 : ℝ) u v]
  let p := ∏ i, (1 + rest i)
  let z := (1 + (u + v + ∑ i, rest i) / (m + 2 : ℝ)) ^ (m + 1)
  have hp : 0 < p := Finset.prod_pos fun i _ => by have := hrest i; positivity
  have hs : 0 ≤ ∑ i, rest i := Finset.sum_nonneg fun i _ => hrest i
  have hz : 0 ≤ z := by dsimp [z]; positivity
  change z ≤ ((1 + u) * (1 + v) * p) ^ 2 ↔
    (u - v) ^ 2 ≤ (2 + (u + v)) ^ 2 - 4 * Real.sqrt z / p
  have hroot : z ≤ ((1 + u) * (1 + v) * p) ^ 2 ↔
      Real.sqrt z ≤ (1 + u) * (1 + v) * p := by
    simpa only [Real.sq_sqrt hz] using
      (pow_le_pow_iff_left₀ (Real.sqrt_nonneg z) (by positivity : 0 ≤ (1 + u) * (1 + v) * p)
        (by decide : 2 ≠ 0))
  rw [hroot]
  have hdiff : (2 + (u + v)) ^ 2 - (u - v) ^ 2 = 4 * ((1 + u) * (1 + v)) := by ring
  calc
    Real.sqrt z ≤ (1 + u) * (1 + v) * p ↔ 4 * Real.sqrt z / p ≤
        (2 + (u + v)) ^ 2 - (u - v) ^ 2 := by
      rw [hdiff, div_le_iff₀ hp]
      constructor <;> intro h <;> linarith only [h]
    _ ↔ _ := by constructor <;> intro h <;> linarith only [h]

end IndependentSpins

end BlackHole.MyersPerry
