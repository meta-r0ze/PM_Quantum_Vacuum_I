import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The length of a circle

The arc length of a curve is its variation `eVariationOn`: the supremum, over all partitions,
of the total length of the inscribed polygon. This file proves that the circle of radius `r`,
`t ↦ r e^{it}` on `[0, 2π]`, has length `2πr`. Nothing about `π` is assumed beyond Mathlib's
analytic definition.

* `chord`: `‖arc r a − arc r b‖ = r·|2 sin((a − b)/2)|`.
* `arc_lipschitz`: a chord is at most `r` times the parameter gap, so the length is `≤ 2πr`.
* `inscribed_sum`: the regular inscribed `n`-gon has perimeter `2nr sin(π/n)`, which exceeds
  `2πr − rπ³/(3n²)`; so the length is `≥ 2πr`.
* `circle_length`: the length is exactly `2πr`.
-/

open Real Complex

namespace PMArch.CircleLength

/-- The circle of radius `r` about the origin, parametrized by angle. -/
noncomputable def arc (r : ℝ) (t : ℝ) : ℂ := (r : ℂ) * exp (I * t)

theorem chord {r : ℝ} (hr : 0 ≤ r) (a b : ℝ) :
    ‖arc r a - arc r b‖ = r * |2 * Real.sin ((a - b) / 2)| := by
  have e : arc r a - arc r b = (r : ℂ) * exp (I * b) * (exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    simp only [arc]
    rw [mul_sub, mul_one, mul_assoc, ← Complex.exp_add]
    push_cast; ring_nf
  rw [e, norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal_sub_one, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr]
  have : ‖exp (I * (b : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I b
  rw [this, mul_one]

theorem chord_le {r : ℝ} (hr : 0 ≤ r) (a b : ℝ) : ‖arc r a - arc r b‖ ≤ r * |a - b| := by
  rw [chord hr]
  apply mul_le_mul_of_nonneg_left _ hr
  have h := Real.abs_sin_le_abs (x := (a - b) / 2)
  rw [abs_mul, abs_two]
  have : |(a - b) / 2| = |a - b| / 2 := by rw [abs_div, abs_two]
  linarith

theorem arc_lipschitz {r : ℝ} (hr : 0 ≤ r) : LipschitzWith r.toNNReal (arc r) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ hr]; exact chord_le hr a b

/-- Length of the circle: the variation of `arc r` on one turn. -/
noncomputable def length (r : ℝ) : ENNReal := eVariationOn (arc r) (Set.Icc 0 (2 * π))

theorem length_le {r : ℝ} (hr : 0 ≤ r) : length r ≤ ENNReal.ofReal (2 * π * r) := by
  have h := (arc_lipschitz hr).lipschitzOnWith (s := Set.univ) |>.comp_eVariationOn_le
    (g := id) (s := Set.Icc 0 (2 * π)) (Set.mapsTo_univ _ _)
  have hid : eVariationOn (id : ℝ → ℝ) (Set.Icc 0 (2 * π)) = ENNReal.ofReal (2 * π) := by
    have := (monotoneOn_id (s := Set.Icc (0 : ℝ) (2 * π))).eVariationOn_eq
      (a := 0) (b := 2 * π) ⟨le_rfl, by positivity⟩ ⟨by positivity, le_rfl⟩
    simpa only [Set.inter_self, id_eq, sub_zero] using this
  unfold length
  calc eVariationOn (arc r) (Set.Icc 0 (2 * π)) = eVariationOn (arc r ∘ id) (Set.Icc 0 (2 * π)) := rfl
    _ ≤ _ := h
    _ = ENNReal.ofReal (2 * π * r) := by
      have hc : ((r.toNNReal : NNReal) : ENNReal) = ENNReal.ofReal r := rfl
      rw [hid, hc, ← ENNReal.ofReal_mul hr]
      congr 1; ring

/-- Vertices of the regular inscribed `n`-gon (clamped after the last). -/
noncomputable def node (n : ℕ) (i : ℕ) : ℝ := 2 * π * (min i n : ℕ) / n

lemma node_mono (n : ℕ) : Monotone (node n) := by
  intro i j hij
  unfold node
  have : ((min i n : ℕ) : ℝ) ≤ (min j n : ℕ) := by exact_mod_cast min_le_min_right n hij
  gcongr

lemma node_mem (n : ℕ) (i : ℕ) : node n i ∈ Set.Icc 0 (2 * π) := by
  unfold node
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : ((min i n : ℕ) : ℝ) ≤ n := by exact_mod_cast min_le_right i n
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hn']
  nlinarith [pi_pos]

theorem inscribed_sum {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n, edist (arc r (node n (i + 1))) (arc r (node n i)) =
      ENNReal.ofReal (2 * n * r * Real.sin (π / n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 ≤ Real.sin (π / n) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (div_le_self pi_pos.le (by exact_mod_cast hn))
  have hterm : ∀ i ∈ Finset.range n, edist (arc r (node n (i + 1))) (arc r (node n i)) =
      ENNReal.ofReal (2 * r * Real.sin (π / n)) := by
    intro i hi
    have hi' : i + 1 ≤ n := Finset.mem_range.mp hi
    rw [edist_dist, dist_eq_norm, chord hr]
    have hd : (node n (i + 1) - node n i) / 2 = π / n := by
      unfold node
      rw [min_eq_left hi', min_eq_left (by omega)]
      push_cast; field_simp; ring
    rw [hd, abs_of_nonneg (by positivity)]
    congr 1; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

theorem length_ge {r : ℝ} (hr : 0 ≤ r) (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (2 * n * r * Real.sin (π / n)) ≤ length r := by
  rw [← inscribed_sum hr hn]
  exact eVariationOn.sum_le (node_mono n) (node_mem n)

/-- **The circle of radius `r` has length `2πr`.** -/
theorem circle_length {r : ℝ} (hr : 0 ≤ r) : length r = ENNReal.ofReal (2 * π * r) := by
  apply le_antisymm (length_le hr)
  have hfin : length r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (length_le hr)
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  -- every inscribed polygon is below the length, and they approach `2πr`
  have key : ∀ n : ℕ, 0 < n → 2 * π * r - r * π ^ 3 / (3 * n ^ 2) ≤ (length r).toReal := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := (ENNReal.ofReal_le_iff_le_toReal hfin).mp (length_ge hr n hn)
    have h2 := Real.sin_gt_sub_cube (x := π / n) (by positivity)
    have h3 : 2 * n * r * (π / n - (π / n) ^ 3 / 6) = 2 * π * r - r * π ^ 3 / (3 * n ^ 2) := by
      field_simp; ring
    have h4 : 2 * n * r * (π / n - (π / n) ^ 3 / 6) ≤ 2 * n * r * Real.sin (π / n) :=
      mul_le_mul_of_nonneg_left h2.le (by positivity)
    linarith
  by_contra hlt
  push Not at hlt
  set L := (length r).toReal
  have hr' : 0 < r := by
    rcases hr.lt_or_eq with h | h
    · exact h
    · subst h; simp at hlt; linarith [ENNReal.toReal_nonneg (a := length 0)]
  obtain ⟨n, hn⟩ := exists_nat_gt (r * π ^ 3 / (3 * (2 * π * r - L)))
  have hgap : 0 < 2 * π * r - L := by linarith
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hk := key n (by exact_mod_cast hnpos)
  have hn1 : (1 : ℝ) ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h] at hnpos
    · exact_mod_cast h
  have : r * π ^ 3 / (3 * n ^ 2) < 2 * π * r - L := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hn
    have : (2 * π * r - L) * (3 * n) ≤ (2 * π * r - L) * (3 * n ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hgap.le; nlinarith
    nlinarith
  linarith

end PMArch.CircleLength
