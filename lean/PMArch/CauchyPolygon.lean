import PMArch.CapacityEnvelope
import PMArch.CircleLength
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.Lattice

/-!
# Cauchy's formula for convex polygons, and the capacity bound on boundary length

`CapacityBarbier` and `CapacityEnvelope` bound the support integral `∫₀^{2π} h`. This file shows
that this integral is the Euclidean boundary length, so the capacity bound is a bound on length.

A `ConvexPolygon` lists its vertices counterclockwise, every other vertex strictly left of each
edge. Its perimeter is the sum of the Euclidean edge lengths, and its support function is the
largest vertex projection.

* `rising_disjoint`: two different edges that both rise in direction `θ` cover disjoint height
  ranges. This is where convexity enters: a line meets the boundary of a convex polygon at most
  twice.
* `rises_le`, `width_le_rises`, `abs_rises`: the rises therefore add up to exactly the width, and
  the total projected boundary `Σ|⟨e_k, u⟩|` is twice the width (`width_eq`).
* `integral_abs_trig`: a segment of length `ℓ` has `∫₀^π |⟨e, u(θ)⟩| dθ = 2ℓ`.
* `ConvexPolygon.cauchy`: **`∫₀^{2π} h = perimeter`**.
* `perimeter_le_of_causal`: a polygon whose vertices are pairwise within `Δ` has perimeter
  `≤ πΔ`.
* `capacity_is_max_length`: with `CircleLength.circle_length`, the circle of diameter `Δ` has arc
  length exactly `πΔ = capacityTerm`. The bound is attained.
* `unitSquare`, `unitSquare_causal`: the hypotheses are satisfiable.

Curves that are not polygons enter through the circle only. The general statement for a
rectifiable convex curve (its length is the supremum of inscribed polygon perimeters) is not
formalized here.
-/

open Real MeasureTheory Finset

namespace PMArch.Capacity.Polygon

/-- Two-dimensional cross product. -/
def cross (a b : ℝ × ℝ) : ℝ := a.1 * b.2 - a.2 * b.1

/-- Euclidean length. -/
noncomputable def len (a : ℝ × ℝ) : ℝ := √(a.1 ^ 2 + a.2 ^ 2)

/-- A strictly convex polygon: vertices `v 0, …, v (n-1)` in counterclockwise order, indexed
periodically, with every other vertex strictly to the left of each edge. -/
structure ConvexPolygon where
  n : ℕ
  three : 3 ≤ n
  v : ℕ → ℝ × ℝ
  periodic : ∀ k, v (k + n) = v k
  strict : ∀ k < n, ∀ i < n, i ≠ k → i ≠ (k + 1) % n →
    0 < cross (v (k + 1) - v k) (v i - v k)

namespace ConvexPolygon

variable (P : ConvexPolygon)

def edge (k : ℕ) : ℝ × ℝ := P.v (k + 1) - P.v k

/-- Euclidean perimeter: the sum of the edge lengths. -/
noncomputable def perimeter : ℝ := ∑ k ∈ range P.n, len (P.edge k)

lemma range_nonempty : (range P.n).Nonempty := nonempty_range_iff.mpr (by have := P.three; omega)

/-- Support function of the polygon: the largest vertex projection. -/
noncomputable def support (θ : ℝ) : ℝ := (range P.n).sup' P.range_nonempty fun k => proj θ (P.v k)

lemma succ_mod {n k : ℕ} (hk : k < n) : (k + 1) % n = if k + 1 = n then 0 else k + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

lemma v_succ_mod {k : ℕ} (hk : k < P.n) : P.v ((k + 1) % P.n) = P.v (k + 1) := by
  rw [succ_mod hk]
  split_ifs with h
  · rw [h, ← P.periodic 0, zero_add]
  · rfl

lemma v_n : P.v P.n = P.v 0 := by rw [← P.periodic 0, zero_add]

lemma weak {k i : ℕ} (hk : k < P.n) (hi : i < P.n) : 0 ≤ cross (P.edge k) (P.v i - P.v k) := by
  by_cases h1 : i = k
  · subst h1; simp [cross]
  by_cases h2 : i = (k + 1) % P.n
  · subst h2; rw [v_succ_mod P hk]; simp only [edge, cross]; ring_nf; rfl
  exact (P.strict k hk i hi h1 h2).le

/-- An interior point of edge `j` lies strictly left of edge `k ≠ j`. -/
lemma strict_point {k j : ℕ} (hk : k < P.n) (hj : j < P.n) (hkj : j ≠ k) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) :
    0 < cross (P.edge k) (P.v j + s • P.edge j - P.v k) := by
  have hn := P.three
  have e : cross (P.edge k) (P.v j + s • P.edge j - P.v k) =
      (1 - s) * cross (P.edge k) (P.v j - P.v k) +
        s * cross (P.edge k) (P.v ((j + 1) % P.n) - P.v k) := by
    rw [v_succ_mod P hj]; simp only [cross, edge, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [e]
  have hX := weak P hk hj
  have hY := weak P hk (Nat.mod_lt _ (by omega) : (j + 1) % P.n < P.n)
  by_cases h : j = (k + 1) % P.n
  · have hY' : 0 < cross (P.edge k) (P.v ((j + 1) % P.n) - P.v k) := by
      apply P.strict k hk _ (Nat.mod_lt _ (by omega))
      · rw [succ_mod hj, h, succ_mod hk]; split_ifs <;> omega
      · rw [succ_mod hj, h, succ_mod hk]; split_ifs <;> omega
    nlinarith [mul_pos hs0 hY', mul_nonneg (sub_pos.2 hs1).le hX]
  · have hX' : 0 < cross (P.edge k) (P.v j - P.v k) := P.strict k hk j hj hkj h
    nlinarith [mul_pos (sub_pos.2 hs1) hX', mul_nonneg hs0.le hY]

/-- Projection of the vertices onto direction `θ`. -/
noncomputable def f (θ : ℝ) (k : ℕ) : ℝ := proj θ (P.v k)

/-- **Two rising edges cover disjoint heights.** If edges `k ≠ j` both rise in direction `θ`,
no level `t` lies strictly inside both. -/
theorem rising_disjoint (θ : ℝ) {k j : ℕ} (hk : k < P.n) (hj : j < P.n) (hkj : j ≠ k) {t : ℝ}
    (h1 : P.f θ k < t) (h2 : t < P.f θ (k + 1)) (h3 : P.f θ j < t) (h4 : t < P.f θ (j + 1)) :
    False := by
  obtain ⟨c, hc⟩ : ∃ c, c = cos θ := ⟨_, rfl⟩
  obtain ⟨sn, hsn⟩ : ∃ x, x = sin θ := ⟨_, rfl⟩
  have hcs : c ^ 2 + sn ^ 2 = 1 := by rw [hc, hsn, add_comm]; exact sin_sq_add_cos_sq θ
  have hf : ∀ m, P.f θ m = (P.v m).1 * c + (P.v m).2 * sn := fun m => by
    simp only [f, proj, hc, hsn]
  obtain ⟨a, ha_def⟩ : ∃ a, a = P.f θ (k + 1) - P.f θ k := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b, b = P.f θ (j + 1) - P.f θ j := ⟨_, rfl⟩
  have ha : 0 < a := by rw [ha_def]; linarith
  have hb : 0 < b := by rw [hb_def]; linarith
  obtain ⟨s, hs_def⟩ : ∃ s, s = (t - P.f θ k) / a := ⟨_, rfl⟩
  obtain ⟨s', hs'_def⟩ : ∃ s, s = (t - P.f θ j) / b := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs_def]; exact div_pos (by linarith) ha
  have hs1 : s < 1 := by rw [hs_def]; exact (div_lt_one ha).mpr (by rw [ha_def]; linarith)
  have hs0' : 0 < s' := by rw [hs'_def]; exact div_pos (by linarith) hb
  have hs1' : s' < 1 := by rw [hs'_def]; exact (div_lt_one hb).mpr (by rw [hb_def]; linarith)
  have hsa : s * a = t - P.f θ k := by rw [hs_def]; exact div_mul_cancel₀ _ ha.ne'
  have hsb : s' * b = t - P.f θ j := by rw [hs'_def]; exact div_mul_cancel₀ _ hb.ne'
  -- p = v k + s e_k and q = v j + s' e_j both lie at level t
  have Hp := strict_point P hj hk (Ne.symm hkj) hs0 hs1
  have Hq := strict_point P hk hj hkj hs0' hs1'
  obtain ⟨e1, he1⟩ : ∃ x, x = (P.v (k + 1)).1 - (P.v k).1 := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ x, x = (P.v (k + 1)).2 - (P.v k).2 := ⟨_, rfl⟩
  obtain ⟨d1, hd1⟩ : ∃ x, x = (P.v (j + 1)).1 - (P.v j).1 := ⟨_, rfl⟩
  obtain ⟨d2, hd2⟩ : ∃ x, x = (P.v (j + 1)).2 - (P.v j).2 := ⟨_, rfl⟩
  have hpa : a = e1 * c + e2 * sn := by rw [ha_def, hf, hf, he1, he2]; ring
  have hpb : b = d1 * c + d2 * sn := by rw [hb_def, hf, hf, hd1, hd2]; ring
  obtain ⟨w1, hw1⟩ : ∃ x, x = ((P.v j).1 + s' * d1) - ((P.v k).1 + s * e1) := ⟨_, rfl⟩
  obtain ⟨w2, hw2⟩ : ∃ x, x = ((P.v j).2 + s' * d2) - ((P.v k).2 + s * e2) := ⟨_, rfl⟩
  have hfk := hf k
  have hfj := hf j
  have horth : w1 * c + w2 * sn = 0 := by
    rw [hw1, hw2]
    linear_combination -hfj - s' * hpb + hfk + s * hpa + hsb - hsa
  have idk : e1 * w2 - e2 * w1 = a * (w2 * c - w1 * sn) := by
    have : (e1 * w2 - e2 * w1) * (c ^ 2 + sn ^ 2) =
        (e1 * c + e2 * sn) * (w2 * c - w1 * sn) + (e1 * sn - e2 * c) * (w1 * c + w2 * sn) := by
      ring
    rw [hcs, mul_one, horth, mul_zero, add_zero, ← hpa] at this; exact this
  have idj : d1 * w2 - d2 * w1 = b * (w2 * c - w1 * sn) := by
    have : (d1 * w2 - d2 * w1) * (c ^ 2 + sn ^ 2) =
        (d1 * c + d2 * sn) * (w2 * c - w1 * sn) + (d1 * sn - d2 * c) * (w1 * c + w2 * sn) := by
      ring
    rw [hcs, mul_one, horth, mul_zero, add_zero, ← hpb] at this; exact this
  -- cross(e_k, q − p) = cross(e_k, q − v k) > 0 and cross(e_j, p − q) = cross(e_j, p − v j) > 0
  have ck : e1 * w2 - e2 * w1 = cross (P.edge k) (P.v j + s' • P.edge j - P.v k) := by
    simp only [cross, edge, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [hw1, hw2, he1, he2, hd1, hd2]; ring
  have cj : -(d1 * w2 - d2 * w1) = cross (P.edge j) (P.v k + s • P.edge k - P.v j) := by
    simp only [cross, edge, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [hw1, hw2, he1, he2, hd1, hd2]; ring
  rw [← ck, idk] at Hq
  rw [← cj, idj] at Hp
  have hl : 0 < w2 * c - w1 * sn := pos_of_mul_pos_right Hq ha.le
  nlinarith [mul_pos hb hl]

/-- Rise of edge `k` in direction `θ`. -/
noncomputable def rise (θ : ℝ) (k : ℕ) : ℝ := P.f θ (k + 1) - P.f θ k

lemma f_n (θ : ℝ) : P.f θ P.n = P.f θ 0 := by simp only [f, v_n]

lemma f_succ_mod (θ : ℝ) {k : ℕ} (hk : k < P.n) : P.f θ ((k + 1) % P.n) = P.f θ (k + 1) := by
  simp only [f, v_succ_mod P hk]

noncomputable def fmax (θ : ℝ) : ℝ := (range P.n).sup' P.range_nonempty (P.f θ)
noncomputable def fmin (θ : ℝ) : ℝ := (range P.n).inf' P.range_nonempty (P.f θ)

lemma le_fmax (θ : ℝ) {k : ℕ} (hk : k < P.n) : P.f θ k ≤ P.fmax θ := le_sup' _ (mem_range.2 hk)
lemma fmin_le (θ : ℝ) {k : ℕ} (hk : k < P.n) : P.fmin θ ≤ P.f θ k := inf'_le _ (mem_range.2 hk)

lemma succ_le_fmax (θ : ℝ) {k : ℕ} (hk : k < P.n) : P.f θ (k + 1) ≤ P.fmax θ := by
  rw [← f_succ_mod P θ hk]; exact le_fmax P θ (Nat.mod_lt _ (by have := P.three; omega))

lemma fmin_le_succ (θ : ℝ) {k : ℕ} (hk : k < P.n) : P.fmin θ ≤ P.f θ (k + 1) := by
  rw [← f_succ_mod P θ hk]; exact fmin_le P θ (Nat.mod_lt _ (by have := P.three; omega))

lemma zero_lt : 0 < P.n := by have := P.three; omega

/-- **The rises add up to at most the width**: rising edges cover disjoint heights. -/
theorem rises_le (θ : ℝ) : ∑ k ∈ range P.n, max (P.rise θ k) 0 ≤ P.fmax θ - P.fmin θ := by
  have hdisj : Set.PairwiseDisjoint (↑(range P.n) : Set ℕ)
      (fun k => Set.Ioo (P.f θ k) (P.f θ (k + 1))) := by
    intro k hk j hj hkj
    rw [Function.onFun, Set.disjoint_left]
    rintro t ⟨h1, h2⟩ ⟨h3, h4⟩
    exact rising_disjoint P θ (mem_range.1 hk) (mem_range.1 hj) (Ne.symm hkj) h1 h2 h3 h4
  have hsub : (⋃ k ∈ range P.n, Set.Ioo (P.f θ k) (P.f θ (k + 1))) ⊆
      Set.Icc (P.fmin θ) (P.fmax θ) := by
    intro t ht
    simp only [Set.mem_iUnion, mem_range, Set.mem_Ioo] at ht
    obtain ⟨k, hk, h1, h2⟩ := ht
    exact ⟨(fmin_le P θ hk).trans h1.le, h2.le.trans (succ_le_fmax P θ hk)⟩
  have hm := measure_mono (μ := volume) hsub
  rw [measure_biUnion_finset hdisj (fun k _ => measurableSet_Ioo), Real.volume_Icc] at hm
  simp only [Real.volume_Ioo] at hm
  have hle : P.fmin θ ≤ P.fmax θ := (fmin_le P θ P.zero_lt).trans (le_fmax P θ P.zero_lt)
  have hmax : ∀ x : ℝ, ENNReal.ofReal x = ENNReal.ofReal (max x 0) := fun x => by
    rcases le_total x 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  rw [sum_congr rfl (fun k _ => hmax _), ← ENNReal.ofReal_sum_of_nonneg
    (fun _ _ => le_max_right _ _), ENNReal.ofReal_le_ofReal_iff (sub_nonneg.2 hle)] at hm
  exact hm

lemma telescope (θ : ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Ico a b, P.rise θ k = P.f θ b - P.f θ a := by
  rw [sum_Ico_eq_sub _ hab]
  simp only [rise]
  rw [sum_range_sub, sum_range_sub]; ring

/-- **The rises add up to at least the width.** -/
theorem width_le_rises (θ : ℝ) : P.fmax θ - P.fmin θ ≤ ∑ k ∈ range P.n, max (P.rise θ k) 0 := by
  obtain ⟨j, hj, hjm⟩ := exists_mem_eq_sup' P.range_nonempty (P.f θ)
  obtain ⟨i, hi, him⟩ := exists_mem_eq_inf' P.range_nonempty (P.f θ)
  rw [fmax, fmin, hjm, him]
  have hpos : ∀ s ⊆ range P.n, ∑ k ∈ s, P.rise θ k ≤ ∑ k ∈ range P.n, max (P.rise θ k) 0 :=
    fun s hs => (sum_le_sum fun k _ => le_max_left _ _).trans
      (sum_le_sum_of_subset_of_nonneg hs fun _ _ _ => le_max_right _ _)
  rw [mem_range] at hi hj
  rcases le_total i j with h | h
  · have := hpos (Ico i j) (fun k hk => by simp only [mem_Ico, mem_range] at hk ⊢; omega)
    rwa [telescope P θ h] at this
  · have hd : Disjoint (Ico i P.n) (Ico 0 j) := by
      rw [disjoint_left]; intro k h1 h2; simp only [mem_Ico] at h1 h2; omega
    have := hpos (Ico i P.n ∪ Ico 0 j)
      (fun k hk => by simp only [mem_union, mem_Ico, mem_range] at hk ⊢; omega)
    rw [sum_union hd, telescope P θ hi.le, telescope P θ (Nat.zero_le _), f_n] at this
    linarith

lemma rises_sum_zero (θ : ℝ) : ∑ k ∈ range P.n, P.rise θ k = 0 := by
  have := telescope P θ (Nat.zero_le P.n)
  rw [Nat.Ico_zero_eq_range, f_n, sub_self] at this; exact this

/-- **Total variation of the projection is twice the width.** -/
theorem abs_rises (θ : ℝ) : ∑ k ∈ range P.n, |P.rise θ k| = 2 * (P.fmax θ - P.fmin θ) := by
  have h : ∀ x : ℝ, |x| = 2 * max x 0 - x := fun x => by
    rcases le_total x 0 with h | h
    · rw [abs_of_nonpos h, max_eq_right h]; ring
    · rw [abs_of_nonneg h, max_eq_left h]; ring
  simp_rw [h]
  rw [sum_sub_distrib, ← mul_sum, rises_sum_zero, sub_zero,
    le_antisymm (rises_le P θ) (width_le_rises P θ)]

lemma rise_eq (θ : ℝ) (k : ℕ) :
    P.rise θ k = (P.edge k).1 * cos θ + (P.edge k).2 * sin θ := by
  simp only [rise, f, proj, edge, Prod.fst_sub, Prod.snd_sub]; ring

lemma support_eq (θ : ℝ) : P.support θ = P.fmax θ := rfl

lemma support_add_pi (θ : ℝ) : P.support (θ + π) = -P.fmin θ := by
  have hf : ∀ k, proj (θ + π) (P.v k) = -P.f θ k := fun k => proj_add_pi θ _
  apply le_antisymm
  · apply sup'_le; intro k hk; rw [hf]; exact neg_le_neg (fmin_le P θ (mem_range.1 hk))
  · obtain ⟨i, hi, him⟩ := exists_mem_eq_inf' P.range_nonempty (P.f θ)
    rw [fmin, him, ← hf]; exact le_sup' (fun k => proj (θ + π) (P.v k)) hi

theorem support_continuous : Continuous P.support := by
  unfold support
  apply Continuous.finset_sup'_apply
  intro k _; unfold proj; fun_prop

/-- **The width of a convex polygon in direction `θ` is half its total projected boundary.** -/
theorem width_eq (θ : ℝ) : P.support θ + P.support (θ + π) =
    (∑ k ∈ range P.n, |(P.edge k).1 * cos θ + (P.edge k).2 * sin θ|) / 2 := by
  simp_rw [← rise_eq]
  rw [abs_rises, support_eq, support_add_pi]; ring

end ConvexPolygon

lemma integral_abs_cos_shift (φ : ℝ) : ∫ x in (0)..π, |cos (x - φ)| = 2 := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => |cos x|)]
  have hper : Function.Periodic (fun x => |cos x|) π := fun x => by simp [cos_add_pi]
  rw [show (0 : ℝ) - φ = -φ by ring, show π - φ = -φ + π by ring,
    hper.intervalIntegral_add_eq (-φ) (-(π / 2)), show -(π / 2) + π = π / 2 by ring]
  have : ∫ x in (-(π / 2))..(π / 2), |cos x| = ∫ x in (-(π / 2))..(π / 2), cos x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith [pi_pos])] at hx
    exact abs_of_nonneg (cos_nonneg_of_mem_Icc hx)
  rw [this, integral_cos, sin_neg, sin_pi_div_two]; ring

/-- `∫₀^π |a cos θ + b sin θ| dθ = 2√(a² + b²)`: a segment's projections over a half turn. -/
theorem integral_abs_trig (a b : ℝ) :
    ∫ θ in (0)..π, |a * cos θ + b * sin θ| = 2 * √(a ^ 2 + b ^ 2) := by
  set z : ℂ := ⟨a, b⟩
  have hR : ‖z‖ = √(a ^ 2 + b ^ 2) := by rw [Complex.norm_def, Complex.normSq_mk]; ring_nf
  have h1 : ‖z‖ * cos z.arg = a := Complex.norm_mul_cos_arg z
  have h2 : ‖z‖ * sin z.arg = b := Complex.norm_mul_sin_arg z
  have key : ∀ θ, |a * cos θ + b * sin θ| = ‖z‖ * |cos (θ - z.arg)| := by
    intro θ
    have : a * cos θ + b * sin θ = ‖z‖ * cos (θ - z.arg) := by
      rw [cos_sub]; linear_combination (-cos θ) * h1 + (-sin θ) * h2
    rw [this, abs_mul, abs_of_nonneg (norm_nonneg z)]
  simp_rw [key]
  rw [intervalIntegral.integral_const_mul, integral_abs_cos_shift, hR]; ring

namespace ConvexPolygon

variable (P : ConvexPolygon)

/-- **Cauchy's formula for convex polygons.** The integral of the support function over a full
turn equals the Euclidean perimeter. -/
theorem cauchy : ∫ θ in (0)..(2 * π), P.support θ = P.perimeter := by
  rw [half_turn_split _ (support_continuous P)]
  simp_rw [width_eq]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum
    (fun k _ => (by fun_prop : Continuous fun θ =>
      |(P.edge k).1 * cos θ + (P.edge k).2 * sin θ|).intervalIntegrable _ _)]
  simp_rw [integral_abs_trig]
  rw [perimeter, ← mul_sum, mul_div_cancel_left₀ _ two_ne_zero]
  rfl

/-- Causal premise for a polygon: every two vertices within distance `Δ`. -/
def Causal (Δ : ℝ) : Prop :=
  0 ≤ Δ ∧ ∀ i < P.n, ∀ j < P.n, ((P.v i).1 - (P.v j).1) ^ 2 + ((P.v i).2 - (P.v j).2) ^ 2 ≤ Δ ^ 2

theorem width_le_of_causal {Δ : ℝ} (h : P.Causal Δ) (θ : ℝ) :
    P.support θ + P.support (θ + π) ≤ Δ := by
  rw [support_eq, support_add_pi]
  obtain ⟨j, hj, hjm⟩ := exists_mem_eq_sup' P.range_nonempty (P.f θ)
  obtain ⟨i, hi, him⟩ := exists_mem_eq_inf' P.range_nonempty (P.f θ)
  rw [fmax, fmin, hjm, him]
  have hsq := proj_sq_le θ ((P.v j).1 - (P.v i).1) ((P.v j).2 - (P.v i).2)
  have hd := h.2 j (mem_range.1 hj) i (mem_range.1 hi)
  have e : P.f θ j + -P.f θ i = ((P.v j).1 - (P.v i).1) * cos θ + ((P.v j).2 - (P.v i).2) * sin θ := by
    simp only [f, proj]; ring
  rw [e]; nlinarith [h.1]

/-- **Every causal convex polygon has perimeter at most `πΔ`.** -/
theorem perimeter_le_of_causal {Δ : ℝ} (h : P.Causal Δ) : P.perimeter ≤ π * Δ := by
  rw [← cauchy]; exact perimeter_le _ (support_continuous P) Δ (width_le_of_causal P h)

end ConvexPolygon

open CircleLength in
/-- **Capacity is the largest causal boundary length.** Every strictly convex polygon whose
vertices lie within the causal distance `Δ` of each other has Euclidean perimeter at most
`πΔ = capacityTerm`, and the circle of diameter `Δ` (any two of its points within `Δ`) has arc
length exactly `πΔ`. No identification of perimeter with the support integral is assumed. -/
theorem capacity_is_max_length (p : Parameters) :
    (∀ P : ConvexPolygon, P.Causal p.period → P.perimeter ≤ capacityTerm p) ∧
      (∀ a b : ℝ, ‖arc (p.period / 2) a - arc (p.period / 2) b‖ ≤ p.period) ∧
      length (p.period / 2) = ENNReal.ofReal (capacityTerm p) := by
  have hΔ : (0 : ℝ) ≤ p.period := Nat.cast_nonneg _
  have hr : (0 : ℝ) ≤ p.period / 2 := by positivity
  refine ⟨fun P h => P.perimeter_le_of_causal h, fun a b => ?_, ?_⟩
  · rw [chord hr, abs_mul, abs_two]
    have := abs_sin_le_one ((a - b) / 2)
    nlinarith
  · rw [circle_length hr, capacityTerm]; congr 1; ring

/-- Vertices of the unit square, counterclockwise. -/
def sqv : ℕ → ℝ × ℝ := fun k =>
  if k % 4 = 0 then (0, 0) else if k % 4 = 1 then (1, 0) else if k % 4 = 2 then (1, 1) else (0, 1)

/-- The unit square is a convex polygon in this sense. -/
noncomputable def unitSquare : ConvexPolygon where
  n := 4
  three := by norm_num
  v := sqv
  periodic := fun k => by simp [sqv, Nat.add_mod_right]
  strict := by
    intro k hk i hi h1 h2
    interval_cases k <;> interval_cases i <;> simp_all [sqv, cross]

theorem unitSquare_causal : unitSquare.Causal 2 := by
  refine ⟨by norm_num, fun i hi j hj => ?_⟩
  change i < 4 at hi; change j < 4 at hj
  simp only [unitSquare]
  interval_cases i <;> interval_cases j <;> simp [sqv] <;> norm_num

end PMArch.Capacity.Polygon
