import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import ELEM.Hypotheses

/-!
# The split-prime count (companion (6)): lattice points under an ellipse

The elementary companion (twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae),
section 3, bounds the number `π₊(t)` of split primes `p ≤ t` by a count of lattice points: under
`h = 1` each split prime is a norm `a² + ab + c b²`, and gives two points `(a, b)`, `(-a-b, b)` with
`b ≥ 1` (the generators of the two primes above `p`, normalised by sign). Since
`4 (a² + ab + c b²) = (2a + b)² + q b²`, the points with norm at most `t` lie in rows
`1 ≤ b ≤ √(4t/q)`, and row `b` holds at most `√(4t - q b²) + 1` of them. The row sum is at most the
integral of the decreasing function `s ↦ √(4t - q s²)` over `[0, √(4t/q)]`, which is `π t / √q`.
Hence `2 π₊(t) ≤ π t/√q + 2 √t/√q`.

The pairing of split primes with lattice points was suggested in the Tao thread by Kyle Pratt;
the constants are the companion's.
-/

set_option autoImplicit false

namespace ELEM.Count

open Real Finset

/-! ## The area integral -/

/-- `∫₀¹ √(1 - x²) = π/4`, from Mathlib's `∫₋₁¹ √(1 - x²) = π/2` and symmetry. -/
theorem integral_sqrt_one_sub_sq_zero_one : ∫ x in (0 : ℝ)..1, √(1 - x ^ 2) = π / 4 := by
  have hc : Continuous fun x : ℝ => √(1 - x ^ 2) := by fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (a := (-1 : ℝ)) (b := 0) (c := 1) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have hneg : ∫ x in (-1 : ℝ)..0, √(1 - x ^ 2) = ∫ x in (0 : ℝ)..1, √(1 - x ^ 2) := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (fun x : ℝ => √(1 - x ^ 2))
    simp only [neg_sq, neg_zero] at this
    exact this.symm
  rw [integral_sqrt_one_sub_sq, hneg] at hsplit
  linarith

/-- The area of the half-ellipse quadrant: for `A ≥ 0`, `κ > 0`,
`∫₀^{√(A/κ)} √(A - κ s²) ds = π A / (4 √κ)`. -/
theorem integral_sqrt_sub_mul_sq {A κ : ℝ} (hA : 0 ≤ A) (hκ : 0 < κ) :
    ∫ s in (0 : ℝ)..√(A / κ), √(A - κ * s ^ 2) = π * A / (4 * √κ) := by
  rcases hA.eq_or_lt with rfl | hA'
  · simp
  set β := √(A / κ) with hβ
  have hβpos : 0 < β := Real.sqrt_pos.mpr (div_pos hA' hκ)
  have hβsq : β ^ 2 = A / κ := Real.sq_sqrt (div_pos hA' hκ).le
  have key := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun s : ℝ => √(A - κ * s ^ 2)) β
  simp only [mul_zero, mul_one, smul_eq_mul] at key
  rw [← key]
  have hpt : ∀ x : ℝ, √(A - κ * (β * x) ^ 2) = √A * √(1 - x ^ 2) := by
    intro x
    rw [← Real.sqrt_mul hA]
    congr 1
    have : κ * (β * x) ^ 2 = A * x ^ 2 := by
      rw [mul_pow, hβsq]; field_simp
    rw [this]; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq_zero_one, hβ,
    Real.sqrt_div hA]
  have hsA : √A * √A = A := Real.mul_self_sqrt hA
  have hsk : 0 < √κ := Real.sqrt_pos.mpr hκ
  calc √A / √κ * (√A * (π / 4)) = π * (√A * √A) / (4 * √κ) := by ring
    _ = π * A / (4 * √κ) := by rw [hsA]


/-! ## The norm form and the two lattice points of a split prime -/

variable {q : ℕ}

/-- `4 c = q + 1` for `c = (q + 1)/4` and `q ≡ 3 (mod 8)`. -/
theorem four_mul_cq (hq : AnalyticSetting q) : 4 * (cq q : ℤ) = q + 1 := by
  have h := hq.mod_eight
  have : 4 * ((q + 1) / 4) = q + 1 := by omega
  unfold cq
  exact_mod_cast this

/-- `4 (a² + ab + c b²) = (2a + b)² + q b²`. -/
theorem four_mul_norm (hq : AnalyticSetting q) (a b : ℤ) :
    4 * (a ^ 2 + a * b + (cq q : ℤ) * b ^ 2) = (2 * a + b) ^ 2 + q * b ^ 2 := by
  linear_combination b ^ 2 * four_mul_cq hq

/-- A split prime is a norm `a² + ab + c b²` with `b ≥ 1`. -/
theorem exists_rep_pos (hq : AnalyticSetting q) {p : ℕ} (hp : p.Prime) (hs : IsSplit q p) :
    ∃ a b : ℤ, 1 ≤ b ∧ a ^ 2 + a * b + (cq q : ℤ) * b ^ 2 = p := by
  obtain ⟨a, b, hab⟩ := hq.rep p hp hs.1
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · exact ⟨-a, -b, by omega, by rw [← hab]; ring⟩
  · exfalso
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have h1 : (p : ℤ) = a * a := by rw [← hab]; ring
    rcases hpi.irreducible.isUnit_or_isUnit h1 with hu | hu <;>
    · rcases Int.isUnit_iff.mp hu with rfl | rfl <;>
      · have : (p : ℤ) = 1 := by rw [h1]; norm_num
        exact hp.one_lt.ne' (by exact_mod_cast this)
  · exact ⟨a, b, hb, hab⟩

/-- The two points `(a, b)` and `(-a-b, b)` of a split prime are distinct: `2a + b = 0` would give
`p = q a²`, so `q ∣ p` and `p = q`. -/
theorem two_mul_add_ne_zero (hq : AnalyticSetting q) {p : ℕ} (hp : p.Prime) (hs : IsSplit q p)
    {a b : ℤ} (hab : a ^ 2 + a * b + (cq q : ℤ) * b ^ 2 = p) : 2 * a + b ≠ 0 := by
  intro h0
  have hb : b = -2 * a := by omega
  have h4 := four_mul_cq hq
  have hpq : (p : ℤ) = q * a ^ 2 := by
    subst hb; linear_combination -hab + a ^ 2 * h4
  have hdvd : q ∣ p := by
    have : (q : ℤ) ∣ p := ⟨a ^ 2, hpq⟩
    exact_mod_cast this
  exact hs.2 ((Nat.prime_dvd_prime_iff_eq hq.prime hp).mp hdvd).symm

/-! ## The lattice count -/

/-- Half-width of row `b = i + 1`: `√(4t - q b²)`. -/
noncomputable def rowW (q : ℕ) (t : ℝ) (i : ℕ) : ℝ := √(4 * t - q * ((i : ℝ) + 1) ^ 2)

/-- The real bounds of the `a`-interval in row `b = i + 1`. -/
noncomputable def rowLo (q : ℕ) (t : ℝ) (i : ℕ) : ℝ := (-((i : ℝ) + 1) - rowW q t i) / 2

noncomputable def rowHi (q : ℕ) (t : ℝ) (i : ℕ) : ℝ := (-((i : ℝ) + 1) + rowW q t i) / 2

/-- The lattice box: rows `b = i + 1 ≤ √(4t/q)`, and in row `b` the integers `a` with
`|2a + b| ≤ √(4t - q b²)`. -/
noncomputable def box (q : ℕ) (t : ℝ) : Finset (Σ _ : ℕ, ℤ) :=
  (range ⌊√(4 * t / q)⌋₊).sigma fun i => Icc ⌈rowLo q t i⌉ ⌊rowHi q t i⌋

/-- The norm form at the point `(i, a)`, i.e. at `a + (i + 1) ω`. -/
def normAt (q : ℕ) (x : Σ _ : ℕ, ℤ) : ℤ :=
  x.2 ^ 2 + x.2 * ((x.1 : ℤ) + 1) + (cq q : ℤ) * ((x.1 : ℤ) + 1) ^ 2

/-- Integers in a real interval of length `w ≥ 0`: at most `w + 1`. -/
theorem card_Icc_ceil_floor_le {lo hi : ℝ} (h : lo ≤ hi) :
    ((Icc ⌈lo⌉ ⌊hi⌋).card : ℝ) ≤ hi - lo + 1 := by
  by_cases hle : ⌈lo⌉ ≤ ⌊hi⌋ + 1
  · have hc := Int.card_Icc_of_le _ _ hle
    have h1 : ((Icc ⌈lo⌉ ⌊hi⌋).card : ℝ) = ((⌊hi⌋ + 1 - ⌈lo⌉ : ℤ) : ℝ) := by
      rw [← hc]; norm_cast
    rw [h1]; push_cast
    linarith [Int.floor_le hi, Int.le_ceil lo]
  · have : (Icc ⌈lo⌉ ⌊hi⌋).card = 0 := by
      rw [Int.card_Icc]; omega
    rw [this]; push_cast; linarith

/-- Each row holds at most `√(4t - q b²) + 1` points. -/
theorem card_box_le (q : ℕ) (t : ℝ) :
    ((box q t).card : ℝ) ≤ ∑ i ∈ range ⌊√(4 * t / q)⌋₊, (rowW q t i + 1) := by
  rw [box, card_sigma]; push_cast
  refine sum_le_sum fun i _ => ?_
  have hw : 0 ≤ rowW q t i := Real.sqrt_nonneg _
  have := card_Icc_ceil_floor_le (lo := rowLo q t i) (hi := rowHi q t i)
    (by unfold rowLo rowHi; linarith)
  unfold rowLo rowHi at this ⊢
  linarith

/-- The row sum is at most the area `π t/√q` plus the number of rows. -/
theorem sum_rowW_le (hq : AnalyticSetting q) {t : ℝ} (ht : 0 ≤ t) :
    ∑ i ∈ range ⌊√(4 * t / q)⌋₊, (rowW q t i + 1) ≤ π * t / √q + 2 * √t / √q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.prime.pos
  set β := √(4 * t / q) with hβ
  set n := ⌊β⌋₊
  have hnβ : (n : ℝ) ≤ β := Nat.floor_le (Real.sqrt_nonneg _)
  set g : ℝ → ℝ := fun s => √(4 * t - q * s ^ 2) with hg
  have hgc : Continuous g := by fun_prop
  have hanti : AntitoneOn g (Set.Icc 0 (0 + n)) := by
    intro x hx y hy hxy
    simp only [hg]
    apply Real.sqrt_le_sqrt
    have : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx.1 hxy 2
    nlinarith
  have hsum := hanti.sum_le_integral
  simp only [zero_add] at hsum
  have hrow : ∑ i ∈ range n, rowW q t i = ∑ i ∈ range n, g (↑(i + 1)) := by
    refine sum_congr rfl fun i _ => ?_
    simp [rowW, hg]
  have hint : ∫ x in (0 : ℝ)..n, g x ≤ ∫ x in (0 : ℝ)..β, g x := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (a := 0) (b := (n : ℝ)) (c := β) (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
    have hnn : 0 ≤ ∫ x in (n : ℝ)..β, g x :=
      intervalIntegral.integral_nonneg hnβ fun x _ => Real.sqrt_nonneg _
    linarith
  have harea : ∫ x in (0 : ℝ)..β, g x = π * (4 * t) / (4 * √q) :=
    integral_sqrt_sub_mul_sq (by linarith) hq0
  have hβ' : β = 2 * √t / √q := by
    rw [hβ, Real.sqrt_div (by linarith), Real.sqrt_mul (by norm_num)]
    congr 2
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [sum_add_distrib, hrow]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  have : π * (4 * t) / (4 * √q) = π * t / √q := by field_simp
  linarith

open Classical in
/-- **The split-prime count (companion (6)).** For `t ≥ 0`,
`π₊(t) = #{p ≤ t split} ≤ π t/(2√q) + √t/√q`. -/
theorem card_split_le (hq : AnalyticSetting q) {t : ℝ} (ht : 0 ≤ t) :
    (((Icc 0 ⌊t⌋₊).filter fun k => k.Prime ∧ IsSplit q k).card : ℝ) ≤
      π * t / (2 * √q) + √t / √q := by
  set P := (Icc 0 ⌊t⌋₊).filter fun k => k.Prime ∧ IsSplit q k
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.prime.pos
  -- each split prime has two points of norm `p` in the box
  have hfib : ∀ p ∈ P, 2 ≤ ((box q t).filter fun x => normAt q x = p).card := by
    intro p hpP
    obtain ⟨hpI, hp, hs⟩ := by simpa [P] using hpP
    obtain ⟨a, b, hb, hab⟩ := exists_rep_pos hq hp hs
    have hne := two_mul_add_ne_zero hq hp hs hab
    have h4 := four_mul_norm hq a b
    rw [hab] at h4
    have hpt : (p : ℝ) ≤ t := (Nat.cast_le.mpr hpI).trans (Nat.floor_le ht)
    have h4r : 4 * (p : ℝ) = (2 * (a : ℝ) + b) ^ 2 + q * (b : ℝ) ^ 2 := by exact_mod_cast h4
    set i := (b - 1).toNat with hi
    have hib : ((i : ℤ) + 1) = b := by rw [hi, Int.toNat_of_nonneg (by omega)]; ring
    have hibr : ((i : ℝ) + 1) = b := by exact_mod_cast hib
    -- the row index is in range
    have hrow : i ∈ range ⌊√(4 * t / q)⌋₊ := by
      rw [mem_range, Nat.lt_iff_add_one_le]
      apply Nat.le_floor
      push_cast
      rw [hibr]
      apply Real.le_sqrt_of_sq_le
      rw [le_div_iff₀ hq0]
      nlinarith [sq_nonneg (2 * (a : ℝ) + b)]
    -- an `a'` with `(2a' + b)² ≤ 4t - q b²` is in the row
    have hcol : ∀ a' : ℤ, (2 * (a' : ℝ) + b) ^ 2 ≤ 4 * t - q * (b : ℝ) ^ 2 →
        a' ∈ Icc ⌈rowLo q t i⌉ ⌊rowHi q t i⌋ := by
      intro a' ha'
      have habs := Real.abs_le_sqrt ha'
      rw [abs_le] at habs
      rw [mem_Icc, Int.ceil_le, Int.le_floor]
      unfold rowLo rowHi rowW
      rw [hibr]
      constructor <;> linarith
    have hm1 : (⟨i, a⟩ : Σ _ : ℕ, ℤ) ∈ (box q t).filter fun x => normAt q x = p := by
      rw [mem_filter, box, mem_sigma]
      refine ⟨⟨hrow, hcol a (by linarith)⟩, ?_⟩
      simp only [normAt, hib]; exact hab
    have hm2 : (⟨i, -a - b⟩ : Σ _ : ℕ, ℤ) ∈ (box q t).filter fun x => normAt q x = p := by
      rw [mem_filter, box, mem_sigma]
      refine ⟨⟨hrow, hcol (-a - b) (by push_cast; nlinarith)⟩, ?_⟩
      simp only [normAt, hib]; rw [← hab]; ring
    have h12 : (⟨i, a⟩ : Σ _ : ℕ, ℤ) ≠ ⟨i, -a - b⟩ := by
      intro h
      have : a = -a - b := by simpa using h
      exact hne (by omega)
    exact one_lt_card.mpr ⟨_, hm1, _, hm2, h12⟩
  -- the fibres are disjoint, so `2 #P ≤ #box`
  have hdisj : (P : Set ℕ).PairwiseDisjoint fun p => (box q t).filter fun x => normAt q x = p := by
    intro p _ p' _ hpp'
    simp only [Function.onFun]
    rw [disjoint_filter]
    intro x _ h1 h2
    exact hpp' (by rw [h1] at h2; exact_mod_cast h2)
  have hsub : (P.biUnion fun p => (box q t).filter fun x => normAt q x = p) ⊆ box q t :=
    biUnion_subset.mpr fun p _ => filter_subset _ _
  have h2P : 2 * P.card ≤ (box q t).card := by
    calc 2 * P.card = ∑ p ∈ P, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ p ∈ P, ((box q t).filter fun x => normAt q x = p).card := sum_le_sum hfib
      _ = (P.biUnion fun p => (box q t).filter fun x => normAt q x = p).card :=
          (card_biUnion hdisj).symm
      _ ≤ (box q t).card := card_le_card hsub
  have h2P' : 2 * (P.card : ℝ) ≤ (box q t).card := by exact_mod_cast h2P
  have := (card_box_le q t).trans (sum_rowW_le hq ht)
  have hsq : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  have e : π * t / (2 * √q) + √t / √q = (π * t / √q + 2 * √t / √q) / 2 := by field_simp
  rw [e]
  linarith

end ELEM.Count
