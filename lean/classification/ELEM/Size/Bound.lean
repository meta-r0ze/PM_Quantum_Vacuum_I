import ELEM.Hypotheses
import ELEM.Size.Leibniz
import ELEM.Size.Embedding

/-!
# ELEM.Size.Bound: the archimedean upper bound (11), Leibniz form (`ELEM.SizeBound`)

The companion (twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae), section
4.2, bounds every entry of row `(r, s)` of Green's derivative matrix by `T^(r+s) (R/T)^J`, with
`T = 2 √(R √q)`, and applies Hadamard's inequality. We apply instead the
row-wise Leibniz bound `|D₀| ≤ N! ∏_rows T^(r+s) (R/T)^J` (`ELEM.Size.Leibniz`), with `N! ≤ N^N`.
With `Δ = |D₀|²` this gives

  `log Δ ≤ 2 N log N + 2 (∑_{r,s} (r + s)) log T + 2 N J log (R/T)`,

and dividing by `R² S`, with `N ≤ R²`, `S ≤ R/12`, `J ≤ R/48 + 1`, `log T = log 2 + (log R)/2 +
(log q)/4`, the bound `(9/16) log R + (25/96) log q + (25/24) log 2 + 6 (log R)/R`. The `6` is the
companion's `4` plus the `2 (log R)/R` that `N!` costs over Hadamard.

The node bound `|z| ≤ T` is derived here from the norm form directly:
`|z|² = a² + a b + c b² ≤ (3/2) a² + (c + 1/2) b²` with `|a| ≤ A₀ < √(R √q) + 1` and
`|b| ≤ B₀ < √(R/√q) + 1`.
-/

set_option autoImplicit false

open QuadraticAlgebra Finset

namespace ELEM.Size

theorem cq_four_mul {q : ℕ} (h : q % 8 = 3) : 4 * cq q = q + 1 := by
  unfold cq; omega

/-- `2 ∑_{r < R, s < S} (r + s) = S R (R - 1) + R S (S - 1)`, hence `≤ R S (R + S)`. -/
theorem two_mul_sum_le (R S : ℕ) :
    2 * ∑ i : Fin R × Fin S, ((i.1 : ℕ) + (i.2 : ℕ)) ≤ R * S * (R + S) := by
  have hR := Finset.sum_range_id_mul_two R
  have hS := Finset.sum_range_id_mul_two S
  have eR : ∑ i : Fin R, (i : ℕ) = ∑ i ∈ range R, i := Fin.sum_univ_eq_sum_range (fun i => i) R
  have eS : ∑ i : Fin S, (i : ℕ) = ∑ i ∈ range S, i := Fin.sum_univ_eq_sum_range (fun i => i) S
  have hsum : ∑ i : Fin R × Fin S, ((i.1 : ℕ) + (i.2 : ℕ)) =
      S * ∑ i : Fin R, (i : ℕ) + R * ∑ i : Fin S, (i : ℕ) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Finset.mul_sum]
  rw [hsum, eR, eS]
  have h1 : R * (R - 1) ≤ R * R := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h2 : S * (S - 1) ≤ S * S := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  nlinarith

/-! ## The parameters `u = √q`, `s = √(R u)`, `t = √(R/u)`, `T = 2 s` -/

/-- `T = 2 √(R √q)` (companion, section 4). -/
noncomputable def Tof (q R : ℕ) : ℝ := 2 * Real.sqrt (R * Real.sqrt q)

/-- The real facts about the parameters that the size bound uses. -/
theorem params {q R : ℕ} (hq : 32768 ≤ q) (hq4 : q ^ 4 < R) :
    181 ≤ Real.sqrt q ∧ 100 ≤ Real.sqrt (R / Real.sqrt q) ∧
      Real.sqrt (R * Real.sqrt q) = Real.sqrt (R / Real.sqrt q) * Real.sqrt q ∧
      10000 * Real.sqrt q ≤ R := by
  have hqR : (32768 : ℝ) ≤ q := by exact_mod_cast hq
  have hq4R : (q : ℝ) ^ 4 < R := by exact_mod_cast hq4
  set u : ℝ := Real.sqrt q with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = q := Real.sq_sqrt (by positivity)
  have hu181 : 181 ≤ u := by nlinarith
  have huq : u ≤ q := by nlinarith
  have hq3 : (10000 : ℝ) ≤ (q : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hqR 3
    norm_num at this; linarith
  have hRu : 10000 * u ≤ R := by
    have : 10000 * (q : ℝ) ≤ (q : ℝ) ^ 4 := by nlinarith
    linarith
  have ht0 : 0 ≤ Real.sqrt (R / u) := Real.sqrt_nonneg _
  have ht2 : Real.sqrt (R / u) ^ 2 = R / u := Real.sq_sqrt (by positivity)
  refine ⟨hu181, ?_, ?_, hRu⟩
  · have h : (10000 : ℝ) ≤ R / u := by rw [le_div_iff₀ (by linarith)]; linarith
    nlinarith
  · have h : (Real.sqrt (R / u) * u) ^ 2 = R * u := by
      rw [mul_pow, ht2]; field_simp
    rw [← h, Real.sqrt_sq (mul_nonneg ht0 hu0)]

theorem one_le_Tof {q R : ℕ} (hq : 32768 ≤ q) (hq4 : q ^ 4 < R) : 1 ≤ Tof q R := by
  obtain ⟨hu, ht, hst, -⟩ := params hq hq4
  unfold Tof; rw [hst]; nlinarith

theorem Tof_le {q R : ℕ} (hq : 32768 ≤ q) (hq4 : q ^ 4 < R) : Tof q R ≤ R := by
  obtain ⟨hu, -, -, hRu⟩ := params hq hq4
  have hs0 : 0 ≤ Real.sqrt (R * Real.sqrt q) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (R * Real.sqrt q) ^ 2 = R * Real.sqrt q :=
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  unfold Tof
  nlinarith

theorem log_Tof {q R : ℕ} (hq : 32768 ≤ q) (hq4 : q ^ 4 < R) :
    Real.log (Tof q R) = Real.log 2 + Real.log R / 2 + Real.log q / 4 := by
  obtain ⟨hu, -, -, hRu⟩ := params hq hq4
  have hR : (0 : ℝ) < R := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs : 0 < Real.sqrt (R * Real.sqrt q) := Real.sqrt_pos.mpr (by positivity)
  unfold Tof
  rw [Real.log_mul (by norm_num) hs.ne', Real.log_sqrt (by positivity),
    Real.log_mul hR.ne' (by positivity), Real.log_sqrt hq0.le]
  ring

/-! ## The node bound `|z| ≤ T` -/

/-- The real inequality behind the node bound. -/
theorem node_sq_le {u t a b c : ℝ} (hu : 181 ≤ u) (ht : 100 ≤ t) (hc : c = (u ^ 2 + 1) / 4)
    (ha : a ^ 2 ≤ (t * u + 1) ^ 2) (hb : b ^ 2 ≤ (t + 1) ^ 2) :
    a * a + 1 * a * b - (-c) * b * b ≤ (2 * (t * u)) ^ 2 := by
  have hab : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (a - b)]
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hcb : c * b ^ 2 ≤ c * (t + 1) ^ 2 := mul_le_mul_of_nonneg_left hb hc0
  have hp : 18100 ≤ t * u := by nlinarith
  have e1 : 12 * (t * u) ≤ (t * u) ^ 2 := by nlinarith
  have e2 : 2 * u ^ 2 * t ≤ (t * u) ^ 2 := by
    have : 0 ≤ u ^ 2 * t := by positivity
    nlinarith
  have e3 : u ^ 2 ≤ (t * u) ^ 2 := by nlinarith
  have e4 : 3 * t ^ 2 ≤ (t * u) ^ 2 := by
    have h3 : 3 ≤ u ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right h3 (sq_nonneg t)
    nlinarith
  have e5 : 6 * t + 9 ≤ (t * u) ^ 2 := by nlinarith
  have hnum : 3 / 2 * (t * u + 1) ^ 2 + ((u ^ 2 + 3) / 4) * (t + 1) ^ 2 ≤ 4 * (t * u) ^ 2 := by
    nlinarith
  rw [hc] at hcb
  nlinarith

theorem sq_sub_le {x A s : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2 * A) (hA : A < s + 1) :
    (x - A) ^ 2 ≤ (s + 1) ^ 2 := by
  have h1 : (x - A) ^ 2 ≤ A ^ 2 := by nlinarith
  nlinarith

theorem norm_node_le {q R : ℕ} (hq : 32768 ≤ q) (hq8 : q % 8 = 3) (hq4 : q ^ 4 < R)
    (hc1 : 1 ≤ cq q) (n : Node q R) : ‖emb (cq q) hc1 (node q R n)‖ ≤ Tof q R := by
  obtain ⟨hu, ht, hst, -⟩ := params hq hq4
  have hcR : 4 * (cq q : ℝ) = q + 1 := by exact_mod_cast cq_four_mul hq8
  have hu2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg _)
  have hc : (cq q : ℝ) = (Real.sqrt q ^ 2 + 1) / 4 := by rw [hu2]; linarith
  have hi : ((n.1 : ℕ) : ℝ) ≤ 2 * (A0 q R : ℝ) := by
    have := n.1.isLt; exact_mod_cast (by omega : (n.1 : ℕ) ≤ 2 * A0 q R)
  have hj : ((n.2 : ℕ) : ℝ) ≤ 2 * (B0 q R : ℝ) := by
    have := n.2.isLt; exact_mod_cast (by omega : (n.2 : ℕ) ≤ 2 * B0 q R)
  have hA0 : (A0 q R : ℝ) < Real.sqrt (R * Real.sqrt q) + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have hB0 : (B0 q R : ℝ) < Real.sqrt (R / Real.sqrt q) + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  rw [hst] at hA0
  have ha := sq_sub_le (Nat.cast_nonneg _) hi hA0
  have hb := sq_sub_le (Nat.cast_nonneg _) hj hB0
  have key : ((QuadraticAlgebra.norm (node q R n) : ℤ) : ℝ) ≤ Tof q R ^ 2 := by
    rw [QuadraticAlgebra.norm_def]
    unfold Tof
    rw [hst]
    simp only [node]
    push_cast
    exact node_sq_le hu ht hc ha hb
  rw [← norm_emb_sq hc1] at key
  have hT0 : 0 ≤ Tof q R := by unfold Tof; positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hT0 two_ne_zero).mp key

/-! ## The entry bound and the determinant bound -/

/-- The bound for row `i = (r, s)`: `T^(r+s) (R/T)^J`. -/
noncomputable def rowBound (q R : ℕ) (i : Row R) : ℝ :=
  Tof q R ^ ((i.1 : ℕ) + (i.2 : ℕ)) * ((R : ℝ) / Tof q R) ^ Jof R

/-- `|(r)_k e^(r-k) e^s| ≤ T^(r+s) (R/T)^J` for `e ≤ T`, `r < R`, `k < J`. -/
theorem entry_real_le {R T e : ℝ} {r s k J Rn : ℕ} (hRn : (Rn : ℝ) = R) (hT1 : 1 ≤ T)
    (hRT : 1 ≤ R / T) (he0 : 0 ≤ e) (he : e ≤ T) (hr : r < Rn) (hk : k ≤ J) :
    ((r.descFactorial k : ℕ) : ℝ) * e ^ (r - k) * e ^ s ≤ T ^ (r + s) * (R / T) ^ J := by
  have hT0 : 0 < T := by linarith
  have hR0 : 0 ≤ R := by
    have := (le_div_iff₀ hT0).mp hRT
    linarith
  by_cases hkr : k ≤ r
  · have hd : ((r.descFactorial k : ℕ) : ℝ) ≤ R ^ k := by
      have h1 : r.descFactorial k ≤ r ^ k := Nat.descFactorial_le_pow r k
      have h2 : r ^ k ≤ Rn ^ k := Nat.pow_le_pow_left hr.le k
      rw [← hRn]; exact_mod_cast h1.trans h2
    have hRk : R ^ k = (R / T) ^ k * T ^ k := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hT0.ne')]
    have hpow : T ^ (r - k) * T ^ k = T ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hkr]
    calc ((r.descFactorial k : ℕ) : ℝ) * e ^ (r - k) * e ^ s
        ≤ R ^ k * T ^ (r - k) * T ^ s := by
          have h1 := pow_le_pow_left₀ he0 he (r - k)
          have h2 := pow_le_pow_left₀ he0 he s
          have h3 : 0 ≤ R ^ k := pow_nonneg hR0 k
          have h4 : 0 ≤ T ^ (r - k) := by positivity
          exact mul_le_mul (mul_le_mul hd h1 (by positivity) h3) h2 (by positivity)
            (mul_nonneg h3 h4)
      _ = (R / T) ^ k * (T ^ (r - k) * T ^ k) * T ^ s := by rw [hRk]; ring
      _ = (R / T) ^ k * T ^ (r + s) := by rw [hpow, pow_add]; ring
      _ ≤ (R / T) ^ J * T ^ (r + s) := by
          gcongr
      _ = T ^ (r + s) * (R / T) ^ J := by ring
  · have hd : r.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [hd]
    have : 0 ≤ T ^ (r + s) * (R / T) ^ J := by positivity
    simpa using this

theorem norm_entry_le {q R : ℕ} (hq : 32768 ≤ q) (hq8 : q % 8 = 3) (hq4 : q ^ 4 < R)
    (hc1 : 1 ≤ cq q) (f : Row R → Col q R) (i j : Row R) :
    ‖emb (cq q) hc1 (M q R i (f j))‖ ≤ rowBound q R i := by
  have hT1 := one_le_Tof hq hq4
  have hTR := Tof_le hq hq4
  have hRT : 1 ≤ (R : ℝ) / Tof q R := by rw [le_div_iff₀ (by linarith)]; linarith
  have he := norm_node_le hq hq8 hq4 hc1 (f j).1
  unfold M rowBound
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, norm_mul, norm_mul, norm_pow, norm_pow,
    norm_emb_star, Complex.norm_natCast]
  exact entry_real_le rfl hT1 hRT (norm_nonneg _) he i.1.isLt ((f j).2.isLt).le

theorem norm_minor_le {q R : ℕ} (hq : 32768 ≤ q) (hq8 : q % 8 = 3) (hq4 : q ^ 4 < R)
    (hc1 : 1 ≤ cq q) (f : Row R → Col q R) :
    ‖emb (cq q) hc1 (minor q R f)‖ ≤
      ((R * Sof R).factorial : ℝ) * ∏ i, rowBound q R i := by
  have h := norm_det_le_factorial_mul_prod
    ((emb (cq q) hc1 : OK (cq q) →+* ℂ).mapMatrix ((M q R).submatrix id f)) (rowBound q R)
    (fun i j => norm_entry_le hq hq8 hq4 hc1 f i j)
  have hcard : Fintype.card (Row R) = R * Sof R := by simp [Row]
  rw [hcard, ← RingHom.map_det] at h
  exact h

/-! ## Logarithms -/

theorem log_rowBound {q R : ℕ} (hq : 32768 ≤ q) (hq4 : q ^ 4 < R) (i : Row R) :
    Real.log (rowBound q R i) = (((i.1 : ℕ) + (i.2 : ℕ) : ℕ) : ℝ) * Real.log (Tof q R) +
      (Jof R : ℝ) * (Real.log R - Real.log (Tof q R)) := by
  have hT0 : 0 < Tof q R := by linarith [one_le_Tof hq hq4]
  have hR0 : (0 : ℝ) < R := by linarith [Tof_le hq hq4]
  unfold rowBound
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_div hR0.ne' hT0.ne']

theorem one_le_rowBound {q R : ℕ} (hq : 32768 ≤ q) (hq4 : q ^ 4 < R) (i : Row R) :
    1 ≤ rowBound q R i := by
  have hT1 := one_le_Tof hq hq4
  have hTR := Tof_le hq hq4
  have hRT : 1 ≤ (R : ℝ) / Tof q R := by rw [le_div_iff₀ (by linarith)]; linarith
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT1) (one_le_pow₀ hRT)

/-- `log Δ ≤ 2 (log N! + ∑_rows log b_row)`. -/
theorem log_Delta_le {q R : ℕ} (hq : 32768 ≤ q) (hq8 : q % 8 = 3) (hq4 : q ^ 4 < R)
    (f : Row R → Col q R) :
    Real.log (Delta q R f) ≤
      2 * (Real.log ((R * Sof R).factorial : ℝ) + ∑ i, Real.log (rowBound q R i)) := by
  have hc1 : 1 ≤ cq q := by have := cq_four_mul hq8; omega
  have hD := norm_minor_le hq hq8 hq4 hc1 f
  have hb1 := one_le_rowBound hq hq4
  have hprod1 : 1 ≤ ∏ i, rowBound q R i := by
    exact Finset.one_le_prod₀ (fun i _ => hb1 i)
  have hfac1 : (1 : ℝ) ≤ ((R * Sof R).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hP1 := one_le_mul_of_one_le_of_one_le hfac1 hprod1
  have hlogP : Real.log (((R * Sof R).factorial : ℝ) * ∏ i, rowBound q R i) =
      Real.log ((R * Sof R).factorial : ℝ) + ∑ i, Real.log (rowBound q R i) := by
    rw [Real.log_mul (by positivity) (by linarith),
      Real.log_prod (fun i _ => (by linarith [hb1 i] : rowBound q R i ≠ 0))]
  rw [← hlogP]
  have hDelta : Delta q R f = ‖emb (cq q) hc1 (minor q R f)‖ ^ 2 := by
    rw [norm_emb_sq]; rfl
  have hle : Delta q R f ≤ (((R * Sof R).factorial : ℝ) * ∏ i, rowBound q R i) ^ 2 := by
    rw [hDelta]; exact pow_le_pow_left₀ (norm_nonneg _) hD 2
  rcases (show (0 : ℝ) ≤ Delta q R f by rw [hDelta]; positivity).eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]
    have := Real.log_nonneg hP1
    linarith
  · calc Real.log (Delta q R f)
        ≤ Real.log ((((R * Sof R).factorial : ℝ) * ∏ i, rowBound q R i) ^ 2) :=
          Real.log_le_log h0 hle
      _ = 2 * Real.log (((R * Sof R).factorial : ℝ) * ∏ i, rowBound q R i) := by
          rw [Real.log_pow]; norm_num

/-! ## The final comparison (pure real arithmetic) -/

/-- Dividing the logarithmic bound by `R² S`. Variables: `R`, `S`, `J`, `lR = log R`,
`lT = log T`, `lN = log N`, `sm = ∑_{r,s} (r + s)`, `lF = log N!`, `lB = ∑ log b_row`. -/
theorem final_arith {R S J lR lT lN sm lF lB Y l2 lq : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hS12 : S * 12 ≤ R) (hJ48 : J * 48 ≤ R + 47) (hlT0 : 0 ≤ lT) (hlTR : lT ≤ lR)
    (hlN : lN ≤ 2 * lR) (hsm : 2 * sm ≤ R * S * (R + S)) (hlF : lF ≤ R * S * lN)
    (hlB : lB = sm * lT + R * S * (J * (lR - lT)))
    (hY : Y ≤ 2 * (lF + lB)) (hlT : lT = l2 + lR / 2 + lq / 4) :
    Y / (R ^ 2 * S) ≤ 9 / 16 * lR + 25 / 96 * lq + 25 / 24 * l2 + 6 * lR / R := by
  rw [div_le_iff₀ (by positivity)]
  have hRS0 : 0 ≤ R * S := by positivity
  have pa : 2 * lF ≤ 4 * (R * S * lR) := by nlinarith
  have pb : 2 * sm * lT ≤ 13 / 12 * (R ^ 2 * S * lT) := by
    have h1 := mul_le_mul_of_nonneg_right hsm hlT0
    have h2 : R * S * (R + S) ≤ 13 / 12 * (R ^ 2 * S) := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right h2 hlT0
    linarith
  have pc : 2 * (R * S * (J * (lR - lT))) ≤ R ^ 2 * S * (lR - lT) / 24 + 2 * (R * S * lR) := by
    have hd : 0 ≤ lR - lT := by linarith
    have h1 : J ≤ R / 48 + 1 := by linarith
    have h2 : 0 ≤ R * S * (lR - lT) := mul_nonneg hRS0 hd
    have h3 : 0 ≤ R * S * lT := mul_nonneg hRS0 hlT0
    have h4 := mul_le_mul_of_nonneg_left h1 h2
    nlinarith
  have hrhs : (9 / 16 * lR + 25 / 96 * lq + 25 / 24 * l2 + 6 * lR / R) * (R ^ 2 * S) =
      R ^ 2 * S * (25 / 24 * lT + lR / 24) + 6 * (R * S * lR) := by
    rw [hlT]; field_simp; ring
  rw [hrhs, hlB] at *
  nlinarith

/-! ## The theorem -/

/-- **(11), Leibniz form** (`ELEM.SizeBound`): for every `N × N` minor `D₀` of `M q R`,
`log Δ / (R² S) ≤ (9/16) log R + (25/96) log q + (25/24) log 2 + 6 (log R)/R`. -/
theorem sizeBound : ELEM.SizeBound := by
  intro q R hq _hRp _hRi hq4 _hR5 f _hf
  have hq0 := hq.large
  have hq8 := hq.mod_eight
  have hT1 := one_le_Tof hq0 hq4
  have hTR := Tof_le hq0 hq4
  have hR0 : (0 : ℝ) < R := by linarith
  have hS1 : 1 ≤ Sof R := by
    have h : (12 : ℝ) ≤ R := by
      obtain ⟨hu, -, -, hRu⟩ := params hq0 hq4
      linarith
    have : 12 ≤ R := by exact_mod_cast h
    unfold Sof; omega
  have hSpos : (0 : ℝ) < Sof R := by exact_mod_cast hS1
  have hS12 : (Sof R : ℝ) * 12 ≤ R := by exact_mod_cast Nat.div_mul_le_self R 12
  have hJ48 : (Jof R : ℝ) * 48 ≤ R + 47 := by
    have : (R + 47) / 48 * 48 ≤ R + 47 := Nat.div_mul_le_self _ _
    exact_mod_cast this
  have hNR : ((R * Sof R : ℕ) : ℝ) = R * Sof R := by push_cast; ring
  have hNpos : (0 : ℝ) < ((R * Sof R : ℕ) : ℝ) := by rw [hNR]; positivity
  have hlogfac : Real.log ((R * Sof R).factorial : ℝ) ≤
      (R : ℝ) * Sof R * Real.log ((R * Sof R : ℕ) : ℝ) := by
    have h : ((R * Sof R).factorial : ℝ) ≤ ((R * Sof R : ℕ) : ℝ) ^ (R * Sof R) := by
      exact_mod_cast Nat.factorial_le_pow _
    calc Real.log ((R * Sof R).factorial : ℝ)
        ≤ Real.log (((R * Sof R : ℕ) : ℝ) ^ (R * Sof R)) := Real.log_le_log (by positivity) h
      _ = (R : ℝ) * Sof R * Real.log ((R * Sof R : ℕ) : ℝ) := by
          rw [Real.log_pow, hNR]
  have hlN : Real.log ((R * Sof R : ℕ) : ℝ) ≤ 2 * Real.log R := by
    have h : ((R * Sof R : ℕ) : ℝ) ≤ (R : ℝ) ^ 2 := by
      rw [hNR]
      have : (Sof R : ℝ) ≤ R := by linarith
      nlinarith
    calc Real.log ((R * Sof R : ℕ) : ℝ) ≤ Real.log ((R : ℝ) ^ 2) := Real.log_le_log hNpos h
      _ = 2 * Real.log R := by rw [Real.log_pow]; norm_num
  have hsumb : ∑ i : Row R, Real.log (rowBound q R i) =
      ((∑ i : Row R, ((i.1 : ℕ) + (i.2 : ℕ)) : ℕ) : ℝ) * Real.log (Tof q R) +
        (R : ℝ) * Sof R * ((Jof R : ℝ) * (Real.log R - Real.log (Tof q R))) := by
    simp only [log_rowBound hq0 hq4, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    simp [Row, Finset.sum_add_distrib]
    ring
  have hsum2 : 2 * ((∑ i : Row R, ((i.1 : ℕ) + (i.2 : ℕ)) : ℕ) : ℝ) ≤
      (R : ℝ) * Sof R * (R + Sof R) := by
    exact_mod_cast two_mul_sum_le R (Sof R)
  exact final_arith hR0 hSpos hS12 hJ48 (Real.log_nonneg hT1)
    (Real.log_le_log (by linarith) hTR) hlN hsum2 hlogfac hsumb (log_Delta_le hq0 hq8 hq4 f)
    (log_Tof hq0 hq4)

end ELEM.Size
