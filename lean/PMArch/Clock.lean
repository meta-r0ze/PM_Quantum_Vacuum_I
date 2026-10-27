import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import PMArch.MainResult

/-!
# The clock: integral binary forms and the period `Δ = |D|`

**Postulate (integral clock).** The clock lattice `Λ = ℤω₁ + ℤω₂ ⊂ ℂ` has integer-valued norm
form `|xω₁ + yω₂|² = a x² + b x y + c y²`. Its shape `τ = ω₂/ω₁` is then a root of
`a τ² + b τ + c = 0`, so the torus `ℂ/Λ` has complex multiplication by the order of discriminant
`D = b² - 4ac` (standard). The clock period is `Δ = |D|`.

* `clock_unique_iff`: for `32 ≤ |D| ≤ 64`, all positive-definite integral forms of
  discriminant `D` are equivalent (the clock geometry is unique) iff `D = -43`. This uses only
  Gauss reduction; no class-number classification is needed.
* `residue_ring`: for odd `D`, the canonical residue ring `O_D/(√D)` is `ℤ/|D|`, a cyclic
  clock with exactly `|D|` states.
-/

namespace PMArch.Clock

/-- Integral binary quadratic form `a x² + b x y + c y²`. -/
@[ext] structure Form where
  a : ℤ
  b : ℤ
  c : ℤ
deriving DecidableEq

namespace Form

def disc (f : Form) : ℤ := f.b ^ 2 - 4 * f.a * f.c
def eval (f : Form) (x y : ℤ) : ℤ := f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2
def PosDef (f : Form) : Prop := 0 < f.a ∧ f.disc < 0
def Reduced (f : Form) : Prop := |f.b| ≤ f.a ∧ f.a ≤ f.c ∧ ((|f.b| = f.a ∨ f.a = f.c) → 0 ≤ f.b)

instance (f : Form) : Decidable f.PosDef := by unfold PosDef; infer_instance
instance (f : Form) : Decidable f.Reduced := by unfold Reduced; infer_instance

lemma c_pos {f : Form} (h : f.PosDef) : 0 < f.c := by
  obtain ⟨ha, hd⟩ := h
  unfold disc at hd
  by_contra hc; push Not at hc
  nlinarith [sq_nonneg f.b, mul_nonneg ha.le (neg_nonneg.mpr hc)]

end Form

open Form

/-- `SL₂(ℤ)`-equivalence: `g = f ∘ γ`. -/
def Equiv (f g : Form) : Prop :=
  ∃ p q r s : ℤ, p * s - q * r = 1 ∧ ∀ x y, g.eval x y = f.eval (p * x + q * y) (r * x + s * y)

lemma Equiv.refl (f : Form) : Equiv f f := ⟨1, 0, 0, 1, by ring, fun x y => by simp⟩

lemma Equiv.symm {f g : Form} (h : Equiv f g) : Equiv g f := by
  obtain ⟨p, q, r, s, hd, he⟩ := h
  refine ⟨s, -q, -r, p, by linear_combination hd, fun x y => ?_⟩
  rw [he]
  have h1 : p * (s * x + -q * y) + q * (-r * x + p * y) = x := by linear_combination x * hd
  have h2 : r * (s * x + -q * y) + s * (-r * x + p * y) = y := by linear_combination y * hd
  rw [h1, h2]

lemma Equiv.trans {f g h : Form} (h1 : Equiv f g) (h2 : Equiv g h) : Equiv f h := by
  obtain ⟨p, q, r, s, hd, he⟩ := h1
  obtain ⟨p', q', r', s', hd', he'⟩ := h2
  refine ⟨p * p' + q * r', p * q' + q * s', r * p' + s * r', r * q' + s * s', ?_, fun x y => ?_⟩
  · linear_combination (p' * s' - q' * r') * hd + hd'
  · rw [he', he]; congr 1 <;> ring

/-- Translation `(x, y) ↦ (x + k y, y)`. -/
def translate (f : Form) (k : ℤ) : Form := ⟨f.a, f.b + 2 * f.a * k, f.a * k ^ 2 + f.b * k + f.c⟩
/-- Inversion `(x, y) ↦ (-y, x)`. -/
def swap (f : Form) : Form := ⟨f.c, -f.b, f.a⟩

lemma equiv_translate (f : Form) (k : ℤ) : Equiv f (translate f k) :=
  ⟨1, k, 0, 1, by ring, fun x y => by simp only [translate, eval]; ring⟩

lemma equiv_swap (f : Form) : Equiv f (swap f) :=
  ⟨0, -1, 1, 0, by ring, fun x y => by simp only [swap, eval]; ring⟩

lemma disc_translate (f : Form) (k : ℤ) : (translate f k).disc = f.disc := by
  simp only [translate, disc]; ring
lemma disc_swap (f : Form) : (swap f).disc = f.disc := by simp only [swap, disc]; ring

/-- **Gauss reduction.** Every positive-definite form is equivalent to a reduced form. -/
theorem exists_reduced : ∀ (n : ℕ) (f : Form), f.PosDef → f.a.toNat ≤ n →
    ∃ g, Equiv f g ∧ g.Reduced ∧ g.disc = f.disc ∧ g.PosDef := by
  intro n
  induction n with
  | zero => intro f hf hn; have := hf.1; omega
  | succ n ih =>
    intro f hf hn
    set k := (f.a - f.b) / (2 * f.a)
    set f1 := translate f k with hf1
    have ha := hf.1
    have hk1 : -f.a < f1.b := by
      simp only [hf1, translate]
      have := Int.emod_lt_of_pos (f.a - f.b) (by omega : 0 < 2 * f.a)
      have := Int.emod_add_mul_ediv (f.a - f.b) (2 * f.a)
      linarith
    have hk2 : f1.b ≤ f.a := by
      simp only [hf1, translate]
      have := Int.emod_nonneg (f.a - f.b) (by omega : 2 * f.a ≠ 0)
      have := Int.emod_add_mul_ediv (f.a - f.b) (2 * f.a)
      linarith
    have hpos1 : f1.PosDef := ⟨ha, by rw [hf1, disc_translate]; exact hf.2⟩
    have hc1 := c_pos hpos1
    have ha1 : f1.a = f.a := rfl
    by_cases hlt : f1.c < f1.a
    · have hpos2 : (swap f1).PosDef := ⟨hc1, by rw [disc_swap]; exact hpos1.2⟩
      obtain ⟨g, hg, hred, hdisc, hgpos⟩ := ih (swap f1) hpos2 (by simp only [swap]; omega)
      exact ⟨g, (equiv_translate f k).trans ((equiv_swap f1).trans hg), hred,
        by rw [hdisc, disc_swap, hf1, disc_translate], hgpos⟩
    · push Not at hlt
      by_cases hneg : f1.c = f1.a ∧ f1.b < 0
      · refine ⟨swap f1, (equiv_translate f k).trans (equiv_swap f1), ?_,
          by rw [disc_swap, hf1, disc_translate], ⟨hc1, by rw [disc_swap]; exact hpos1.2⟩⟩
        simp only [Reduced, swap]
        refine ⟨by rw [abs_neg, abs_of_neg hneg.2]; omega, by omega, fun _ => by omega⟩
      · refine ⟨f1, equiv_translate f k, ?_, by rw [hf1, disc_translate], hpos1⟩
        refine ⟨abs_le.mpr ⟨by omega, by omega⟩, hlt, fun h => ?_⟩
        rcases h with h | h
        · rcases abs_eq (by omega : 0 ≤ f1.a) |>.mp h with h' | h' <;> omega
        · by_contra hb; push Not at hb; exact hneg ⟨h.symm, hb⟩

/-- A reduced form takes no nonzero value below `a`. -/
lemma reduced_min {f : Form} (hred : f.Reduced) (hpos : f.PosDef) {x y : ℤ}
    (hxy : x ≠ 0 ∨ y ≠ 0) : f.a ≤ f.eval x y := by
  obtain ⟨hb, hac, -⟩ := hred
  have ha := hpos.1
  set X := |x| with hXd
  set Y := |y| with hYd
  set B := |f.b| with hBd
  have hX : 0 ≤ X := abs_nonneg x
  have hY : 0 ≤ Y := abs_nonneg y
  have hB : 0 ≤ B := abs_nonneg f.b
  have key : f.a * X ^ 2 - B * X * Y + f.c * Y ^ 2 ≤ f.eval x y := by
    have h1 : -(B * (X * Y)) ≤ f.b * x * y := by
      have := neg_abs_le (f.b * x * y)
      rwa [abs_mul, abs_mul, mul_assoc] at this
    have hx2 : x ^ 2 = X ^ 2 := (sq_abs x).symm
    have hy2 : y ^ 2 = Y ^ 2 := (sq_abs y).symm
    unfold eval; rw [hx2, hy2]; linarith
  rcases le_total Y X with h | h
  · rcases eq_or_ne Y 0 with hy | hy
    · have hy0 : y = 0 := abs_eq_zero.mp hy
      have hX1 : 1 ≤ X := Int.one_le_abs (hxy.resolve_right (by simp [hy0]))
      have : f.a ≤ f.a * X ^ 2 := by
        have := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ X ^ 2 by nlinarith) ha.le; linarith
      rw [hy] at key; nlinarith
    · have hY1 : 1 ≤ Y := by rcases lt_or_eq_of_le hY with h' | h' <;> omega
      have e1 : B * X * Y ≤ f.a * X * Y := by
        have := mul_le_mul_of_nonneg_right hb (mul_nonneg hX hY)
        linarith [show B * X * Y = B * (X * Y) by ring, show f.a * X * Y = f.a * (X * Y) by ring]
      have e2 : f.a * X * Y ≤ f.a * X ^ 2 := by
        have := mul_le_mul_of_nonneg_left h (mul_nonneg ha.le hX)
        linarith [show f.a * X * Y = f.a * X * Y by ring, show f.a * X ^ 2 = f.a * X * X by ring]
      have e3 : f.c ≤ f.c * Y ^ 2 := by
        have := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ Y ^ 2 by nlinarith) (c_pos hpos).le
        linarith
      linarith
  · rcases eq_or_ne X 0 with hx | hx
    · have hx0 : x = 0 := abs_eq_zero.mp hx
      have hY1 : 1 ≤ Y := Int.one_le_abs (hxy.resolve_left (by simp [hx0]))
      have : f.c ≤ f.c * Y ^ 2 := by
        have := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ Y ^ 2 by nlinarith) (c_pos hpos).le
        linarith
      rw [hx] at key; nlinarith
    · have hX1 : 1 ≤ X := by rcases lt_or_eq_of_le hX with h' | h' <;> omega
      have e1 : B * X * Y ≤ f.c * X * Y := by
        have := mul_le_mul_of_nonneg_right (hb.trans hac) (mul_nonneg hX hY)
        linarith [show B * X * Y = B * (X * Y) by ring, show f.c * X * Y = f.c * (X * Y) by ring]
      have e2 : f.c * X * Y ≤ f.c * Y ^ 2 := by
        have := mul_le_mul_of_nonneg_left h (mul_nonneg (c_pos hpos).le hY)
        linarith [show f.c * X * Y = f.c * Y * X by ring, show f.c * Y ^ 2 = f.c * Y * Y by ring]
      have e3 : f.a ≤ f.a * X ^ 2 := by
        have := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ X ^ 2 by nlinarith) ha.le; linarith
      linarith

/-- The clock geometry of discriminant `D` exists and is unique up to equivalence. -/
def UniqueClock (D : ℤ) : Prop :=
  (∃ f : Form, f.PosDef ∧ f.disc = D) ∧
    ∀ f g : Form, f.PosDef → g.PosDef → f.disc = D → g.disc = D → Equiv f g

lemma disc_mod_four (f : Form) : f.disc % 4 = 0 ∨ f.disc % 4 = 1 := by
  unfold disc
  rcases Int.even_or_odd f.b with ⟨k, hk⟩ | ⟨k, hk⟩
  · have e : f.b ^ 2 - 4 * f.a * f.c = 4 * (k ^ 2 - f.a * f.c) := by rw [hk]; ring
    rw [e]; generalize k ^ 2 - f.a * f.c = t; omega
  · have e : f.b ^ 2 - 4 * f.a * f.c = 4 * (k ^ 2 + k - f.a * f.c) + 1 := by rw [hk]; ring
    rw [e]; generalize k ^ 2 + k - f.a * f.c = t; omega

lemma no_form {D : ℤ} (hD : D % 4 = 2 ∨ D % 4 = 3) : ¬ UniqueClock D := by
  rintro ⟨⟨f, -, hf⟩, -⟩
  have := disc_mod_four f
  omega

lemma not_unique {D : ℤ} (P F : Form) (hP : P.PosDef) (hF : F.PosDef) (hPd : P.disc = D)
    (hFd : F.disc = D) (hP1 : P.eval 1 0 = 1) (hred : F.Reduced) (h2 : 2 ≤ F.a) :
    ¬ UniqueClock D := by
  rintro ⟨-, hU⟩
  obtain ⟨p, q, r, s, -, he⟩ := (hU P F hP hF hPd hFd).symm
  have h1 := he 1 0
  rw [hP1] at h1
  have hnz : p * 1 + q * 0 ≠ 0 ∨ r * 1 + s * 0 ≠ 0 := by
    by_contra h; push Not at h; rw [h.1, h.2] at h1; simp [eval] at h1
  have := reduced_min hred hF hnz
  omega

lemma reduced_43 {g : Form} (hred : g.Reduced) (hpos : g.PosDef) (hd : g.disc = -43) :
    g = ⟨1, 1, 11⟩ := by
  obtain ⟨hb, hac, hsgn⟩ := hred
  have ha := hpos.1
  unfold disc at hd
  have hb2 : g.b ^ 2 ≤ g.a ^ 2 := sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
  have ha3 : g.a ≤ 3 := by nlinarith
  have hbl := (abs_le.mp hb).1
  have hbu := (abs_le.mp hb).2
  ext <;> simp only <;>
  · interval_cases h : g.a <;> interval_cases h' : g.b <;> simp_all <;> omega

/-- **Clock selection.** In the window `32 ≤ |D| ≤ 64`, the clock geometry is unique iff
`D = -43`. -/
theorem clock_unique_iff (D : ℤ) (h1 : -64 ≤ D) (h2 : D ≤ -32) : UniqueClock D ↔ D = -43 := by
  constructor
  · intro hU
    by_contra hne
    interval_cases D
    all_goals first
    | exact absurd rfl hne
    | exact no_form (by decide) hU
    | exact (not_unique ⟨1, 0, 16⟩ ⟨4, 4, 5⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 1, 16⟩ ⟨2, 1, 8⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 0, 15⟩ ⟨3, 0, 5⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 1, 15⟩ ⟨3, 1, 5⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 0, 14⟩ ⟨2, 0, 7⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 1, 14⟩ ⟨2, 1, 7⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 0, 13⟩ ⟨2, 2, 7⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 1, 13⟩ ⟨3, 3, 5⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 0, 12⟩ ⟨3, 0, 4⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 1, 12⟩ ⟨2, 1, 6⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 0, 11⟩ ⟨3, 2, 4⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 0, 10⟩ ⟨2, 0, 5⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 1, 10⟩ ⟨2, 1, 5⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 0, 9⟩ ⟨2, 2, 5⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 1, 9⟩ ⟨3, 1, 3⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
    | exact (not_unique ⟨1, 0, 8⟩ ⟨3, 2, 3⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hU
  · rintro rfl
    have hP : Form.PosDef ⟨1, 1, 11⟩ := by decide
    refine ⟨⟨⟨1, 1, 11⟩, hP, by decide⟩, fun f g hf hg hfd hgd => ?_⟩
    obtain ⟨f', hf', hfr, hfd', hfp⟩ := exists_reduced f.a.toNat f hf le_rfl
    obtain ⟨g', hg', hgr, hgd', hgp⟩ := exists_reduced g.a.toNat g hg le_rfl
    have e1 := reduced_43 hfr hfp (hfd'.trans hfd)
    have e2 := reduced_43 hgr hgp (hgd'.trans hgd)
    rw [e1] at hf'
    rw [e2] at hg'
    exact hf'.trans hg'.symm

/-! ## The period -/

/-- Multiplication by `√D` on `ℤ[ω]`, `ω = (D + √D)/2`, in coordinates `x + y ω`
(with `2K = D² - D`). -/
def mulSqrt (D K : ℤ) (w : ℤ × ℤ) : ℤ × ℤ := (-D * w.1 - K * w.2, 2 * w.1 + D * w.2)

/-- `mulSqrt` squares to multiplication by `D`, confirming it is multiplication by `√D`. -/
lemma mulSqrt_sq (D K : ℤ) (hK : 2 * K = D ^ 2 - D) (w : ℤ × ℤ) :
    mulSqrt D K (mulSqrt D K w) = (D * w.1, D * w.2) := by
  simp only [mulSqrt, Prod.mk.injEq]
  constructor
  · linear_combination (-w.1) * hK
  · linear_combination (-w.2) * hK

/-- **Residue ring.** For odd `D`, `x + y ω ∈ √D · O_D` iff `D ∣ x`; hence `O_D/(√D) ≅ ℤ/|D|`
via `x + y ω ↦ x mod |D|`. -/
theorem residue_ring (D K : ℤ) (hD : Odd D) (hK : 2 * K = D ^ 2 - D) (v : ℤ × ℤ) :
    (∃ w, mulSqrt D K w = v) ↔ D ∣ v.1 := by
  obtain ⟨m, hm⟩ := hD
  constructor
  · rintro ⟨w, rfl⟩
    simp only [mulSqrt]
    have : K = D * m := by
      have : 2 * K = 2 * (D * m) := by rw [hK, hm]; ring
      linarith
    exact ⟨-w.1 - m * w.2, by rw [this]; ring⟩
  · rintro ⟨k, hk⟩
    refine ⟨(-D * k - m * v.2, 2 * k + v.2), ?_⟩
    have hKm : K = D * m := by
      have : 2 * K = 2 * (D * m) := by rw [hK, hm]; ring
      linarith
    simp only [mulSqrt, hKm]
    ext
    · simp only; rw [hk]; linear_combination (D * k) * hm
    · simp only; linear_combination v.2 * hm

/-- The residue clock `ℤ/|D|`, advancing by one, has period exactly `|D|`. -/
theorem clock_period (D : ℤ) (hD : D ≠ 0) : addOrderOf (1 : ZMod D.natAbs) = D.natAbs := by
  have : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD⟩
  exact ZMod.addOrderOf_one _

/-- The residue ring `O_D/(√D)` has `|D|` elements for every `D`: `mulSqrt` has determinant
`-D`. -/
lemma mulSqrt_det (D K : ℤ) (hK : 2 * K = D ^ 2 - D) : (-D) * D - (-K) * 2 = -D := by
  linear_combination hK

/-- **Period selection from an integral clock.** Serialization and scheduling place `Δ = |D|`
in `[32, 64]`; uniqueness of the clock geometry then forces `Δ = 43`. -/
theorem schedule_selects_43_of_clock {Δ : ℕ} (D : ℤ) (hΔ : (Δ : ℤ) = -D)
    (hU : UniqueClock D) (encode : Fin 32 → Fin Δ) (hinj : Function.Injective encode)
    (advance : Equiv.Perm (Fin Δ)) (active : Finset (Fin Δ))
    (hactive : active.card = 32) (hgap : NoAdjacentIdle advance active) : Δ = 43 := by
  have h1 := serialization_bound encode hinj
  have h2 := periodic_schedule_bound advance active hgap
  simp only [Fintype.card_fin, hactive] at h2
  have := (clock_unique_iff D (by omega) (by omega)).mp hU
  omega

/-- End-to-end: an integral clock with unique geometry and the scheduling hypotheses give the
certified enclosure of the geometric index. -/
theorem schedule_impedance_bounds_of_clock {Δ : ℕ} (D : ℤ) (hΔ : (Δ : ℤ) = -D)
    (hU : UniqueClock D) (encode : Fin 32 → Fin Δ) (hinj : Function.Injective encode)
    (advance : Equiv.Perm (Fin Δ)) (active : Finset (Fin Δ))
    (hactive : active.card = 32) (hgap : NoAdjacentIdle advance active) :
    (137.035999212381397211 : ℝ) < impedance { baseline with period := Δ } ∧
    impedance { baseline with period := Δ } < (137.035999212381397213 : ℝ) := by
  have h := schedule_selects_43_of_clock D hΔ hU encode hinj advance active hactive hgap
  subst h
  exact geometricIndex_bounds

end PMArch.Clock
