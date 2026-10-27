import PMArch.ThetaE8
import Mathlib.Combinatorics.Pigeonhole

/-!
# Uniqueness of E8

A positive-definite even unimodular integral Gram matrix of size 8 is integrally equivalent to
the explicit E8 Gram matrix `PMArch.Lattices.gram`.

Proof outline:
1. `θ = E₄` gives 240 roots and 2160 vectors of norm 4.
2. Roots occupy 120 classes of `L/2L`; norm-4 vectors lie in the at most 135 remaining nonzero
   classes, so some class contains 16 of them. Norm-4 vectors in one class are orthogonal or
   opposite, giving an orthogonal frame `v₁,…,v₈` of norm-4 vectors congruent modulo `2L`.
3. The vectors `(vᵢ ± vⱼ)/2` span `D8`; self-duality and evenness supply a glue vector, and an
   explicit change of basis identifies the lattice with E8.
-/

noncomputable section
open Matrix
open scoped ArithmeticFunction.sigma

namespace PMArch.E8Unique
open PMArch.RankEight PMArch.ThetaE8 UpperHalfPlane ModularForm EisensteinSeries

lemma E₄_qExpansion_coeff_two : (qExpansion 1 E₄).coeff 2 = 2160 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel,
    show σ 3 2 = 9 by decide]

/-- A rank-eight even unimodular lattice has exactly 2160 vectors of norm 4. -/
theorem card_norm_four (A : Matrix (Fin 8) (Fin 8) ℤ)
    (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef)
    (heven : ∀ z : Fin 8 → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) (hdet : IsUnit A.det) :
    Nat.card {z : Fin 8 → ℤ // z ⬝ᵥ (A *ᵥ z) = 4} = 2160 := by
  have h2 := thetaMF_coeff A hpos heven hdet 2
  rw [thetaMF_eq_E₄, E₄_qExpansion_coeff_two] at h2
  have hcard : Nat.card (halfNorm A ⁻¹' {2}) = 2160 := by exact_mod_cast h2.symm
  rw [← hcard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
  rw [norm_eq_two_halfNorm A hpos heven z]
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  omega

/-- Hypotheses: positive-definite, even, unimodular. -/
structure Hyp (A : Matrix (Fin 8) (Fin 8) ℤ) : Prop where
  pos : (A.map (Int.cast : ℤ → ℝ)).PosDef
  even : ∀ z : Fin 8 → ℤ, Even (z ⬝ᵥ (A *ᵥ z))
  det : IsUnit A.det

/-- The bilinear form. -/
def B (A : Matrix (Fin 8) (Fin 8) ℤ) (x y : Fin 8 → ℤ) : ℤ := x ⬝ᵥ (A *ᵥ y)

variable {A : Matrix (Fin 8) (Fin 8) ℤ}

lemma Hyp.symm (h : Hyp A) (i j : Fin 8) : A j i = A i j := by
  have := h.pos.1.apply i j
  simp only [Matrix.map_apply, star_trivial] at this
  exact_mod_cast this

lemma B_comm (h : Hyp A) (x y : Fin 8 → ℤ) : B A x y = B A y x := by
  simp only [B, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [h.symm i j]; ring

lemma B_add_left (x y z : Fin 8 → ℤ) : B A (x + y) z = B A x z + B A y z := by
  simp [B, add_dotProduct]
lemma B_add_right (x y z : Fin 8 → ℤ) : B A x (y + z) = B A x y + B A x z := by
  simp [B, mulVec_add, dotProduct_add]
lemma B_smul_left (c : ℤ) (x y : Fin 8 → ℤ) : B A (c • x) y = c * B A x y := by
  simp only [B]; rw [smul_dotProduct, smul_eq_mul]
lemma B_smul_right (c : ℤ) (x y : Fin 8 → ℤ) : B A x (c • y) = c * B A x y := by
  simp only [B]; rw [mulVec_smul, dotProduct_smul, smul_eq_mul]
lemma B_neg_left (x y : Fin 8 → ℤ) : B A (-x) y = -B A x y := by
  simp [B, neg_dotProduct]
lemma B_neg_right (x y : Fin 8 → ℤ) : B A x (-y) = -B A x y := by
  simp [B, mulVec_neg, dotProduct_neg]

lemma Q_add (h : Hyp A) (x y : Fin 8 → ℤ) :
    B A (x + y) (x + y) = B A x x + 2 * B A x y + B A y y := by
  rw [B_add_left, B_add_right, B_add_right, B_comm h y x]; ring

lemma Q_add_two (h : Hyp A) (w u : Fin 8 → ℤ) :
    B A (w + (2 : ℤ) • u) (w + (2 : ℤ) • u) = B A w w + 4 * B A w u + 4 * B A u u := by
  rw [Q_add h, B_smul_right, B_smul_left, B_smul_right]; ring

lemma Q_nonneg (h : Hyp A) (z : Fin 8 → ℤ) : 0 ≤ B A z z := by
  have := qf_nonneg h.pos (vcast z)
  rw [qf_cast] at this
  exact_mod_cast this

lemma Q_eq_zero (h : Hyp A) {z : Fin 8 → ℤ} (hz : B A z z = 0) : z = 0 := by
  by_contra hne
  have hv : vcast z ≠ 0 := by
    intro h0; apply hne; ext i
    have := congrFun h0 i
    simpa [vcast] using this
  have := qf_pos h.pos hv
  rw [qf_cast] at this
  have : (0 : ℤ) < B A z z := by exact_mod_cast this
  omega

lemma Q_even (h : Hyp A) (z : Fin 8 → ℤ) : Even (B A z z) := h.even z

/-- Residue class modulo `2L`. -/
def cls (z : Fin 8 → ℤ) : Fin 8 → ZMod 2 := fun i => (z i : ZMod 2)

lemma exists_of_cls_eq {z w : Fin 8 → ℤ} (hc : cls z = cls w) :
    ∃ u : Fin 8 → ℤ, z = w + (2 : ℤ) • u := by
  refine ⟨fun i => (z i - w i) / 2, ?_⟩
  ext i
  have h1 := congrFun hc i
  simp only [cls] at h1
  have h2 : (2 : ℤ) ∣ z i - w i := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (w i) (z i) 2).mp h1.symm
    simpa using this
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  omega

lemma cls_neg (z : Fin 8 → ℤ) : cls (-z) = cls z := by
  ext i; simp [cls, ZMod.neg_eq_self_mod_two]

lemma root_cls (h : Hyp A) {r s : Fin 8 → ℤ} (hr : B A r r = 2) (hs : B A s s = 2)
    (hc : cls r = cls s) : r = s ∨ r = -s := by
  obtain ⟨u, rfl⟩ := exists_of_cls_eq hc
  have e := Q_add_two h s u
  have hsu := Q_add h s u
  have hn := Q_nonneg h (s + u)
  have hu0 := Q_nonneg h u
  obtain ⟨k, hk⟩ := Q_even h u
  rcases (show B A u u = 0 ∨ B A u u = 2 by omega) with h0 | h2
  · left; rw [Q_eq_zero h h0]; simp
  · right
    have : s + u = 0 := Q_eq_zero h (by omega)
    have hu : u = -s := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact this
    rw [hu]; ext i; simp; ring

lemma root_norm4_cls (h : Hyp A) {r v : Fin 8 → ℤ} (hr : B A r r = 2) (hv : B A v v = 4)
    (hc : cls r = cls v) : False := by
  obtain ⟨u, rfl⟩ := exists_of_cls_eq hc
  have e := Q_add_two h v u
  omega

lemma root_cls_ne_zero (_h : Hyp A) {r : Fin 8 → ℤ} (hr : B A r r = 2) : cls r ≠ 0 := by
  intro hc
  obtain ⟨u, hu⟩ := exists_of_cls_eq (w := 0) (by rw [hc]; ext; simp [cls])
  rw [hu, zero_add, B_smul_left, B_smul_right] at hr
  omega

lemma norm4_cls_ne_zero (h : Hyp A) {v : Fin 8 → ℤ} (hv : B A v v = 4) : cls v ≠ 0 := by
  intro hc
  obtain ⟨u, hu⟩ := exists_of_cls_eq (w := 0) (by rw [hc]; ext; simp [cls])
  rw [hu, zero_add, B_smul_left, B_smul_right] at hv
  obtain ⟨k, hk⟩ := Q_even h u
  omega

lemma norm4_cls (h : Hyp A) {v w : Fin 8 → ℤ} (hv : B A v v = 4) (hw : B A w w = 4)
    (hc : cls v = cls w) : v = w ∨ v = -w ∨ B A v w = 0 := by
  obtain ⟨u, rfl⟩ := exists_of_cls_eq hc
  have e := Q_add_two h w u
  have hwu := Q_add h w u
  have hn := Q_nonneg h (w + u)
  have hu0 := Q_nonneg h u
  obtain ⟨k, hk⟩ := Q_even h u
  rcases (show B A u u = 0 ∨ B A u u = 2 ∨ B A u u = 4 by omega) with h0 | h2 | h4
  · left; rw [Q_eq_zero h h0]; simp
  · right; right
    rw [B_add_left, B_smul_left, B_comm h u w]
    omega
  · right; left
    have : w + u = 0 := Q_eq_zero h (by omega)
    have hu : u = -w := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact this
    rw [hu]; ext i; simp; ring

lemma Q_neg (z : Fin 8 → ℤ) : B A (-z) (-z) = B A z z := by
  rw [B_neg_left, B_neg_right, neg_neg]

lemma finite_of_card {P : (Fin 8 → ℤ) → Prop} {n : ℕ} (hn : Nat.card {z // P z} = n)
    (h0 : n ≠ 0) : ({z | P z} : Set (Fin 8 → ℤ)).Finite := by
  have : Finite {z // P z} := Nat.finite_of_card_ne_zero (by rw [hn]; exact h0)
  exact Set.finite_coe_iff.mp this

/-- An orthogonal frame of eight norm-4 vectors, all congruent modulo `2L`. -/
theorem exists_frame (h : Hyp A) : ∃ col : Fin 8 → Fin 8 → ℤ,
    (∀ i j, B A (col i) (col j) = if i = j then 4 else 0) ∧
    ∀ i j, cls (col i) = cls (col j) := by
  classical
  have h240 := card_roots_eq_240 A h.pos h.even h.det
  have h2160 := card_norm_four A h.pos h.even h.det
  have hRf := finite_of_card h240 (by norm_num)
  have hFf := finite_of_card h2160 (by norm_num)
  set R := hRf.toFinset with hRdef
  set F := hFf.toFinset with hFdef
  have hRc : R.card = 240 := by
    rw [← h240, hRdef, ← Nat.card_eq_card_finite_toFinset]; rfl
  have hFc : F.card = 2160 := by
    rw [← h2160, hFdef, ← Nat.card_eq_card_finite_toFinset]; rfl
  have memR : ∀ z, z ∈ R ↔ B A z z = 2 := by intro z; simp [R, B]
  have memF : ∀ z, z ∈ F ↔ B A z z = 4 := by intro z; simp [F, B]
  have hCR : 120 ≤ (R.image cls).card := by
    have key := Finset.card_le_mul_card_image (f := cls) R 2 (fun c hc => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hc
      calc (R.filter fun x => cls x = cls r).card ≤ ({r, -r} : Finset _).card :=
            Finset.card_le_card (fun x hx => by
              simp only [Finset.mem_filter] at hx
              rcases root_cls h ((memR x).mp hx.1) ((memR r).mp hr) hx.2 with e | e <;>
                simp [e])
        _ ≤ 2 := Finset.card_le_two)
    omega
  have hdisj : Disjoint (R.image cls) (F.image cls) := by
    refine Finset.disjoint_left.mpr fun c hc1 hc2 => ?_
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hc1
    obtain ⟨v, hv, e⟩ := Finset.mem_image.mp hc2
    exact root_norm4_cls h ((memR r).mp hr) ((memF v).mp hv) e.symm
  have h0F : (0 : Fin 8 → ZMod 2) ∉ F.image cls := by
    intro hc
    obtain ⟨v, hv, e⟩ := Finset.mem_image.mp hc
    exact norm4_cls_ne_zero h ((memF v).mp hv) e
  have h0R : (0 : Fin 8 → ZMod 2) ∉ R.image cls := by
    intro hc
    obtain ⟨r, hr, e⟩ := Finset.mem_image.mp hc
    exact root_cls_ne_zero h ((memR r).mp hr) e
  have hCF : (F.image cls).card ≤ 135 := by
    have hu : (R.image cls ∪ F.image cls ∪ {0}).card ≤ 256 := by
      calc _ ≤ Fintype.card (Fin 8 → ZMod 2) := Finset.card_le_univ _
        _ = 256 := by simp
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr (by simp [h0F, h0R])),
      Finset.card_union_of_disjoint hdisj, Finset.card_singleton] at hu
    omega
  obtain ⟨c, -, hfib⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := F) (t := F.image cls) (f := cls) (n := 15)
    (fun v hv => Finset.mem_image_of_mem cls hv) (by rw [hFc]; omega)
  set S := F.filter fun v => cls v = c with hS
  set Sp := S.filter fun v => toLex v < toLex (-v) with hSpdef
  have memS : ∀ v, v ∈ S ↔ B A v v = 4 ∧ cls v = c := by
    intro v; rw [hS, Finset.mem_filter, memF]
  have hne : ∀ v ∈ S, v ≠ -v := by
    intro v hv e
    have h0 : v = 0 := by
      ext i; have := congrFun e i
      simp only [Pi.neg_apply] at this
      simp only [Pi.zero_apply]; omega
    have := ((memS v).mp hv).1
    rw [h0] at this; simp [B] at this
  have hSp : 8 ≤ Sp.card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := S) (fun v => toLex v < toLex (-v))
    rw [← hSpdef] at hsplit
    have hneg : (S.filter fun v => ¬ toLex v < toLex (-v)).card ≤ Sp.card := by
      refine Finset.card_le_card_of_injOn (fun v => -v) (fun v hv => ?_)
        (fun a _ b _ e => neg_injective e)
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hv
      obtain ⟨hvS, hlt⟩ := hv
      have hvS' := (memS v).mp hvS
      simp only [hSpdef, Finset.coe_filter, Set.mem_ofPred_eq, neg_neg]
      refine ⟨(memS (-v)).mpr ⟨by rw [Q_neg]; exact hvS'.1, by rw [cls_neg]; exact hvS'.2⟩, ?_⟩
      have hle := not_lt.mp hlt
      refine lt_of_le_of_ne hle fun e => hne v hvS ?_
      exact (toLex.injective e).symm
    omega
  obtain ⟨t, htSp, htc⟩ := Finset.exists_subset_card_eq hSp
  let e : t ≃ Fin 8 := Finset.equivFinOfCardEq htc
  have hmem : ∀ i, (e.symm i : Fin 8 → ℤ) ∈ Sp := fun i => htSp (e.symm i).2
  have hS' : ∀ i, B A (e.symm i : Fin 8 → ℤ) (e.symm i) = 4 ∧ cls (e.symm i : Fin 8 → ℤ) = c :=
    fun i => (memS _).mp (Finset.mem_filter.mp (hmem i)).1
  have hlex : ∀ i, toLex (e.symm i : Fin 8 → ℤ) < toLex (-(e.symm i : Fin 8 → ℤ)) :=
    fun i => (Finset.mem_filter.mp (hmem i)).2
  refine ⟨fun i => (e.symm i : Fin 8 → ℤ), fun i j => ?_, fun i j => by
    rw [(hS' i).2, (hS' j).2]⟩
  split_ifs with hij
  · subst hij; exact (hS' i).1
  · have hne' : (e.symm i : Fin 8 → ℤ) ≠ e.symm j := fun h' =>
      hij (e.symm.injective (Subtype.ext h'))
    rcases norm4_cls h (hS' i).1 (hS' j).1 ((hS' i).2.trans (hS' j).2.symm) with h1 | h1 | h1
    · exact absurd h1 hne'
    · exfalso
      have a := hlex i
      have b := hlex j
      rw [h1, neg_neg] at a
      exact absurd (a.trans b) (lt_irrefl _)
    · exact h1

/-! ### From the frame to an explicit isometry -/

/-- E8 simple roots (Bourbaki order matching `Lattices.gram`), scaled by 2, in the coordinates
`D8 ∪ (D8 + ½(1,…,1))`. -/
def c1 : Fin 8 → Fin 8 → ℤ :=
  ![![1, -1, -1, -1, -1, -1, -1, 1], ![2, 2, 0, 0, 0, 0, 0, 0], ![-2, 2, 0, 0, 0, 0, 0, 0],
    ![0, -2, 2, 0, 0, 0, 0, 0], ![0, 0, -2, 2, 0, 0, 0, 0], ![0, 0, 0, -2, 2, 0, 0, 0],
    ![0, 0, 0, 0, -2, 2, 0, 0], ![0, 0, 0, 0, 0, -2, 2, 0]]

/-- Reflection in the first coordinate. -/
def flipc (v : Fin 8 → ℤ) : Fin 8 → ℤ := fun i => if i = 0 then -v i else v i

/-- The same basis for the other glue class `D8 + ½(-1,1,…,1)`. -/
def c2 : Fin 8 → Fin 8 → ℤ := fun k => flipc (c1 k)

def sig1 : Fin 8 → ℤ := fun _ => 1
def sig2 : Fin 8 → ℤ := flipc sig1
def sflag : Fin 8 → ℤ := fun k => if k = 0 then 1 else 0

lemma c1_gram : ∀ k l, c1 k ⬝ᵥ c1 l = 4 * Lattices.gram k l := by decide
lemma c2_gram : ∀ k l, c2 k ⬝ᵥ c2 l = 4 * Lattices.gram k l := by decide
lemma c1_mod : ∀ k i, (c1 k i - sflag k * sig1 i) % 2 = 0 := by decide
lemma c1_sum : ∀ k, (∑ i, (c1 k i - sflag k * sig1 i) / 2) % 2 = 0 := by decide
lemma c2_mod : ∀ k i, (c2 k i - sflag k * sig2 i) % 2 = 0 := by decide
lemma c2_sum : ∀ k, (∑ i, (c2 k i - sflag k * sig2 i) / 2) % 2 = 0 := by decide
lemma sig2_eq : sig2 = sig1 - (2 : ℤ) • Pi.single 0 1 := by decide

/-- Columns as a matrix. -/
def Vm (col : Fin 8 → Fin 8 → ℤ) : Matrix (Fin 8) (Fin 8) ℤ := Matrix.of fun k i => col i k

lemma B_mulVec (P : Matrix (Fin 8) (Fin 8) ℤ) (a b : Fin 8 → ℤ) :
    B A (P *ᵥ a) (P *ᵥ b) = a ⬝ᵥ ((Pᵀ * A * P) *ᵥ b) := by
  simp only [B]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec a, vecMul_transpose]

lemma col_eq (P : Matrix (Fin 8) (Fin 8) ℤ) (i : Fin 8) :
    P *ᵥ Pi.single i 1 = fun k => P k i := by
  ext k; simp

lemma gram_entry (P : Matrix (Fin 8) (Fin 8) ℤ) (i j : Fin 8) :
    (Pᵀ * A * P) i j = B A (fun k => P k i) (fun k => P k j) := by
  rw [← col_eq, ← col_eq, B_mulVec, mulVec_single_one, single_dotProduct, one_mul]
  rfl

section Frame
variable {col : Fin 8 → Fin 8 → ℤ}

lemma VtAV (horth : ∀ i j, B A (col i) (col j) = if i = j then 4 else 0) :
    (Vm col)ᵀ * A * Vm col = (4 : ℤ) • (1 : Matrix (Fin 8) (Fin 8) ℤ) := by
  ext i j
  rw [gram_entry]
  show B A (col i) (col j) = _
  rw [horth]
  by_cases hij : i = j <;> simp [hij]

lemma B_lin (horth : ∀ i j, B A (col i) (col j) = if i = j then 4 else 0) (a b : Fin 8 → ℤ) :
    B A (Vm col *ᵥ a) (Vm col *ᵥ b) = 4 * (a ⬝ᵥ b) := by
  rw [B_mulVec, VtAV horth, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

lemma V_mul_M (horth : ∀ i j, B A (col i) (col j) = if i = j then 4 else 0) :
    Vm col * ((Vm col)ᵀ * A) = (4 : ℤ) • (1 : Matrix (Fin 8) (Fin 8) ℤ) := by
  have hMV : ((Vm col)ᵀ * A) * Vm col = (4 : ℤ) • 1 := VtAV horth
  have hdet : (Vm col).det ≠ 0 := by
    intro h0
    have := congrArg det hMV
    rw [det_mul, h0, mul_zero, det_smul, det_one] at this
    norm_num at this
  set X := Vm col * ((Vm col)ᵀ * A) - (4 : ℤ) • 1 with hX
  have hXV : X * Vm col = 0 := by
    rw [hX, Matrix.sub_mul, Matrix.mul_assoc, hMV, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, sub_self]
  have h2 : (Vm col).det • X = 0 := by
    rw [← Matrix.mul_one X, ← Matrix.mul_smul, ← mul_adjugate, ← Matrix.mul_assoc, hXV,
      Matrix.zero_mul]
  rw [← sub_eq_zero, ← hX]
  exact (smul_eq_zero.mp h2).resolve_left hdet

lemma expand (horth : ∀ i j, B A (col i) (col j) = if i = j then 4 else 0) (y : Fin 8 → ℤ) :
    Vm col *ᵥ (fun i => B A (col i) y) = (4 : ℤ) • y := by
  have : (fun i => B A (col i) y) = ((Vm col)ᵀ * A) *ᵥ y := by
    ext i
    simp only [B, ← mulVec_mulVec]
    simp [Vm, mulVec, dotProduct, transpose_apply]
  rw [this, mulVec_mulVec, V_mul_M horth, smul_mulVec, one_mulVec]

lemma d8 (hcls : ∀ i j, cls (col i) = cls (col j)) (d : Fin 8 → ℤ) (hd : Even (∑ i, d i)) :
    ∃ w, Vm col *ᵥ d = (2 : ℤ) • w := by
  choose u hu using fun i => exists_of_cls_eq (hcls i 0)
  obtain ⟨m, hm⟩ := hd
  refine ⟨m • col 0 + fun k => ∑ i, u i k * d i, ?_⟩
  ext k
  have hc : ∀ i, col i k = col 0 k + 2 * u i k := fun i => by
    have := congrFun (hu i) k; simpa using this
  simp only [Vm, mulVec, dotProduct, of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e : ∑ i, col i k * d i = col 0 k * ∑ i, d i + 2 * ∑ i, u i k * d i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hc i]; ring
  rw [e, hm]; ring

lemma glue (h : Hyp A) (horth : ∀ i j, B A (col i) (col j) = if i = j then 4 else 0)
    (hcls : ∀ i j, cls (col i) = cls (col j)) :
    ∃ sg : Fin 8 → ℤ, (sg = sig1 ∨ sg = sig2) ∧ ∃ g, Vm col *ᵥ sg = (4 : ℤ) • g := by
  -- some lattice vector pairs oddly with `col 0`
  have hodd : ∃ y, Odd (B A (col 0) y) := by
    by_contra hall
    push Not at hall
    have hev : ∀ k, Even ((A *ᵥ col 0) k) := by
      intro k
      have := Int.not_odd_iff_even.mp (hall (Pi.single k 1))
      rwa [B_comm h, B, single_dotProduct, one_mul] at this
    choose w hw using hev
    have hA : A *ᵥ col 0 = (2 : ℤ) • w := by ext k; simp [hw k]; ring
    have hc0 : col 0 = (2 : ℤ) • (A⁻¹ *ᵥ w) := by
      rw [← mulVec_smul, ← hA, mulVec_mulVec, nonsing_inv_mul A h.det, one_mulVec]
    have h4 : B A (col 0) (col 0) = 4 := by simpa using horth 0 0
    rw [hc0, B_smul_left, B_smul_right] at h4
    obtain ⟨k, hk⟩ := Q_even h (A⁻¹ *ᵥ w)
    omega
  obtain ⟨y, hy⟩ := hodd
  choose u hu using fun i => exists_of_cls_eq (hcls i 0)
  have hodd_all : ∀ i, Odd (B A (col i) y) := by
    intro i
    rw [hu i, B_add_left, B_smul_left]
    exact hy.add_even (even_two_mul _)
  choose t ht using hodd_all
  have hsplit : (fun i => B A (col i) y) = sig1 + (2 : ℤ) • t := by
    ext i; simp [ht i, sig1]; ring
  have h4y := expand horth y
  rw [hsplit, mulVec_add, mulVec_smul] at h4y
  rcases Int.even_or_odd (∑ i, t i) with hte | hto
  · obtain ⟨w, hw⟩ := d8 hcls t hte
    refine ⟨sig1, Or.inl rfl, y - w, ?_⟩
    ext k
    have := congrFun h4y k
    have hwk := congrFun hw k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this hwk
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linarith
  · set e0 : Fin 8 → ℤ := Pi.single 0 1 with he0
    have hde : Even (∑ i, (t + e0) i) := by
      have : ∑ i, (t + e0) i = ∑ i, t i + 1 := by
        simp [he0, Finset.sum_add_distrib]
      rw [this]; exact hto.add_one
    obtain ⟨w, hw⟩ := d8 hcls (t + e0) hde
    refine ⟨sig2, Or.inr rfl, y - w, ?_⟩
    rw [sig2_eq, ← he0, mulVec_sub, mulVec_smul]
    rw [mulVec_add] at hw
    ext k
    have := congrFun h4y k
    have hwk := congrFun hw k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this hwk
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linarith

end Frame

/-- **Uniqueness of E8.** Every positive-definite even unimodular integral Gram matrix of size 8
is integrally equivalent to the explicit E8 Gram matrix. -/
theorem e8_unique (A : Matrix (Fin 8) (Fin 8) ℤ) (hpos : (A.map (Int.cast : ℤ → ℝ)).PosDef)
    (heven : ∀ z : Fin 8 → ℤ, Even (z ⬝ᵥ (A *ᵥ z))) (hdet : IsUnit A.det) :
    ∃ P : Matrix (Fin 8) (Fin 8) ℤ, IsUnit P.det ∧ Pᵀ * A * P = Lattices.gram := by
  have h : Hyp A := ⟨hpos, heven, hdet⟩
  obtain ⟨col, horth, hcls⟩ := exists_frame h
  obtain ⟨sg, hsg, g, hg⟩ := glue h horth hcls
  obtain ⟨c, hcg, hcmod, hcsum⟩ : ∃ c : Fin 8 → Fin 8 → ℤ,
      (∀ k l, c k ⬝ᵥ c l = 4 * Lattices.gram k l) ∧
      (∀ k i, (c k i - sflag k * sg i) % 2 = 0) ∧
      (∀ k, (∑ i, (c k i - sflag k * sg i) / 2) % 2 = 0) := by
    rcases hsg with rfl | rfl
    · exact ⟨c1, c1_gram, c1_mod, c1_sum⟩
    · exact ⟨c2, c2_gram, c2_mod, c2_sum⟩
  have hp : ∀ k, ∃ p, Vm col *ᵥ c k = (4 : ℤ) • p := by
    intro k
    set d : Fin 8 → ℤ := fun i => (c k i - sflag k * sg i) / 2 with hd
    have hcd : c k = sflag k • sg + (2 : ℤ) • d := by
      ext i
      have := hcmod k i
      simp only [hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      omega
    obtain ⟨w, hw⟩ := d8 hcls d (Int.even_iff.mpr (hcsum k))
    refine ⟨sflag k • g + w, ?_⟩
    rw [hcd, mulVec_add, mulVec_smul, mulVec_smul, hg, hw]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  choose p hp using hp
  let P : Matrix (Fin 8) (Fin 8) ℤ := Matrix.of fun i k => p k i
  have hgram : Pᵀ * A * P = Lattices.gram := by
    ext k l
    rw [gram_entry]
    show B A (p k) (p l) = _
    have := B_lin horth (c k) (c l)
    rw [hp k, hp l, B_smul_left, B_smul_right, hcg] at this
    linarith
  refine ⟨P, ?_, hgram⟩
  have hd := congrArg det hgram
  rw [det_mul, det_mul, det_transpose] at hd
  have hu := Lattices.gram_unimodular
  rw [← hd] at hu
  exact isUnit_of_mul_isUnit_right hu

end PMArch.E8Unique
