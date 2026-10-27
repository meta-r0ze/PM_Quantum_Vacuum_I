import PMArch.SelfReadable
import PMArch.OrthogonalExchange
import PMArch.ClaimBoundary
import PMArch.ClockPlane
import PMArch.Channels
import PMArch.DiscriminantGroup
import PMArch.Sectors

/-!
# The vacuum postulates and the main selection theorem

A *substrate* is an integral symmetric quadratic cost on the address lattice `ℤⁿ`.
Each postulate below is a formal reading of a Persistence Mechanics requirement
for a persisting closed system. They are stated as hypotheses; their PM
motivation is recorded in the docstrings and in the paper's postulate table.

Main results:

* `geometric_selects_e8`: the geometric postulates plus Economy force `E₈`.
* `e8_satisfies`: `E₈` satisfies every postulate (the set is consistent).
* `vacuum_selects`: adding the clock postulates also forces `Δ = 43`, and the
  six-term index then lies in `(137.035999212381397211, 137.035999212381397213)`.

Rank divisibility by eight, positivity, evenness and unimodularity are not
assumed: they are derived from the postulates.
-/

namespace PMArch.Vacuum
open Matrix

/-- A candidate substrate: integral symmetric configuration cost on `ℤⁿ`. -/
structure Substrate where
  n : ℕ
  A : Matrix (Fin n) (Fin n) ℤ
  symm : A.IsSymm

/-- The geometric postulates. -/
structure Geometric (s : Substrate) : Prop where
  /-- **Finiteness.** Every bounded-cost set of states is finite. -/
  finite : ∀ c : ℤ, {z : Fin s.n → ℤ | z ⬝ᵥ (s.A *ᵥ z) ≤ c}.Finite
  /-- **Conservation under Closure.** Every one-bit distinction of the closed substrate is
  detectable by a substrate probe at one-bit resolution. -/
  readable : SelfReadable.BitReadable s.A
  /-- **Map.** Addresses are bits: every glue element is its own inverse, `2Λ* ⊆ Λ`. -/
  bitAddressed : ∃ M : Matrix (Fin s.n) (Fin s.n) ℤ, s.A * M = (2 : ℤ) • 1
  /-- **Protocol / Causality.** A nontrivial exchange law exists that is alternating
  (operations commute with themselves) and local (zero-pairing operations commute). -/
  exchange : ∃ C : OrthogonalExchange.Exchange s.n, OrthogonalExchange.Alternating C ∧
    OrthogonalExchange.OrthogonalLocal s.A C ∧ C ≠ 0

/-- **Economy** (PM selection principle): no substrate meeting the geometric postulates
has smaller rank. -/
def Economical (s : Substrate) : Prop := ∀ t : Substrate, Geometric t → s.n ≤ t.n

/-- What the geometric postulates imply about the lattice. -/
theorem geometric_lattice {s : Substrate} (h : Geometric s) :
    (s.A.map (Int.cast : ℤ → ℝ)).PosDef ∧ (∀ z, Even (z ⬝ᵥ (s.A *ᵥ z))) ∧
      IsUnit s.A.det ∧ 0 < s.n := by
  obtain ⟨C, halt, hloc, hC⟩ := h.exchange
  obtain ⟨M, hM⟩ := h.bitAddressed
  refine ⟨(Translation.posDef_iff_finite_levels s.symm).mpr h.finite,
    OrthogonalExchange.orthogonal_nontrivial_exchange_forces_even s.A s.symm C halt hloc hC,
    SelfReadable.bitAddressed_bitReadable_unimodular s.A M hM h.readable, ?_⟩
  rcases Nat.eq_zero_or_pos s.n with h0 | h0
  · exfalso; apply hC
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
    have hx : x = 0 := funext fun i => absurd i.2 (by omega)
    simp [hx]
  · exact h0

/-- Every substrate meeting the geometric postulates has rank at least eight. -/
theorem geometric_rank {s : Substrate} (h : Geometric s) : 8 ≤ s.n := by
  obtain ⟨hp, he, hd, hn⟩ := geometric_lattice h
  have := RankEight.rank_dvd_eight s.A hp he hd
  exact Nat.le_of_dvd hn this

/-- The `E₈` substrate. -/
def e8 : Substrate := ⟨8, Lattices.gram, Lattices.gram_symmetric⟩

theorem e8_geometric : Geometric e8 := by
  obtain ⟨hp, he, hd⟩ := RankEight.e8_even_unimodular
  refine ⟨(Translation.posDef_iff_finite_levels e8.symm).mp hp, ?_, ?_,
    OrthogonalExchange.e8_exchange_form_witness⟩
  · rw [SelfReadable.bitReadable_iff_odd]
    rcases Int.isUnit_iff.mp hd with h1 | h1 <;> change Odd Lattices.gram.det <;> rw [h1] <;> decide
  · refine ⟨(2 : ℤ) • Lattices.gramInverse, ?_⟩
    have h1 : Lattices.gram * Lattices.gramInverse = 1 :=
      mul_eq_one_comm.mp Lattices.gram_inverse
    change Lattices.gram * ((2 : ℤ) • Lattices.gramInverse) = (2 : ℤ) • 1
    rw [Matrix.mul_smul, h1]

theorem e8_economical : Economical e8 := fun _ ht => geometric_rank ht

/-- **Main lattice theorem.** The geometric postulates and Economy force `E₈`. -/
theorem geometric_selects_e8 {s : Substrate} (h : Geometric s) (hmin : Economical s) :
    ClaimBoundary.IsE8 s.A := by
  obtain ⟨hp, he, hd, hn⟩ := geometric_lattice h
  have hle : s.n ≤ 8 := hmin e8 e8_geometric
  obtain ⟨n, A, hs⟩ := s
  have h8 : n = 8 := RankEight.minimal_rank_eight_of_lattice A hp he hd hn hle
  subst h8
  obtain ⟨P, hP, hgram⟩ := E8Unique.e8_unique A hp he hd
  exact ⟨Equiv.refl _, P, hP, by simpa using hgram⟩

/-- The postulates are consistent and determine the substrate up to isometry. -/
theorem substrate_exists_unique :
    (∃ s, Geometric s ∧ Economical s) ∧
      ∀ s, Geometric s → Economical s → ClaimBoundary.IsE8 s.A :=
  ⟨⟨e8, e8_geometric, e8_economical⟩, fun _ h hm => geometric_selects_e8 h hm⟩

/-- Gram matrix of two orthogonal copies of a rank-4 sector of type `k`
(`Sectors.cand`: `A₄, D₄, A₃A₁, A₂A₂, A₂A₁A₁, A₁⁴`, the rank-4 simply-laced root lattices). -/
def sectorGram (k : Fin 6) : Matrix (Fin 8) (Fin 8) ℤ := fun i j =>
  if h : (i : ℕ) < 4 ∧ (j : ℕ) < 4 then Sectors.candF k ⟨i, h.1⟩ ⟨j, h.2⟩
  else if h' : 4 ≤ (i : ℕ) ∧ 4 ≤ (j : ℕ) then
    Sectors.candF k ⟨i - 4, by omega⟩ ⟨j - 4, by omega⟩
  else 0

/-- **Postulate B (sectors).** The substrate contains two orthogonal rank-4 root sectors of the
same type, one for addresses and one for internal state. Each is irreducible (not a further
orthogonal sum) and bit-addressed (involutive glue, the Map requirement applied to a sector). -/
def SectorPostulates (s : Substrate) : Prop :=
  ∃ (k : Fin 6) (S : Matrix (Fin s.n) (Fin 8) ℤ),
    Sectors.Connected (Sectors.candF k) ∧ Sectors.InvolutiveGlue (Sectors.cand k) ∧
    Sᵀ * s.A * S = sectorGram k

/-- The sectors are forced to be `D₄`; their glue classes then carry `8` minimal vectors each
(`Channels.minimal_class_card`), giving `N = 32`. -/
theorem sectors_are_d4 {s : Substrate} (h : SectorPostulates s) :
    ∃ S : Matrix (Fin s.n) (Fin 8) ℤ, Sᵀ * s.A * S = Channels.d4d4 := by
  obtain ⟨k, S, hc, hi, hS⟩ := h
  have hk := (Sectors.sector_selection k).mp ⟨hc, hi⟩
  subst hk
  refine ⟨S, hS.trans ?_⟩
  decide

theorem e8_sectors : SectorPostulates e8 :=
  ⟨1, Channels.sectorBasis, (Sectors.sector_selection 1).mpr rfl |>.1,
    (Sectors.sector_selection 1).mpr rfl |>.2, by
      have : sectorGram 1 = Channels.d4d4 := by decide
      rw [this]; exact Channels.e8_two_d4_sectors⟩

/-- Gram matrix of the plane `ℤu + ℤv`. -/
def planeGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (u v : Fin n → ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![u ⬝ᵥ (A *ᵥ u), u ⬝ᵥ (A *ᵥ v); u ⬝ᵥ (A *ᵥ v), v ⬝ᵥ (A *ᵥ v)]

/-- The clock postulates, with `Δ` the clock period.

* **Closure:** the clock's period lattice is a nondegenerate plane `ℤu + ℤv` of the substrate;
  its states are the plane's discriminant group `ℤ²/Gℤ²`, and one tick visits each state once,
  so `Δ` is the number of states. (`DiscriminantGroup.card_discriminant_group` gives
  `Δ = |det G| = |D|`, `D = B(u,v)² − Q(u)Q(v)`.)
* **Map:** the clock geometry is determined by its data: one torus class (class number one).
* **Causality:** one cycle serializes the `N = Channels.channelTotal` channel labels (`= 32`,
  `Channels.channel_total`) as active slots, each followed by an idle run `g i`, with
  `Δ = N + Σ g i`. Runs are uniformly bounded (Finiteness), and the schedule is
  reconstructable from gap-only local observations (no external clock or run-length counter):
  `Sectors.obs` is injective on the admissible class. -/
structure ClockPostulates (s : Substrate) (Δ : ℕ) : Prop where
  plane : ∃ u v : Fin s.n → ℤ, (planeGram s.A u v).det ≠ 0 ∧
    Δ = Nat.card ((Fin 2 → ℤ) ⧸ LinearMap.range (Matrix.toLin' (planeGram s.A u v))) ∧
    Clock.UniqueClock ((u ⬝ᵥ (s.A *ᵥ v)) ^ 2 - (u ⬝ᵥ (s.A *ᵥ u)) * (v ⬝ᵥ (s.A *ᵥ v)))
  schedule : ∃ (k : ℕ) (g : Fin Channels.channelTotal → ℕ), (∀ i, g i ≤ k) ∧
    Set.InjOn Sectors.obs {g : Fin Channels.channelTotal → ℕ | ∀ i, g i ≤ k} ∧
    Δ = Sectors.period g

/-- Causality bounds the period: `N ≤ Δ ≤ 2N`. -/
theorem period_window {Δ : ℕ} (h : ∃ (k : ℕ) (g : Fin Channels.channelTotal → ℕ), (∀ i, g i ≤ k) ∧
    Set.InjOn Sectors.obs {g : Fin Channels.channelTotal → ℕ | ∀ i, g i ≤ k} ∧
    Δ = Sectors.period g) : 32 ≤ Δ ∧ Δ ≤ 64 := by
  obtain ⟨k, g, hk, hinj, rfl⟩ := h
  have hN : 0 < Channels.channelTotal := by rw [Channels.channel_total]; norm_num
  have hk1 := (Sectors.obs_injOn_iff hN k).mp hinj
  have h2 := Sectors.period_le_two_mul g fun i => (hk i).trans hk1
  have h1 : Channels.channelTotal ≤ Sectors.period g := by unfold Sectors.period; omega
  have e := Channels.channel_total
  omega

/-- **Main theorem.** The vacuum postulates force the `E₈` substrate, the clock period
`Δ = 43`, and the stated bounds on the six-term index. -/
theorem vacuum_selects {s : Substrate} {Δ : ℕ} (h : Geometric s) (hmin : Economical s)
    (hsec : SectorPostulates s) (hc : ClockPostulates s Δ) :
    ClaimBoundary.IsE8 s.A ∧ (∃ S : Matrix (Fin s.n) (Fin 8) ℤ, Sᵀ * s.A * S = Channels.d4d4) ∧
      Δ = 43 ∧
      (137.035999212381397211 : ℝ) < impedance { baseline with period := Δ } ∧
      impedance { baseline with period := Δ } < (137.035999212381397213 : ℝ) := by
  obtain ⟨u, v, hdet, hcard, hU⟩ := hc.plane
  rw [DiscriminantGroup.card_discriminant_group _ hdet] at hcard
  have hD : (u ⬝ᵥ (s.A *ᵥ v)) ^ 2 - (u ⬝ᵥ (s.A *ᵥ u)) * (v ⬝ᵥ (s.A *ᵥ v)) < 0 := by
    obtain ⟨⟨f, hf, hfd⟩, _⟩ := hU
    rw [← hfd]; exact hf.2
  have hdetv : (planeGram s.A u v).det =
      (u ⬝ᵥ (s.A *ᵥ u)) * (v ⬝ᵥ (s.A *ᵥ v)) - (u ⬝ᵥ (s.A *ᵥ v)) ^ 2 := by
    simp [planeGram, Matrix.det_fin_two]; ring
  have hΔ : (Δ : ℤ) = (u ⬝ᵥ (s.A *ᵥ u)) * (v ⬝ᵥ (s.A *ᵥ v)) - (u ⬝ᵥ (s.A *ᵥ v)) ^ 2 := by
    rw [hcard, ← hdetv, Int.natCast_natAbs, abs_of_pos (by rw [hdetv]; linarith)]
  have hw := period_window hc.schedule
  have hΔ' : (Δ : ℤ) = -((u ⬝ᵥ (s.A *ᵥ v)) ^ 2 - (u ⬝ᵥ (s.A *ᵥ u)) * (v ⬝ᵥ (s.A *ᵥ v))) := by
    rw [hΔ]; ring
  have hD := (Clock.clock_unique_iff _ (by omega) (by omega)).mp hU
  have h43 : Δ = 43 := by omega
  subst h43
  exact ⟨geometric_selects_e8 h hmin, sectors_are_d4 hsec, rfl, geometricIndex_bounds⟩
/-- `E₈` with the 43-cycle satisfies the clock postulates. -/
lemma first_eleven (m : ℕ) (hm : 11 ≤ m) :
    ∑ i : Fin m, (if (i : ℕ) < 11 then 1 else 0) = 11 := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, if_neg (by omega), add_zero]

theorem e8_clock : ClockPostulates e8 43 := by
  obtain ⟨h1, h2, h3⟩ := ClockPlane.e8_plane_gram
  have hg : planeGram e8.A ClockPlane.cu ClockPlane.cv = !![2, 1; 1, 22] := by
    unfold planeGram; erw [h1, h2, h3]
  have hN : 11 ≤ Channels.channelTotal := by rw [Channels.channel_total]; norm_num
  refine ⟨⟨ClockPlane.cu, ClockPlane.cv, by rw [hg]; simp [Matrix.det_fin_two], ?_, ?_⟩,
    ⟨1, fun i => if (i : ℕ) < 11 then 1 else 0, fun i => by dsimp only; split_ifs <;> omega,
      (Sectors.obs_injOn_iff (by omega) 1).mpr le_rfl, ?_⟩⟩
  · rw [hg, DiscriminantGroup.card_discriminant_group _ (by simp [Matrix.det_fin_two])]
    simp [Matrix.det_fin_two]
  · dsimp only [e8]
    erw [h1, h2, h3]
    exact (Clock.clock_unique_iff _ (by norm_num) (by norm_num)).mpr (by norm_num)
  · unfold Sectors.period
    rw [first_eleven _ hN, Channels.channel_total]

/-- All postulates together are consistent. -/
theorem postulates_consistent :
    ∃ s Δ, Geometric s ∧ Economical s ∧ SectorPostulates s ∧ ClockPostulates s Δ :=
  ⟨e8, 43, e8_geometric, e8_economical, e8_sectors, e8_clock⟩

end PMArch.Vacuum
