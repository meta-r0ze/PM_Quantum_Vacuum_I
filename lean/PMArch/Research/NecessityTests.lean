import PMArch.OrthogonalExchange

/-!
# Testing necessity of orthogonal locality and nontrivial exchange

The examples are explicit operational protocols, not quantum-vacuum models.
Costs are positive per-operation time/action accounting, not a claim of
irreversible heat expenditure from a finite reserve for infinite time.
-/
noncomputable section
namespace PMArch.NecessityTests
open Matrix

/-- Physical separation into independent state factors suffices for
commutation. Linking metric orthogonality to this factorization is extra. -/
theorem separate_factors_commute {S T : Type*} (f : Equiv.Perm S) (g : Equiv.Perm T) :
    Equiv.prodCongr f (Equiv.refl T) * Equiv.prodCongr (Equiv.refl S) g =
    Equiv.prodCongr (Equiv.refl S) g * Equiv.prodCongr f (Equiv.refl T) := by
  apply Equiv.ext
  rintro ⟨s,t⟩
  rfl

/-- A nonnegative bilinear cross cost on the whole signed address lattice is
necessarily zero. Signed pairing cannot simply be a nonnegative count of
shared physical channels. -/
theorem nonnegative_cross_pairing_trivial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ x y, 0 ≤ x ⬝ᵥ (A *ᵥ y)) : ∀ x y, x ⬝ᵥ (A *ᵥ y) = 0 := by
  intro x y
  have hp := h x y
  have hn := h x (-y)
  simp only [Matrix.mulVec_neg, dotProduct_neg] at hn
  omega

/-- The primitive directions have orthogonal, additive label costs. -/
theorem orthogonal_label_costs :
    let A : Matrix (Fin 2) (Fin 2) ℤ := 1
    let x : Fin 2 → ℤ := ![1,0]
    let y : Fin 2 → ℤ := ![0,1]
    x ⬝ᵥ (A *ᵥ y) = 0 ∧ x ⬝ᵥ (A *ᵥ x) = 1 ∧
      y ⬝ᵥ (A *ᵥ y) = 1 ∧ (x+y) ⬝ᵥ (A *ᵥ (x+y)) = 2 := by decide

abbrev Bits := ZMod 2 × (ZMod 2 × ZMod 2)

/-- All state information, including the central phase bit, is retained. -/
def bitX : Equiv.Perm Bits where
  toFun := fun s => (s.1, s.2.1+1, s.2.2)
  invFun := fun s => (s.1, s.2.1-1, s.2.2)
  left_inv := by rintro ⟨a,x,y⟩; simp
  right_inv := by rintro ⟨a,x,y⟩; simp

def bitY : Equiv.Perm Bits where
  toFun := fun s => (s.1+s.2.1, s.2.1, s.2.2+1)
  invFun := fun s => (s.1-s.2.1, s.2.1, s.2.2-1)
  left_inv := by rintro ⟨a,x,y⟩; simp
  right_inv := by rintro ⟨a,x,y⟩; simp

def bitPhase : Equiv.Perm Bits where
  toFun := fun s => (s.1+1, s.2.1, s.2.2)
  invFun := fun s => (s.1-1, s.2.1, s.2.2)
  left_inv := by rintro ⟨a,x,y⟩; simp
  right_inv := by rintro ⟨a,x,y⟩; simp

theorem finite_central_exchange :
    bitPhase ≠ 1 ∧ bitX*bitY = bitPhase*(bitY*bitX) ∧
      bitPhase*bitX = bitX*bitPhase ∧ bitPhase*bitY = bitY*bitPhase := by decide

theorem finite_exchange_noncommuting : bitX*bitY ≠ bitY*bitX := by decide

theorem commutator_loop : bitX*bitY*bitX⁻¹*bitY⁻¹ = bitPhase := by decide

theorem phase_loop_period_two : bitPhase*bitPhase = 1 := by decide

/-- A cyclic internal controller gives an autonomous reversible update. Its
program is fixed; no time-dependent external input is supplied. -/
def controlled {S : Type*} (g : Fin 4 → Equiv.Perm S) : Equiv.Perm (Fin 4 × S) where
  toFun := fun p => (finRotate 4 p.1, g p.1 p.2)
  invFun := fun p => ((finRotate 4).symm p.1,
    (g ((finRotate 4).symm p.1)).symm p.2)
  left_inv := by rintro ⟨t,s⟩; simp
  right_inv := by rintro ⟨t,s⟩; simp

def program : Fin 4 → Equiv.Perm Bits := ![bitX,bitY,bitX⁻¹,bitY⁻¹]
def autonomous : Equiv.Perm (Fin 4 × Bits) := controlled program

theorem finite_protocol_size : Fintype.card (Fin 4 × Bits) = 32 := by decide

theorem autonomous_period_eight : ∀ s : Fin 4 × Bits, (autonomous^[8]) s = s := by decide

theorem autonomous_nonstatic : autonomous (0,(0,0,0)) ≠ (0,(0,0,0)) := by decide

theorem all_histories_reconstruct (t : ℕ) :
    Function.Injective ((autonomous : (Fin 4 × Bits) → (Fin 4 × Bits))^[t]) :=
  autonomous.injective.iterate t

/-- Every primitive loop operation can have positive toll. Zero geometric
cross cost is not zero total action for the commutator loop. -/
theorem loop_positive_action (c : ℝ) (hc : 0 < c) :
    (∑ _ : Fin 4, c) = 4*c ∧ 0 < ∑ _ : Fin 4, c := by
  constructor
  · simp
  · simpa using mul_pos (by norm_num : (0 : ℝ) < 4) hc

/-- The shared finite register can be local at each site; repeating the same
rule pointwise commutes with every relabeling of physical sites. -/
theorem pointwise_protocol_homogeneous {I : Type*} (e : Equiv.Perm I)
    (state : I → (Fin 4 × Bits)) :
    (fun i => autonomous (state (e i))) =
      (fun i => (fun j => autonomous (state j)) (e i)) := rfl

/-- Faithful integer-label operations repair the periodic-label limitation of
a Pauli matrix family. This is an algebraic model on a larger state space. -/
abbrev IntegerState := ZMod 2 × (ℤ × ℤ)

def integerMove (p : ℤ × ℤ) : Equiv.Perm IntegerState where
  toFun := fun s => (s.1 + ((p.2*s.2.1 : ℤ) : ZMod 2), p.1+s.2.1, p.2+s.2.2)
  invFun := fun s => (s.1 - ((p.2*(s.2.1-p.1) : ℤ) : ZMod 2), s.2.1-p.1, s.2.2-p.2)
  left_inv := by rintro ⟨a,x,y⟩; simp
  right_inv := by rintro ⟨a,x,y⟩; simp

def integerPhase : Equiv.Perm IntegerState where
  toFun := fun s => (s.1+1, s.2.1, s.2.2)
  invFun := fun s => (s.1-1, s.2.1, s.2.2)
  left_inv := by rintro ⟨a,x,y⟩; simp
  right_inv := by rintro ⟨a,x,y⟩; simp

theorem integer_move_faithful : Function.Injective integerMove := by
  intro p q h
  have hz := congrArg (fun f : Equiv.Perm IntegerState => (f (0,0,0)).2) h
  simpa [integerMove] using hz

theorem integer_exchange : integerMove (1,0) * integerMove (0,1) =
    integerPhase * (integerMove (0,1) * integerMove (1,0)) := by
  apply Equiv.ext
  rintro ⟨a,x,y⟩
  have htwo : (1 : ZMod 2)+1 = 0 := by decide
  simp [integerMove, integerPhase, Equiv.Perm.mul_apply,
    add_left_comm, add_comm, htwo]

theorem integer_phase_nontrivial : integerPhase ≠ 1 := by
  intro h
  have hz := congrArg (fun f : Equiv.Perm IntegerState => (f (0,0,0)).1) h
  norm_num [integerPhase] at hz

/-- A positive clock tick and invertible nontrivial evolution are compatible
with entirely commuting powers. Causality does not imply nontrivial exchange. -/
theorem causal_clock_commuting :
    finRotate 43 ≠ 1 ∧ ∀ i j : ℕ,
      (finRotate 43)^i * (finRotate 43)^j = (finRotate 43)^j * (finRotate 43)^i := by
  constructor
  · intro h
    have h0 := congrArg (fun f : Equiv.Perm (Fin 43) => f 0) h
    norm_num [finRotate_apply] at h0
  · intro i j
    rw [← pow_add, ← pow_add, Nat.add_comm]

/-- The same orthogonal-direction/noncommuting pattern occurs in the
Clifford algebra used in Paper II. These are exact matrix identities. Applying
OL universally to these direction generators would be incompatible with that
algebra; a different pairing/operator sector requires an explicit bridge. -/
def cliffordX : Matrix (Fin 2) (Fin 2) ℤ := !![0,1;1,0]
def cliffordZ : Matrix (Fin 2) (Fin 2) ℤ := !![1,0;0,-1]

theorem orthogonal_clifford_certificate :
    cliffordX*cliffordX = 1 ∧ cliffordZ*cliffordZ = 1 ∧
    cliffordXᵀ*cliffordX = 1 ∧ cliffordZᵀ*cliffordZ = 1 ∧
    cliffordX*cliffordZ = -(cliffordZ*cliffordX) ∧
    cliffordX*cliffordZ ≠ cliffordZ*cliffordX := by decide

/-- Reconstructing every binary control history is stronger than preserving
initial-state distinctions under a fixed autonomous update. -/
theorem finite_history_capacity {S : Type*} [Fintype S] (n : ℕ)
    (encode : (Fin n → Bool) → S) (hinj : Function.Injective encode) :
    2^n ≤ Fintype.card S := by
  have h := Fintype.card_le_of_injective encode hinj
  simpa using h

theorem no_unbounded_history_memory (S : Type*) [Fintype S] :
    ¬ (∀ n : ℕ, ∃ encode : (Fin n → Bool) → S, Function.Injective encode) := by
  intro h
  have hg : ∀ n : ℕ, n < 2^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih => simp only [pow_succ]; omega
  obtain ⟨encode, he⟩ := h (Fintype.card S + 1)
  have hc := finite_history_capacity _ encode he
  have hp := hg (Fintype.card S + 1)
  omega

end PMArch.NecessityTests
