import CN1.Foundations.Splitting
import CN1.Foundations.Discr
import CN1.Finite.SplitPrime
import CN1.Finite.Converse
import CN1.Finite.Witnesses

/-!
# CN1.Finite.Bridge: the finite part on top of the foundations (step 6 of the argument)

`CN1.Foundations.Basic` provides `omegaInt hα : 𝓞 K`, the decomposition `z = u + v·ω` of every
element of `𝓞 K`, and the norm form `Algebra.norm ℤ (x + y·ω) = principalForm m x y`. With
`minpoly_int_omegaInt` (`CN1.Foundations.Splitting`; `bInt m = -tOf m`, `cInt m = cOf m`) this gives
the `QuadInt` interface of `CN1.Finite.SplitPrime` outright, and `discr_eq` (`CN1.Foundations.Discr`)
discharges the converse's `|discr K| ≤ d`. The two final theorems take only the challenge statement's
hypotheses (`hK`, `hm`, `hsq`) plus the `d`-range or the membership in the nine.
-/

open NumberField Module Polynomial CN1.Foundations

namespace CN1.Finite

variable {K : Type*} [Field K] [NumberField K]

theorem disc_eq_dOf (m : ℕ) : disc m = dOf m := rfl

theorem principalForm_eq (m : ℕ) (x y : ℤ) :
    principalForm m x y = x ^ 2 + (tOf m : ℤ) * x * y + (cOf m : ℤ) * y ^ 2 := by
  unfold principalForm tOf cOf
  split_ifs <;> push_cast <;> ring

theorem bInt_eq (m : ℕ) : bInt m = -(tOf m : ℤ) := by
  unfold bInt tOf; split_ifs <;> simp

theorem cInt_eq (m : ℕ) : cInt m = (cOf m : ℤ) := by
  unfold cInt cOf; split_ifs <;> simp

/-- The foundations' data assembled into the `QuadInt` interface. -/
noncomputable def quadIntOfFoundations (hK : finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m) {α : K}
    (hα : α ^ 2 = -(m : K)) : QuadInt K (tOf m) (cOf m) where
  θ := omegaInt hα
  adjoin_eq_top := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨u, v, rfl⟩ := exists_int_add_int_mul_omegaInt hα hK hm z
    exact Subalgebra.add_mem _ (Subalgebra.intCast_mem _ _)
      (Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (Algebra.self_mem_adjoin_singleton ℤ _))
  minpoly_eq := by
    rw [minpoly_int_omegaInt hα hm.ne_zero, bInt_eq, cInt_eq, map_neg, neg_mul, sub_eq_add_neg]
  norm_eq := fun x y => by
    rw [norm_int_eq_principalForm hα hK hm.ne_zero rfl, principalForm_eq]

/-- **The finite part on the foundations.** For squarefree `m` with `dOf m ≤ 652` outside the nine,
`classNumber K ≠ 1`. Only the challenge statement's hypotheses and the `d`-range remain. -/
theorem classNumber_ne_one_of_foundations (hK : finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : dOf m ≤ 652) (hnine : m ∉ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)) :
    classNumber K ≠ 1 := by
  obtain ⟨α, hα⟩ := hsq
  exact classNumber_ne_one_of_quadInt (quadIntOfFoundations hK hm hα) hm hd hnine

/-- **The converse on the foundations.** For the nine radicands, `classNumber K = 1`. -/
theorem classNumber_eq_one_of_foundations (hK : finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hnine : m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)) : classNumber K = 1 := by
  obtain ⟨α, hα⟩ := hsq
  exact classNumber_eq_one_of_mem_nine hK m hnine ⟨α, hα⟩
    (by rw [discr_eq hα hK hm, abs_neg, Nat.abs_cast, disc_eq_dOf])

end CN1.Finite
