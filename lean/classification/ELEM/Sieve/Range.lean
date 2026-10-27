import ELEM.Sieve.Defs
import ELEM.Sieve.Chunk0
import ELEM.Sieve.Chunk1
import ELEM.Sieve.Chunk2
import ELEM.Sieve.Chunk3
import ELEM.Sieve.Chunk4
import ELEM.Sieve.Chunk5
import ELEM.Sieve.Chunk6
import ELEM.Sieve.Chunk7

/-!
# ELEM.Sieve.Range: the finite part below `2^15`, in terms of `q = |disc K| = dOf m`

`sieveOK_of_lt` collects the eight kernel-checked chunks into one statement over all
`q ≡ 3 (mod 8)` with `8 < q < 2^15`; `ELEM.Sieve.sieve` (ELEM.Sieve.Main) reads it off, and the finite
part of the final theorem is the glue's `ELEM.classNumber_ne_one_of_lt`, over `dOf m`.
`exists_isWitness_of_dOf_lt` (every radicand `m ≠ 0` outside the nine with `dOf m < 2^15` has a CN-1
witness) and `not_sieveHit_survivors` are unused: neither is in the closure of
`CN1.classNumber_eq_one_iff`.
-/

namespace ELEM.Sieve

open CN1.Finite

/-- **The residue sieve, assembled.** Every `q ≡ 3 (mod 8)` with `8 < q < 2^15` is one of
`11, 19, 43, 67, 163` or is rejected by a sieve prime. -/
theorem sieveOK_of_lt {q : ℕ} (hq : q < 32768) (h3 : q % 8 = 3) (h8 : 8 < q) :
    SieveOK survivors sievePrimes q := by
  obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < 512 ∧ q = 8 * (512 * i + j) + 3 :=
    ⟨q / 8 / 512, q / 8 % 512, Nat.mod_lt _ (by norm_num), by omega⟩
  have hi : i < 8 := by omega
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sieveOK_chunk0 j hj h8
  · exact sieveOK_chunk1 j hj h8
  · exact sieveOK_chunk2 j hj h8
  · exact sieveOK_chunk3 j hj h8
  · exact sieveOK_chunk4 j hj h8
  · exact sieveOK_chunk5 j hj h8
  · exact sieveOK_chunk6 j hj h8
  · exact sieveOK_chunk7 j hj h8

/-- Unused; not in the closure of `CN1.classNumber_eq_one_iff`. Every `m ≠ 0` outside the nine with `dOf m < 2^15` has a witness prime:
`p = 2` when `m ≢ 3 (mod 4)` or `m ≡ 7 (mod 8)`, and a sieve prime `3 ≤ p ≤ 31` when
`m ≡ 3 (mod 8)`. Squarefreeness is not needed. -/
theorem exists_isWitness_of_dOf_lt {m : ℕ} (hm0 : m ≠ 0) (hd : dOf m < 32768)
    (hnine : m ∉ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)) : ∃ p y, IsWitness m p y := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnine
  obtain ⟨h1, h2, h3, h7, h11, h19, h43, h67, h163⟩ := hnine
  by_cases h4 : m % 4 = 3
  · rw [dOf_of_mod m h4] at hd
    by_cases h87 : m % 8 = 7
    · exact ⟨2, 0, isWitness_two_of_mod_eight_eq_seven h87 (by omega)⟩
    · rcases sieveOK_of_lt hd (by omega) (by omega) with hs | hs
      · simp only [survivors, List.mem_cons, List.not_mem_nil, or_false] at hs
        omega
      · exact isWitness_of_sieveHit h4 hs
  · exact ⟨2, m % 2, isWitness_two_of_mod_four_ne_three h4 (by omega)⟩

/-- Unused; not in the closure of `CN1.classNumber_eq_one_iff`. The five survivors do survive: no sieve prime rejects them (so the survivor list is exact). -/
theorem not_sieveHit_survivors : ∀ q ∈ survivors, ¬ SieveHit sievePrimes q := by
  decide +kernel

end ELEM.Sieve
