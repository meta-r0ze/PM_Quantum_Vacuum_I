import CN1.Finite.SplitPrime

/-!
# ELEM.Sieve.Defs: the residue sieve below `2^15` and the two uniform `p = 2` lemmas

The residue sieve. For an imaginary quadratic field of discriminant
`-q`, a prime `p` with `4p ≤ q` (and `p ≠ c`) at which the principal polynomial `X² - t·X + c` has a
root mod `p` forces `h ≠ 1` (`CN1.Finite.classNumber_ne_one_of_isWitness`). So `h = 1` makes every
such small prime inert, and the finite range is closed by exhibiting, for every `q < 2^15` outside
the nine, one small prime that is NOT inert:

* `m ≢ 3 (mod 4)`, `m ≥ 3` (so `q = 4m`): `p = 2` ramifies, root `y = m mod 2`
  (the closure uses `ELEM.isWitness_two_of_not_mod_four` in ELEM.Glue);
* `m ≡ 7 (mod 8)`, `m ≥ 15` (so `q = m`, `c = (m+1)/4` even): `p = 2` splits, root `y = 0`
  (the closure uses `ELEM.isWitness_two_of_mod_eight` in ELEM.Glue);
* `q = m ≡ 3 (mod 8)`, `8 < q < 2^15`: the residue sieve over the odd primes `3, …, 31`, checked by
  the kernel in `ELEM.Sieve.Chunk0` to `Chunk7` and assembled in `ELEM.Sieve.Range`; the
  candidates are all `4,095` integers `q = 8k + 3`, squarefree or not, and the only ones no sieve
  prime rejects are `11, 19, 43, 67, 163`.

The residue sieve and its use of `p | q` (a ramified prime rejects as a split one does) are those of
the elementary companion (twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae),
section 6, where the sieve is credited to Kyle Pratt; the Lean statement and proofs here are ours.

Unused here: `prime_of_mem_sievePrimes`, `isWitness_of_sieveHit`,
`isWitness_two_of_mod_four_ne_three` and `isWitness_two_of_mod_eight_eq_seven` are not in the closure of
`CN1.classNumber_eq_one_iff`. The final theorem reads this development only through `ELEM.Sieve.sieve`
(ELEM.Sieve.Main) and the definitions it unfolds; the glue proves its own `p = 2` lemmas.
-/

namespace ELEM.Sieve

open CN1.Finite

/-- The odd sieve primes, `3 ≤ p ≤ 31`. -/
def sievePrimes : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

/-- The candidates `q ≡ 3 (mod 8)`, `8 < q < 2^15`, that no sieve prime rejects. -/
def survivors : List ℕ := [11, 19, 43, 67, 163]

/-- `X² - X + c` has a root mod `p`, written over `ℕ` with `-y ≡ (p - 1)·y`. -/
def HasRoot (p c : ℕ) : Prop := ∃ y, y < p ∧ (y ^ 2 + (p - 1) * y + c) % p = 0

instance (p c : ℕ) : Decidable (HasRoot p c) :=
  inferInstanceAs (Decidable (∃ y, y < p ∧ (y ^ 2 + (p - 1) * y + c) % p = 0))

/-- Some prime `p` of the list `P` with `4p < q` is not inert in the field of discriminant `-q`
(`q ≡ 3 mod 4`, `c = (q + 1)/4`): the principal polynomial has a root mod `p`. -/
def SieveHit (P : List ℕ) (q : ℕ) : Prop := ∃ p ∈ P, 4 * p < q ∧ HasRoot p ((q + 1) / 4)

instance (P : List ℕ) (q : ℕ) : Decidable (SieveHit P q) :=
  inferInstanceAs (Decidable (∃ p ∈ P, 4 * p < q ∧ HasRoot p ((q + 1) / 4)))

/-- The sieve's verdict on `q`: listed in `S`, or rejected by a prime of `P`. -/
def SieveOK (S P : List ℕ) (q : ℕ) : Prop := q ∈ S ∨ SieveHit P q

instance (S P : List ℕ) (q : ℕ) : Decidable (SieveOK S P q) :=
  inferInstanceAs (Decidable (q ∈ S ∨ SieveHit P q))

/-- Unused; not in the closure of `CN1.classNumber_eq_one_iff`. The sieve primes are prime. -/
theorem prime_of_mem_sievePrimes {p : ℕ} (hp : p ∈ sievePrimes) : p.Prime := by
  simp only [sievePrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Unused; not in the closure of `CN1.classNumber_eq_one_iff`. A sieve hit at `q = m ≡ 3 (mod 4)` is a CN-1 witness for `m`. -/
theorem isWitness_of_sieveHit {m : ℕ} (hm : m % 4 = 3) (h : SieveHit sievePrimes m) :
    ∃ p y, IsWitness m p y := by
  obtain ⟨p, hpP, hpq, y, hyp, hroot⟩ := h
  have hp := prime_of_mem_sievePrimes hpP
  have ht : tOf m = 1 := tOf_of_mod m hm
  have hc : cOf m = (m + 1) / 4 := by simp [cOf, hm]
  have hd : dOf m = m := dOf_of_mod m hm
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hyy : y ≤ y ^ 2 := by nlinarith
  -- `y² + (p-1)·y + c = (y² + c - y) + p·y`
  have hsplit : y ^ 2 + (p - 1) * y + (m + 1) / 4 = (y ^ 2 + (m + 1) / 4 - y) + p * y := by
    have : (p - 1) * y = p * y - y := Nat.sub_one_mul p y
    have : y ≤ p * y := Nat.le_mul_of_pos_left y hp1
    omega
  refine ⟨p, y, hp, ?_, ?_, ?_, ?_⟩
  · rw [ht, hc]; omega
  · rw [ht, hc, one_mul]
    have h0 : p ∣ y ^ 2 + (p - 1) * y + (m + 1) / 4 := Nat.dvd_of_mod_eq_zero hroot
    rw [hsplit] at h0
    exact (Nat.dvd_add_left (Dvd.intro y rfl)).mp h0
  · rw [hd]; omega
  · rw [hc]; omega

/-- Unused; not in the closure of `CN1.classNumber_eq_one_iff`. **`p = 2` ramifies.** For `m ≢ 3 (mod 4)` with `m ≥ 3` (discriminant `-4m`, `t = 0`, `c = m`),
`X² + m` has the root `m mod 2` modulo `2`, and `8 ≤ 4m`, `2 ≠ m`. -/
theorem isWitness_two_of_mod_four_ne_three {m : ℕ} (h : m % 4 ≠ 3) (hm : 3 ≤ m) :
    IsWitness m 2 (m % 2) := by
  have ht : tOf m = 0 := by simp [tOf, h]
  have hc : cOf m = m := by simp [cOf, h]
  have hd : dOf m = 4 * m := by simp [dOf, h]
  refine ⟨Nat.prime_two, ?_, ?_, ?_, ?_⟩
  · rw [ht, zero_mul]; exact Nat.zero_le _
  · rw [ht, hc, zero_mul, Nat.sub_zero]
    rcases Nat.mod_two_eq_zero_or_one m with h2 | h2 <;> rw [h2] <;> omega
  · rw [hd]; omega
  · rw [hc]; omega

/-- Unused; not in the closure of `CN1.classNumber_eq_one_iff`. **`p = 2` splits.** For `m ≡ 7 (mod 8)` with `m ≥ 15` (discriminant `-m`, `t = 1`,
`c = (m+1)/4` even), `X² - X + c` has the root `0` modulo `2`, and `8 ≤ m`, `2 ≠ c`. -/
theorem isWitness_two_of_mod_eight_eq_seven {m : ℕ} (h : m % 8 = 7) (hm : 15 ≤ m) :
    IsWitness m 2 0 := by
  have h4 : m % 4 = 3 := by omega
  have ht : tOf m = 1 := tOf_of_mod m h4
  have hc : cOf m = (m + 1) / 4 := by simp [cOf, h4]
  have hd : dOf m = m := dOf_of_mod m h4
  refine ⟨Nat.prime_two, ?_, ?_, ?_, ?_⟩
  · rw [ht, mul_zero]; exact Nat.zero_le _
  · rw [ht, hc, mul_zero, Nat.sub_zero]; omega
  · rw [hd]; omega
  · rw [hc]; omega

end ELEM.Sieve
