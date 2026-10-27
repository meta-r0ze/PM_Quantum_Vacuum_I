import ELEM.Hypotheses
import ELEM.Sieve.Range

/-!
# ELEM.Sieve.Main: the proof of `ELEM.Sieve`

`ELEM.Sieve` (ELEM.Hypotheses) is the residue-sieve proposition over `k < 4096`, `q = 8k + 3`.
It is `ELEM.Sieve.sieveOK_of_lt`, the eight kernel-checked chunks assembled, read off at `q = 8k + 3`.
-/

namespace ELEM.Sieve

/-- **The residue sieve below `2^15`.** -/
theorem sieve : ELEM.Sieve := by
  intro k hk h8
  rcases sieveOK_of_lt (q := 8 * k + 3) (by omega) (by omega) h8 with hs | hs
  · left
    simp only [survivors, List.mem_cons, List.not_mem_nil, or_false] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hs
  · right
    exact hs

end ELEM.Sieve
