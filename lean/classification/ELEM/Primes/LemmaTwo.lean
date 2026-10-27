import ELEM.Hypotheses
import ELEM.Primes.Theta
import ELEM.Primes.SumLogDivSq
import ELEM.Primes.Mertens

/-!
# Lemma 2 of the elementary companion, against the fixed statements of `ELEM.Hypotheses`

The companion is twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae.
The three estimates of its Lemma 2, with its constants:

* `θ(x) < (3/2) x` for `x ≥ 1` (`ELEM.LemmaTwoTheta`);
* `log m - 7/3 < A(m) < log m + 3/2` for integers `m ≥ 2` (`ELEM.LemmaTwoA`);
* `∑_p (log p)/p²` converges and `B < 2/3` (`ELEM.LemmaTwoB`).

The proofs are in `ELEM.Primes.Theta`, `ELEM.Primes.SumLogDivSq` and `ELEM.Primes.Mertens`.
-/

namespace ELEM.Primes

/-- Lemma 2, `θ(x) < (3/2) x`. -/
theorem lemmaTwoTheta : ELEM.LemmaTwoTheta := fun _ hx =>
  theta_lt_three_halves_mul (by linarith)

/-- Lemma 2, `log m - 7/3 < A(m) < log m + 3/2`. -/
theorem lemmaTwoA : ELEM.LemmaTwoA := fun _ hm =>
  ⟨log_sub_lt_sum_log_div (by omega), sum_log_div_lt_log_add (by omega)⟩

/-- Lemma 2, `B < 2/3` (with summability). -/
theorem lemmaTwoB : ELEM.LemmaTwoB :=
  ⟨summable_log_div_sq, tsum_log_div_sq_lt_two_thirds⟩

end ELEM.Primes
