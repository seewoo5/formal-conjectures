/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 683

*References:*
- [erdosproblems.com/683](https://www.erdosproblems.com/683)
- [Er34] Erdős, Paul, A Theorem of Sylvester and Schur. J. London Math. Soc. (1934), 282--288.
- [Er55d] Erdős, P., On consecutive integers. Nieuw Arch. Wisk. (3) (1955), 124--128.
- [Er79d] Erdős, P., Some unconventional problems in number theory. Acta Math. Acad. Sci. Hungar. (1979), 71-80.
-/

namespace Erdos683

def withBotToNat : WithBot ℕ → ℕ
| ⊥       => 0
| (n : ℕ) => n

/--
Let $P(n, k)$ be the largest prime factor of $\binom{n}{k}$.
Note that `(n.choose k).primeFactors.max` returns a `WithBot ℕ` to account for the empty set case,
so we convert it to `ℕ` with `withBotToNat`. Note that we will only consider the case where
$0 < k < n$, so $\binom{n}{k}$ is always greater than 0 and thus has at least one prime factor.
-/
def P (n k : ℕ) : ℕ := withBotToNat (n.choose k).primeFactors.max

/--
There exists $c > 0$ such that $P(n, k) > \min\{n-k+1, k^{1 + c}\}$ for all $0 \le k \le n$.}
-/
@[category research open, AMS 11]
theorem erdos_683 : (∃ c > 0, ∀ n k : ℕ, 0 < k ∧ k < n → P n k > min (n - k + 1) (k ^ (1 + c))) ↔
    answer(sorry) := by
  sorry

/--
Sylvester and Schur [Er34] proved that $P(n, k) > k$ for $k \le n/2$.
-/
@[category research solved, AMS 11]
theorem erdos_683.variant.sylvester_schur :
    ∀ n k : ℕ, 0 < k ∧ k ≤ n / 2 → P n k > k := by
  sorry

/--
Erdos [Er55d] improved this to $P(n, k) \gg k \log k $ for $k \le n/2$.
-/
@[category research solved, AMS 11]
theorem erdos_683.variant.erdos_log :
    ∃ C > 0, ∀ n k : ℕ, 0 < k ∧ k ≤ n / 2 → P n k > C * k * Real.log k := by
  sorry

/--
Standard heuristics suggest that $P(n, k) > e^{c\sqrt{k}}$ for some constant $c > 0$.
-/
@[category research open, AMS 11]
theorem erdos_683.variant.exp_sqrt :
    ∃ c > 0, ∀ n k : ℕ, 0 < k ∧ k ≤ n / 2 → P n k > Real.exp (c * Real.sqrt k) := by
  sorry

end Erdos683
