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

*Reference:* [erdosproblems.com/683](https://www.erdosproblems.com/683)
-/

namespace Erdos683

/-- Let `P(n, k)` be the largest prime factor of `n choose k`. -/
def P (n k : ℕ) : ℕ := (n.choose k).primeFactors.max

/--
There exists $c > 0$ such that $P(n, k) > \min\{n-k+1, k^{1 + c}\}$ for all $0 \le k \le n$.}
-/
@[category research open, AMS 11]
theorem erdos_683 : (∃ c > 0, ∀ n k : ℕ, k ≤ n → P n k > min (n - k + 1) (k ^ (1 + c))) ↔
    answer(sorry) := by
  sorry

end Erdos683
