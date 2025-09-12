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
# Erdős Problem 975

*References:*
 - [erdosproblems.com/975](https://www.erdosproblems.com/975)
 - [Va39] van der Corput, J. G., Une in\'egalit\'e{} relative au nombre des diviseurs. Nederl. Akad. Wetensch., Proc. (1939), 547--553.
 - [Er52b] Erd\"os, P., On the sum {$\sum^x_{k=1} d(f(k))$}. J. London Math. Soc. (1952), 7--15.
-/

open Filter Real Polynomial

namespace Erdos975

/- Sum of $\tau(f(n))$ for a function $f : \mathbb{N} \to \mathbb{N}$. -/
noncomputable def erdos975Sum (f : ℕ → ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (f n).divisors.card

/--
For an irreducible polynomial $f \in \mathbb{Z}[x]$ with $f(n) \ge 0$ for all $n \ge 0$,
does there exists a constant $c = c(f) > 0$ such that
$\sum_{n \le x} \tau(f(n)) \approx c \cdot x \log x$?
-/
@[category research open, AMS 11]
theorem erdos_975 (f : ℕ → ℕ) (hf : ∃ g : ℤ[X], Irreducible g ∧ ∀ n : ℕ, f n = g.eval ↑n) :
    ∃ (c : ℝ), c > 0 ∧ Tendsto (fun x ↦ erdos975Sum f x / (x * x.log)) (atTop) (nhds c) := by
  sorry

/--
The correctness of growth rate is shown in [Va39] (lower bound) and [Er52b] (upper bound).
-/
@[category research solved, AMS 11]
theorem erdos_975.variant.upper_bound (f : ℕ → ℕ)
    (hf : ∃ g : ℤ[X], Irreducible g ∧ ∀ n : ℕ, f n = g.eval ↑n) :
    erdos975Sum f =O[atTop] (fun x ↦ x * x.log) := by
  sorry

@[category research solved, AMS 11]
theorem erdos_975.variant.lower_bound (f : ℕ → ℕ)
    (hf : ∃ g : ℤ[X], Irreducible g ∧ ∀ n : ℕ, f n = g.eval ↑n) :
    (fun x ↦ x * x.log) =O[atTop] (erdos975Sum f) := by
  sorry

end Erdos975
