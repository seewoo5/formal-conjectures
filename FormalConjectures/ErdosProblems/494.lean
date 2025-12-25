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
# Erdős Problem 494

*Reference:* [erdosproblems.com/494](https://www.erdosproblems.com/494)
-/

open Filter
namespace Erdos494

/--
For a finite set $A \subset \mathbb{C}$ and $k \ge 1$, define $A_k$ as a multiset consisting of
all sums of $k$ distinct elements of $A$.
-/
noncomputable def erdos494_A_k (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  ((A.powersetCard k).val.map (fun s => s.sum id))

def erdos_494_unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → A.card = B.card → erdos494_A_k A k = erdos494_A_k B k → A = B

/--
Selfridge and Straus [SeSt58] showed that the conjecture is true when $k = 2$ and
$|A| \ne 2^l$ for $l \ge 0$.
They also gave counterexamples when $k = 2$ and $|A| = 2^l$.
-/
@[category research solved, AMS 11] -- Change tag
theorem erdos_494.variant.k_eq_2_card_not_pow_two :
    ∀ card : ℕ, (¬∃ l : ℕ, card = 2 ^ l) → erdos_494_unique 2 card := by
  sorry

@[category research solved, AMS 11] -- Change tag
theorem erdos_494.variant.k_eq_2_card_pow_two :
    ∀ card : ℕ, (∃ l : ℕ, card = 2 ^ l) → ¬erdos_494_unique 2 card := by
  sorry

/--
Selfridge and Straus [SeSt58] also showed that the conjecture is true when
1) $k = 3$ and $|A| > 6$ or
2) $k = 4$ and $|A| > 12$.
More generally, they proved that $A$ is determined by $A_k$ (and $|A|$) if $|A|$ is divisible by
a prime greater than $k$.
-/
@[category research solved, AMS 11] -- Change tag
theorem erdos_494.variant.k_eq_3_card_gt_6 :
    ∀ card : ℕ, card > 6 → erdos_494_unique 3 card := by
  sorry

@[category research solved, AMS 11] -- Change tag
theorem erdos_494.variant.k_eq_4_card_gt_12 :
    ∀ card : ℕ, card > 12 → erdos_494_unique 4 card := by
  sorry

/--
Kruyt noted that the conjecture fails when $k = |A|$, by rotating $A$ around an appropriate point.
-/
@[category research solved, AMS 11] -- Change tag
theorem erdos_494.variant.k_eq_card :
    ∀ card : ℕ, 1 ≤ card → ¬erdos_494_unique card card := by
  sorry

/--
Gordon, Fraenkel, and Straus [GRS62] proved that the claim is true for all $k > 2$ when
$|A|$ is sufficiently large.
-/
@[category research solved, AMS 11] -- Change tag
theorem erdos_494.variant.gordon_fraenkel_straus :
    ∀ k : ℕ, 2 < k → (∀ᶠ card in atTop, erdos_494_unique k card) := by
  sorry

/--
A version in [Er61] by Erdős is product instead of sum, which is false.
Counterexample (by Steinerberger): consider $k = 3$ and let
$A = \{1, \zeta_6, \zeta_6^2, \zeta_6^4\}$ and $B = \{1, \zeta_6^2, \zeta_6^3, \zeta_6^4\}$.
-/
noncomputable def erdos494_A_k_prod (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  ((A.powersetCard k).val.map (fun s => s.prod id))

@[category research solved, AMS 11] -- Change tag
theorem erdos_494.variant.product :
    ∃ (A B : Finset ℂ), A.card = B.card ∧ erdos494_A_k_prod A 3 = erdos494_A_k_prod B 3 ∧
    A ≠ B := by
  sorry

end Erdos494
