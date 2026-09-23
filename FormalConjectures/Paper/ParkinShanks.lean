/-
Copyright 2026 The Formal Conjectures Authors.

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
module

public import FormalConjecturesUtil

/-!
# Parkin-Shanks Conjecture

The Parkin-Shanks conjecture states that the natural density of `n` where the partition number `p(n)`
is even (resp. odd) exists and equal to `1/2`.

*References:*
* [On the distribution of parity in the partition function](https://www.jstor.org/stable/2003251)
  T. R. Parkin and D. Shanks, Math. Comp. 21 (1967), 466–480
-/

@[expose] public section

namespace ParkinShanks

open Nat Set Filter Topology

/-- The natural density of `n` where the partition number `p(n)` is even (resp. odd) exists and equal to `1/2`-/
@[category research open, AMS 11]
theorem parkin_shanks :
    {n : ℕ | Even (partitionNumber n)}.HasDensity (1 / 2) ∧
    {n : ℕ | Odd (partitionNumber n)}.HasDensity (1 / 2) := by
  sorry

end ParkinShanks
