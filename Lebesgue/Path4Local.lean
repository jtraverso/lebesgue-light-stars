/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# The local inequality for light `4`-paths

Around a `5`-vertex `X` with neighbours of degrees `d₀, …, d₄` in rotation order, a neighbour of
degree `7`, `8` or at least `9` sends `1/3`, `1/2` or `1/3`, and every corner not on a triangle
gives `1/2`. If the corner between `nᵢ` and `nᵢ₊₁` is on a triangle, the paths `nₐ X nᵢ nᵢ₊₁` show
that `dₐ + dᵢ + dᵢ₊₁ ≥ 19` for the other three neighbours `nₐ` when there is no `4`-path of
weight at most `23`. Then `X` receives at least `1` (`one_le_recvP`, checked by `decide` with
degrees capped at nine).
-/

@[expose] public section

namespace LightPath4

/-- What a vertex of degree `k` sends to each `5`-neighbour. -/
noncomputable def cQ (k : ℕ) : ℚ :=
  if k = 7 then 1 / 3 else if k = 8 then 1 / 2 else if 9 ≤ k then 1 / 3 else 0

/-- `6 * cQ`. -/
def c6 (k : ℕ) : ℕ := if k = 7 then 2 else if k = 8 then 3 else if 9 ≤ k then 2 else 0

/-- `6 *` what a corner not on a triangle gives. -/
def f6 (t : Bool) : ℕ := if t then 0 else 3

/-- Degrees capped at nine. -/
def cap9 (a : ℕ) : ℕ := if 9 ≤ a then 9 else a

def okC (a b c : ℕ) : Bool := decide (19 ≤ a + b + c)

/-- The triangle conditions at the five corners. -/
def okP (d0 d1 d2 d3 d4 : ℕ) (t0 t1 t2 t3 t4 : Bool) : Bool :=
  (!t0 || (okC d2 d0 d1 && okC d3 d0 d1 && okC d4 d0 d1)) &&
  (!t1 || (okC d3 d1 d2 && okC d4 d1 d2 && okC d0 d1 d2)) &&
  (!t2 || (okC d4 d2 d3 && okC d0 d2 d3 && okC d1 d2 d3)) &&
  (!t3 || (okC d0 d3 d4 && okC d1 d3 d4 && okC d2 d3 d4)) &&
  (!t4 || (okC d1 d4 d0 && okC d2 d4 d0 && okC d3 d4 d0))

set_option maxRecDepth 100000 in
theorem p4_check : ∀ x0 x1 x2 x3 x4 : Fin 5, ∀ t0 t1 t2 t3 t4 : Bool,
    okP (x0.val + 5) (x1.val + 5) (x2.val + 5) (x3.val + 5) (x4.val + 5) t0 t1 t2 t3 t4 = true →
    6 ≤ c6 (x0.val + 5) + c6 (x1.val + 5) + c6 (x2.val + 5) + c6 (x3.val + 5) + c6 (x4.val + 5) +
      (f6 t0 + f6 t1 + f6 t2 + f6 t3 + f6 t4) := by
  decide

theorem cQ_eq {k : ℕ} (hk : 5 ≤ k) : cQ k = (c6 (cap9 k) : ℚ) / 6 := by
  unfold cQ c6 cap9
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

theorem c6_cap {k : ℕ} : c6 (cap9 k) = c6 k := by
  unfold c6 cap9
  split_ifs <;> omega

theorem okC_cap {a b c : ℕ} (ha : 5 ≤ a) (hb : 5 ≤ b) (hc : 5 ≤ c) (h : 19 ≤ a + b + c) :
    okC (cap9 a) (cap9 b) (cap9 c) = true := by
  unfold okC cap9
  simp only [decide_eq_true_eq]
  split_ifs <;> omega

theorem toFin9 (a : ℕ) (ha : 5 ≤ a) : ∃ x : Fin 5, x.val + 5 = cap9 a :=
  ⟨⟨cap9 a - 5, by unfold cap9; split_ifs <;> omega⟩, by unfold cap9; split_ifs <;> simp <;> omega⟩

noncomputable def fQ (t : Bool) : ℚ := if t then 0 else 1 / 2

theorem fQ_eq (t : Bool) : fQ t = (f6 t : ℚ) / 6 := by
  unfold fQ f6
  cases t <;> norm_num

/-- A `5`-vertex receives at least `1`. -/
theorem one_le_recvP (d0 d1 d2 d3 d4 : ℕ) (t0 t1 t2 t3 t4 : Bool) (h0 : 5 ≤ d0) (h1 : 5 ≤ d1)
    (h2 : 5 ≤ d2) (h3 : 5 ≤ d3) (h4 : 5 ≤ d4)
    (hok : okP (cap9 d0) (cap9 d1) (cap9 d2) (cap9 d3) (cap9 d4) t0 t1 t2 t3 t4 = true) :
    1 ≤ cQ d0 + cQ d1 + cQ d2 + cQ d3 + cQ d4 + (fQ t0 + fQ t1 + fQ t2 + fQ t3 + fQ t4) := by
  obtain ⟨x0, e0⟩ := toFin9 d0 h0
  obtain ⟨x1, e1⟩ := toFin9 d1 h1
  obtain ⟨x2, e2⟩ := toFin9 d2 h2
  obtain ⟨x3, e3⟩ := toFin9 d3 h3
  obtain ⟨x4, e4⟩ := toFin9 d4 h4
  have key := p4_check x0 x1 x2 x3 x4 t0 t1 t2 t3 t4 (by rw [e0, e1, e2, e3, e4]; exact hok)
  rw [e0, e1, e2, e3, e4, c6_cap, c6_cap, c6_cap, c6_cap, c6_cap] at key
  rw [cQ_eq h0, cQ_eq h1, cQ_eq h2, cQ_eq h3, cQ_eq h4, fQ_eq, fQ_eq, fQ_eq, fQ_eq, fQ_eq,
    c6_cap, c6_cap, c6_cap, c6_cap, c6_cap]
  have : ((6 : ℕ) : ℚ) ≤ ((c6 d0 + c6 d1 + c6 d2 + c6 d3 + c6 d4 +
      (f6 t0 + f6 t1 + f6 t2 + f6 t3 + f6 t4) : ℕ) : ℚ) := by
    exact_mod_cast key
  push_cast at this
  linarith

end LightPath4
