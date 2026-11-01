/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# The local inequalities for light stars

A vertex `A` of degree at least seven sends charge to each `5`-neighbour `X` through each of the
two faces on the sides of the edge `AX`: `aa (deg A) t`, where `t` is the degree of the third
vertex of that face if it is a triangle, and `6` otherwise (`1/6` from a `7`-vertex unless
`t = 5`; from a vertex of degree at least eight, `1/4`, or `1/8` if `t = 5`). Faces of length at
least four give `1/2` to each corner.

* `one_le_sum_cvX`: a `5`-vertex whose neighbourhood contains no light star receives at least
  `1`; the finite check (`recv_check`, degrees capped at eight) is done by `decide`;
* `sum_loss7_le`: a `7`-vertex loses at most `1` (`send7_check`, by `decide`).
-/

@[expose] public section

namespace Lebesgue

/-- What a vertex of degree `s` sends to a `5`-neighbour through a side whose third vertex has
degree `t` (`t = 6` for a face of length at least four). -/
noncomputable def aa (s t : ℕ) : ℚ :=
  if s = 7 then (if 6 ≤ t then 1 / 6 else 0) else if 8 ≤ s then (if 6 ≤ t then 1 / 4 else 1 / 8)
  else 0

/-- What a `5`-vertex receives at the corner between neighbours of degrees `a` and `b`, on a
triangle if `t`. -/
noncomputable def cvX (a b : ℕ) (t : Bool) : ℚ :=
  if t then aa a b + aa b a else 1 / 2 + aa a 6 + aa b 6

/-- Degrees capped at eight, shifted: `5 ↦ 0`, `6 ↦ 1`, `7 ↦ 2`, `8+ ↦ 3`. -/
def cl (a : ℕ) : ℕ := (if 8 ≤ a then 8 else a) - 5

/-- `24 * aa` on degree classes. -/
def aa24 (s t : ℕ) : ℕ :=
  if s = 2 then (if 1 ≤ t then 4 else 0) else if s = 3 then (if 1 ≤ t then 6 else 3) else 0

/-- `24 * cvX` on degree classes. -/
def cv24 (a b : ℕ) (t : Bool) : ℕ :=
  if t then aa24 a b + aa24 b a else 12 + aa24 a 1 + aa24 b 1

/-- The two light star patterns on degree classes: `(5, ≤ 6, ≤ 7)` and `(6, 6, 6)`. -/
def pat (x y z : ℕ) : Bool := (x == 0 && decide (y ≤ 1) && decide (z ≤ 2)) || (x == 1 && y == 1 && z == 1)

/-- Some three distinct neighbours form a light star pattern. -/
def starB (c : Fin 5 → ℕ) : Bool :=
  (List.finRange 5).any fun i => (List.finRange 5).any fun j => (List.finRange 5).any fun l =>
    i != j && i != l && j != l && pat (c i) (c j) (c l)

set_option maxRecDepth 100000 in
theorem recv_check : ∀ c0 c1 c2 c3 c4 : Fin 4, ∀ t0 t1 t2 t3 t4 : Bool,
    starB ![c0.val, c1.val, c2.val, c3.val, c4.val] = false →
    24 ≤ cv24 c0 c1 t0 + cv24 c1 c2 t1 + cv24 c2 c3 t2 + cv24 c3 c4 t3 + cv24 c4 c0 t4 := by
  decide

theorem cl_lt (a : ℕ) : cl a < 4 := by
  unfold cl
  split_ifs <;> omega

theorem aa_eq {s t : ℕ} (hs : 5 ≤ s) (ht : 5 ≤ t) : aa s t = (aa24 (cl s) (cl t) : ℚ) / 24 := by
  unfold aa aa24 cl
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

theorem cvX_eq {a b : ℕ} (t : Bool) (ha : 5 ≤ a) (hb : 5 ≤ b) :
    cvX a b t = (cv24 (cl a) (cl b) t : ℚ) / 24 := by
  have h6 : cl 6 = 1 := rfl
  unfold cvX cv24
  cases t
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [aa_eq ha (by norm_num), aa_eq hb (by norm_num), h6]
    push_cast
    ring
  · simp only [↓reduceIte]
    rw [aa_eq ha hb, aa_eq hb ha]
    push_cast
    ring

theorem pat_cl {x y z : ℕ} (hx : 5 ≤ x) (hy : 5 ≤ y) (hz : 5 ≤ z)
    (h : pat (cl x) (cl y) (cl z) = true) :
    (x = 5 ∧ y ≤ 6 ∧ z ≤ 7) ∨ (x = 6 ∧ y = 6 ∧ z = 6) := by
  have c0 : ∀ a, 5 ≤ a → (cl a = 0 ↔ a = 5) := fun a ha => by unfold cl; split_ifs <;> constructor <;> intro <;> first | omega | contradiction | simp_all
  have c1 : ∀ a, 5 ≤ a → (cl a = 1 ↔ a = 6) := fun a ha => by unfold cl; split_ifs <;> constructor <;> intro <;> first | omega | contradiction | simp_all
  have c1' : ∀ a, 5 ≤ a → (cl a ≤ 1 ↔ a ≤ 6) := fun a ha => by unfold cl; split_ifs <;> constructor <;> intro <;> first | omega | contradiction | simp_all
  have c2' : ∀ a, 5 ≤ a → (cl a ≤ 2 ↔ a ≤ 7) := fun a ha => by unfold cl; split_ifs <;> constructor <;> intro <;> first | omega | contradiction | simp_all
  simp only [pat, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    c0 x hx, c1 x hx, c1 y hy, c1 z hz, c1' y hy, c2' z hz] at h
  rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
  · exact Or.inl ⟨h1, h2, h3⟩
  · exact Or.inr ⟨h1, h2, h3⟩

theorem exists_of_starB {c : Fin 5 → ℕ} (h : starB c = true) :
    ∃ i j l : Fin 5, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧ pat (c i) (c j) (c l) = true := by
  simp only [starB, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨i, j, l, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩ := h
  exact ⟨i, j, l, h1, h2, h3, h4⟩

/-- A `5`-vertex receives at least `1`. -/
theorem one_le_sum_cvX (d0 d1 d2 d3 d4 : ℕ) (t0 t1 t2 t3 t4 : Bool) (h0 : 5 ≤ d0) (h1 : 5 ≤ d1)
    (h2 : 5 ≤ d2) (h3 : 5 ≤ d3) (h4 : 5 ≤ d4)
    (hs : starB ![cl d0, cl d1, cl d2, cl d3, cl d4] = false) :
    1 ≤ cvX d0 d1 t0 + cvX d1 d2 t1 + cvX d2 d3 t2 + cvX d3 d4 t3 + cvX d4 d0 t4 := by
  have key := recv_check ⟨cl d0, cl_lt _⟩ ⟨cl d1, cl_lt _⟩ ⟨cl d2, cl_lt _⟩ ⟨cl d3, cl_lt _⟩
    ⟨cl d4, cl_lt _⟩ t0 t1 t2 t3 t4 hs
  rw [cvX_eq t0 h0 h1, cvX_eq t1 h1 h2, cvX_eq t2 h2 h3, cvX_eq t3 h3 h4, cvX_eq t4 h4 h0]
  have : ((24 : ℕ) : ℚ) ≤ ((cv24 (cl d0) (cl d1) t0 + cv24 (cl d1) (cl d2) t1 +
      cv24 (cl d2) (cl d3) t2 + cv24 (cl d3) (cl d4) t3 + cv24 (cl d4) (cl d0) t4 : ℕ) : ℚ) := by
    exact_mod_cast key
  push_cast at this
  linarith

/-! ### `7`-vertices -/

/-- `6 *` what a `7`-vertex sends through the corner between neighbours `b`, `b'` (true for a
`5`-vertex), on a triangle if `t`. -/
def p6 (b b' t : Bool) : ℕ :=
  (if b && (!t || !b') then 1 else 0) + (if b' && (!t || !b) then 1 else 0)

/-- `6 *` what the corner receives from a face of length at least four. -/
def q3 (t : Bool) : ℕ := if t then 0 else 3

set_option maxRecDepth 100000 in
theorem send7_check : ∀ b0 b1 b2 b3 b4 b5 b6 t0 t1 t2 t3 t4 t5 t6 : Bool,
    p6 b0 b1 t0 + p6 b1 b2 t1 + p6 b2 b3 t2 + p6 b3 b4 t3 + p6 b4 b5 t4 + p6 b5 b6 t5 +
      p6 b6 b0 t6 ≤
    6 + (q3 t0 + q3 t1 + q3 t2 + q3 t3 + q3 t4 + q3 t5 + q3 t6) := by
  decide

/-- What a `7`-vertex loses at the corner between neighbours of degrees `h`, `h'`. -/
noncomputable def loss7 (h h' : ℕ) (t : Bool) : ℚ :=
  (if h = 5 then (if t then aa 7 h' else aa 7 6) else 0) +
    (if h' = 5 then (if t then aa 7 h else aa 7 6) else 0) - (if t then 0 else 1 / 2)

theorem loss7_eq {h h' : ℕ} (t : Bool) (hh : 5 ≤ h) (hh' : 5 ≤ h') :
    loss7 h h' t = ((p6 (decide (h = 5)) (decide (h' = 5)) t : ℚ) - q3 t) / 6 := by
  unfold loss7 p6 q3 aa
  cases t <;> by_cases e1 : h = 5 <;> by_cases e2 : h' = 5 <;>
    simp [e1, e2, show 6 ≤ h ↔ ¬ h = 5 by omega, show 6 ≤ h' ↔ ¬ h' = 5 by omega] <;> norm_num

theorem sum_loss7_le (d0 d1 d2 d3 d4 d5 d6 : ℕ) (t0 t1 t2 t3 t4 t5 t6 : Bool) (h0 : 5 ≤ d0)
    (h1 : 5 ≤ d1) (h2 : 5 ≤ d2) (h3 : 5 ≤ d3) (h4 : 5 ≤ d4) (h5 : 5 ≤ d5) (h6 : 5 ≤ d6) :
    loss7 d0 d1 t0 + loss7 d1 d2 t1 + loss7 d2 d3 t2 + loss7 d3 d4 t3 + loss7 d4 d5 t4 +
      loss7 d5 d6 t5 + loss7 d6 d0 t6 ≤ 1 := by
  rw [loss7_eq t0 h0 h1, loss7_eq t1 h1 h2, loss7_eq t2 h2 h3, loss7_eq t3 h3 h4,
    loss7_eq t4 h4 h5, loss7_eq t5 h5 h6, loss7_eq t6 h6 h0]
  have key := send7_check (decide (d0 = 5)) (decide (d1 = 5)) (decide (d2 = 5)) (decide (d3 = 5))
    (decide (d4 = 5)) (decide (d5 = 5)) (decide (d6 = 5)) t0 t1 t2 t3 t4 t5 t6
  have hk : ((p6 (decide (d0 = 5)) (decide (d1 = 5)) t0 + p6 (decide (d1 = 5)) (decide (d2 = 5)) t1 +
      p6 (decide (d2 = 5)) (decide (d3 = 5)) t2 + p6 (decide (d3 = 5)) (decide (d4 = 5)) t3 +
      p6 (decide (d4 = 5)) (decide (d5 = 5)) t4 + p6 (decide (d5 = 5)) (decide (d6 = 5)) t5 +
      p6 (decide (d6 = 5)) (decide (d0 = 5)) t6 : ℕ) : ℚ) ≤
      ((6 + (q3 t0 + q3 t1 + q3 t2 + q3 t3 + q3 t4 + q3 t5 + q3 t6) : ℕ) : ℚ) := by
    exact_mod_cast key
  push_cast at hk
  linarith

end Lebesgue
