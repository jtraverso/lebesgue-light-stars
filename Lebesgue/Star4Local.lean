/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# The local inequalities for light `4`-stars

Around a `5`-vertex `X` with neighbours `n₀, …, n₄` in rotation order, every vertex of degree at
least twelve sends `1/2`, and a neighbour `nᵢ` of degree eleven sends `1/2` unless both its
flanking neighbours `nᵢ₋₁`, `nᵢ₊₁` are `5`-vertices and either `nᵢ₊₂`, `nᵢ₊₃` both have degree at
least eleven or the corner between `nᵢ₊₁` and `nᵢ₊₂` is not on a triangle; every corner not on a
triangle gives `1/2`. If at least two neighbours have degree at least eleven, `X` receives at
least `1` (`one_le_recv4`, checked by `decide` on degree classes). The parity of an `11`-cycle is
`parity_check`.
-/

@[expose] public section

namespace LightStar4

/-- Degree classes: `≤ 5 ↦ 0`, `6..10 ↦ 1`, `11 ↦ 2`, `≥ 12 ↦ 3`. -/
def cl4 (a : ℕ) : ℕ := if a ≤ 5 then 0 else if a ≤ 10 then 1 else if a = 11 then 2 else 3

/-- `2 *` what a neighbour of class `c` sends, given the classes of the next neighbours. -/
def send2 (cm c cp cpp cppp : ℕ) (tp : Bool) : ℕ :=
  if c = 3 then 1
  else if c = 2 then (if cm = 0 && cp = 0 && ((2 ≤ cpp && 2 ≤ cppp) || !tp) then 0 else 1)
  else 0

/-- `2 *` what a corner not on a triangle gives. -/
def face2 (t : Bool) : ℕ := if t then 0 else 1

/-- Four of the five neighbours have degree at most ten. -/
def four_small (c0 c1 c2 c3 c4 : ℕ) : Bool :=
  (c1 ≤ 1 && c2 ≤ 1 && c3 ≤ 1 && c4 ≤ 1) || (c0 ≤ 1 && c2 ≤ 1 && c3 ≤ 1 && c4 ≤ 1) ||
    (c0 ≤ 1 && c1 ≤ 1 && c3 ≤ 1 && c4 ≤ 1) || (c0 ≤ 1 && c1 ≤ 1 && c2 ≤ 1 && c4 ≤ 1) ||
    (c0 ≤ 1 && c1 ≤ 1 && c2 ≤ 1 && c3 ≤ 1)

set_option maxRecDepth 100000 in
theorem recv4_check : ∀ c0 c1 c2 c3 c4 : Fin 4, ∀ t0 t1 t2 t3 t4 : Bool,
    four_small c0 c1 c2 c3 c4 = false →
    2 ≤ face2 t0 + face2 t1 + face2 t2 + face2 t3 + face2 t4 +
      send2 c4 c0 c1 c2 c3 t1 + send2 c0 c1 c2 c3 c4 t2 + send2 c1 c2 c3 c4 c0 t3 +
      send2 c2 c3 c4 c0 c1 t4 + send2 c3 c4 c0 c1 c2 t0 := by
  decide

set_option maxRecDepth 100000 in
theorem parity_check : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    (b0 != b1 && b1 != b2 && b2 != b3 && b3 != b4 && b4 != b5 && b5 != b6 && b6 != b7 &&
      b7 != b8 && b8 != b9 && b9 != b10 && b10 != b0) = false := by
  decide

/-- What a neighbour of degree `a` sends, given the degrees `am`, `ap`, `app`, `appp` of the
previous and the next three neighbours and whether the corner after the next neighbour is on a
triangle. -/
noncomputable def sendQ (am a ap app appp : ℕ) (tp : Bool) : ℚ :=
  if 12 ≤ a then 1 / 2
  else if a = 11 then
    (if am = 5 ∧ ap = 5 ∧ ((11 ≤ app ∧ 11 ≤ appp) ∨ tp = false) then 0 else 1 / 2)
  else 0

noncomputable def faceQ (t : Bool) : ℚ := if t then 0 else 1 / 2

theorem cl4_lt (a : ℕ) : cl4 a < 4 := by
  unfold cl4
  split_ifs <;> omega

theorem cl4_iff (a : ℕ) : (cl4 a = 3 ↔ 12 ≤ a) ∧ (cl4 a = 2 ↔ a = 11) ∧ (2 ≤ cl4 a ↔ 11 ≤ a) ∧
    (5 ≤ a → (cl4 a = 0 ↔ a = 5)) := by
  unfold cl4
  refine ⟨?_, ?_, ?_, fun h => ?_⟩ <;> split_ifs <;> constructor <;> intro <;>
    first | omega | contradiction | simp_all

theorem sendQ_eq {am a ap app appp : ℕ} (tp : Bool) (h1 : 5 ≤ am) (h2 : 5 ≤ a) (h3 : 5 ≤ ap)
    (h4 : 5 ≤ app) (h5 : 5 ≤ appp) :
    sendQ am a ap app appp tp = (send2 (cl4 am) (cl4 a) (cl4 ap) (cl4 app) (cl4 appp) tp : ℚ) / 2 := by
  obtain ⟨e3, e2, -, -⟩ := cl4_iff a
  have zam := (cl4_iff am).2.2.2 h1
  have zap := (cl4_iff ap).2.2.2 h3
  have bpp := (cl4_iff app).2.2.1
  have bppp := (cl4_iff appp).2.2.1
  unfold sendQ send2
  by_cases h12 : 12 ≤ a
  · rw [if_pos h12, if_pos (e3.2 h12)]
    norm_num
  · rw [if_neg h12, if_neg (mt e3.1 h12)]
    by_cases h11 : a = 11
    · rw [if_pos h11, if_pos (e2.2 h11)]
      cases tp <;> by_cases q1 : am = 5 <;> by_cases q2 : ap = 5 <;> by_cases q3 : 11 ≤ app <;>
        by_cases q4 : 11 ≤ appp <;> simp [q1, q2, q3, q4, zam, zap, bpp, bppp, show cl4 5 = 0 from rfl]
    · rw [if_neg h11, if_neg (mt e2.1 h11)]
      norm_num

theorem faceQ_eq (t : Bool) : faceQ t = (face2 t : ℚ) / 2 := by
  unfold faceQ face2
  cases t <;> norm_num

theorem four_small_cl4 {d0 d1 d2 d3 d4 : ℕ} (h : four_small (cl4 d0) (cl4 d1) (cl4 d2) (cl4 d3)
    (cl4 d4) = true) :
    (d1 ≤ 10 ∧ d2 ≤ 10 ∧ d3 ≤ 10 ∧ d4 ≤ 10) ∨ (d0 ≤ 10 ∧ d2 ≤ 10 ∧ d3 ≤ 10 ∧ d4 ≤ 10) ∨
      (d0 ≤ 10 ∧ d1 ≤ 10 ∧ d3 ≤ 10 ∧ d4 ≤ 10) ∨ (d0 ≤ 10 ∧ d1 ≤ 10 ∧ d2 ≤ 10 ∧ d4 ≤ 10) ∨
      (d0 ≤ 10 ∧ d1 ≤ 10 ∧ d2 ≤ 10 ∧ d3 ≤ 10) := by
  have c : ∀ a, (cl4 a ≤ 1 ↔ a ≤ 10) := fun a => by
    unfold cl4; split_ifs <;> constructor <;> intro <;> first | omega | contradiction | simp_all
  simp only [four_small, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, c] at h
  tauto

/-- A `5`-vertex with at least two neighbours of degree at least eleven receives at least `1`. -/
theorem one_le_recv4 (d0 d1 d2 d3 d4 : ℕ) (t0 t1 t2 t3 t4 : Bool) (h0 : 5 ≤ d0) (h1 : 5 ≤ d1)
    (h2 : 5 ≤ d2) (h3 : 5 ≤ d3) (h4 : 5 ≤ d4)
    (hs : four_small (cl4 d0) (cl4 d1) (cl4 d2) (cl4 d3) (cl4 d4) = false) :
    1 ≤ faceQ t0 + faceQ t1 + faceQ t2 + faceQ t3 + faceQ t4 +
      sendQ d4 d0 d1 d2 d3 t1 + sendQ d0 d1 d2 d3 d4 t2 + sendQ d1 d2 d3 d4 d0 t3 +
      sendQ d2 d3 d4 d0 d1 t4 + sendQ d3 d4 d0 d1 d2 t0 := by
  have key := recv4_check ⟨cl4 d0, cl4_lt _⟩ ⟨cl4 d1, cl4_lt _⟩ ⟨cl4 d2, cl4_lt _⟩
    ⟨cl4 d3, cl4_lt _⟩ ⟨cl4 d4, cl4_lt _⟩ t0 t1 t2 t3 t4 hs
  rw [faceQ_eq, faceQ_eq, faceQ_eq, faceQ_eq, faceQ_eq, sendQ_eq t1 h4 h0 h1 h2 h3,
    sendQ_eq t2 h0 h1 h2 h3 h4, sendQ_eq t3 h1 h2 h3 h4 h0, sendQ_eq t4 h2 h3 h4 h0 h1,
    sendQ_eq t0 h3 h4 h0 h1 h2]
  have : ((2 : ℕ) : ℚ) ≤ ((face2 t0 + face2 t1 + face2 t2 + face2 t3 + face2 t4 +
      send2 (cl4 d4) (cl4 d0) (cl4 d1) (cl4 d2) (cl4 d3) t1 +
      send2 (cl4 d0) (cl4 d1) (cl4 d2) (cl4 d3) (cl4 d4) t2 +
      send2 (cl4 d1) (cl4 d2) (cl4 d3) (cl4 d4) (cl4 d0) t3 +
      send2 (cl4 d2) (cl4 d3) (cl4 d4) (cl4 d0) (cl4 d1) t4 +
      send2 (cl4 d3) (cl4 d4) (cl4 d0) (cl4 d1) (cl4 d2) t0 : ℕ) : ℚ) := by
    exact_mod_cast key
  push_cast at this
  linarith

end LightStar4
