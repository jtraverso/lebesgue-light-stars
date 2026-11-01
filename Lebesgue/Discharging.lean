/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Borodin.Discharging
public import Lebesgue.Local

/-!
# Light stars in plane maps of minimum degree five

Let `M` be a plane map of a finite simple graph of minimum degree at least five with no light
star (`NoStar`: no `5`-vertex with three distinct neighbours of degrees `(5, ≤ 6, ≤ 7)` or
`(6, 6, 6)`). Start from the charges of `Kotzig.sum_charge` (total `-12 K < 0`) and move charge:

* every face of length at least four gives `1/2` to each of its corners (`Borodin.bigF`);
* a vertex `A` of degree at least seven sends to each `5`-neighbour `X`, through each of the two
  faces on the sides of `AX`, the amount `aa (deg A) t` (`sL`, `sR`, `gg`).

This is the discharging of Jendrol' and Madaras (Rules 1 and 2: strong, semi-strong and weak
neighbours), split over the two sides of an edge, with face charges in place of triangulating.
Faces stay nonnegative; around a vertex the charge is a sum over its corners, computed from the
cyclic enumeration of its darts (`enum`): `5`-vertices receive at least `1`
(`Lebesgue.one_le_sum_cvX`), `7`-vertices lose at most `1` (`Lebesgue.sum_loss7_le`), and
vertices of degree `k ≥ 8` lose at most `k / 4`.
-/

@[expose] public section

namespace Lebesgue

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Kotzig Borodin

theorem sum_shift (g : ℕ → ℚ) (k : ℕ) (h : g k = g 0) :
    ∑ n ∈ Finset.range k, g (n + 1) = ∑ n ∈ Finset.range k, g n := by
  have h1 := Finset.sum_range_succ' g k
  have h2 := Finset.sum_range_succ g k
  rw [h] at h2
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- No light star: no `5`-vertex has three distinct neighbours of degrees `(5, ≤ 6, ≤ 7)` or
`(6, 6, 6)`. -/
def NoStar : Prop :=
  ∀ x a₁ a₂ a₃ : V, G.Adj x a₁ → G.Adj x a₂ → G.Adj x a₃ → a₁ ≠ a₂ → a₁ ≠ a₃ → a₂ ≠ a₃ →
    G.degree x = 5 → ¬ ((G.degree a₁ = 5 ∧ G.degree a₂ ≤ 6 ∧ G.degree a₃ ≤ 7) ∨
      (G.degree a₁ = 6 ∧ G.degree a₂ = 6 ∧ G.degree a₃ = 6))

variable (M : PlaneMap G)

/-- What the tail of `e` sends to its head through the face of `e.symm`. -/
noncomputable def sR (e : G.Dart) : ℚ :=
  if fLen M e.symm = 3 then aa (G.degree e.fst) (G.degree (M.rot e).snd)
  else aa (G.degree e.fst) 6

/-- What the tail of `e` sends to its head through the face of `e`. -/
noncomputable def sL (e : G.Dart) : ℚ :=
  if fLen M e = 3 then aa (G.degree e.fst) (G.degree (M.facePerm e).snd)
  else aa (G.degree e.fst) 6

/-- What the tail of `e` sends to its head, if the head is a `5`-vertex. -/
noncomputable def gg (e : G.Dart) : ℚ := if G.degree e.snd = 5 then sL M e + sR M e else 0

/-- What a vertex of degree `k` loses at the corner between neighbours of degrees `h`, `h'`. -/
noncomputable def lossG (k h h' : ℕ) (t : Bool) : ℚ :=
  (if h = 5 then (if t then aa k h' else aa k 6) else 0) +
    (if h' = 5 then (if t then aa k h else aa k 6) else 0) - (if t then 0 else 1 / 2)

theorem lossG_le {k h h' : ℕ} (t : Bool) (hk : 8 ≤ k) (hh : 5 ≤ h) (hh' : 5 ≤ h') :
    lossG k h h' t ≤ 1 / 4 := by
  unfold lossG aa
  have k7 : k ≠ 7 := by omega
  cases t <;> by_cases e1 : h = 5 <;> by_cases e2 : h' = 5 <;>
    simp [e1, e2, k7, hk, show 6 ≤ h ↔ ¬ h = 5 by omega, show 6 ≤ h' ↔ ¬ h' = 5 by omega] <;>
    norm_num

/-! ### Faces -/

theorem fLen_facePerm (x : G.Dart) : fLen M (M.facePerm x) = fLen M x := by
  unfold fLen
  rw [cls_eq (s := SameCycle.setoid M.facePerm)
    (show SameCycle M.facePerm x (M.facePerm x) from ⟨1, by simp⟩)]

theorem third_tri {x : G.Dart} (h : fLen M x = 3) :
    (M.facePerm (M.facePerm x)).snd = x.fst := by
  have h3 : M.facePerm (M.facePerm (M.facePerm x)) = x := by
    have := pow_card_cls M.facePerm x
    unfold fLen at h
    rw [h] at this
    simpa [pow_three] using this
  have := fst_facePerm M (M.facePerm (M.facePerm x))
  rw [h3] at this
  exact this.symm

theorem rot_eq (e : G.Dart) : M.rot e = M.facePerm e.symm := by
  rw [M.facePerm_apply, SimpleGraph.Dart.symm_symm]

theorem face_orbit_nonneg (hδ : ∀ v, 5 ≤ G.degree v) (x : G.Dart) :
    0 ≤ ∑ y ∈ cls (SameCycle.setoid M.facePerm) x, ((2 - 6 / (fLen M y : ℚ)) - bigF M y) := by
  have hδ2 : ∀ v, 2 ≤ G.degree v := fun v => by have := hδ v; omega
  set O := cls (SameCycle.setoid M.facePerm) x with hO
  have hlen : ∀ y ∈ O, fLen M y = O.card := fun y hy => by
    unfold fLen
    rw [← cls_eq (mem_cls.1 hy)]
  have hℓ3 : 3 ≤ O.card := three_le_fLen M hδ2 x
  have hpos : (0 : ℚ) < O.card := by exact_mod_cast (by omega : 0 < O.card)
  rcases Nat.lt_or_ge 3 O.card with h4 | h3
  · have hval : ∀ y ∈ O, ((2 - 6 / (fLen M y : ℚ)) - bigF M y) = 2 - 6 / (O.card : ℚ) - 1 / 2 := by
      intro y hy
      unfold bigF
      rw [hlen y hy, if_pos (by omega)]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    have h4' : (4 : ℚ) ≤ O.card := by exact_mod_cast h4
    have : (O.card : ℚ) * (2 - 6 / O.card - 1 / 2) = 3 / 2 * O.card - 6 := by
      field_simp
      ring
    rw [this]
    linarith
  · have hc3 : O.card = 3 := le_antisymm h3 hℓ3
    refine Finset.sum_nonneg (fun y hy => ?_)
    unfold bigF
    rw [hlen y hy, hc3, if_neg (by omega)]
    norm_num

/-! ### The discharging preserves the total -/

theorem sum_split :
    ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + (2 - 6 / (fLen M d : ℚ))) =
      ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + gg M d.symm - gg M d + bigF M d.symm) +
      ∑ x : G.Dart, ((2 - 6 / (fLen M x : ℚ)) - bigF M x) := by
  have h1 : ∑ d : G.Dart, gg M d.symm = ∑ d : G.Dart, gg M d :=
    Equiv.sum_comp (dartSymm G) (gg M)
  have h2 : ∑ d : G.Dart, bigF M d.symm = ∑ d : G.Dart, bigF M d :=
    Equiv.sum_comp (dartSymm G) (bigF M)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2]
  ring

/-! ### The darts around a vertex -/

theorem enum (v : V) (hk : 0 < G.degree v) :
    ∃ e : ℕ → G.Dart, (∀ n, e (n + 1) = M.rot (e n)) ∧ e (G.degree v) = e 0 ∧
      (∀ n, (e n).fst = v) ∧ Set.InjOn e (Finset.range (G.degree v) : Set ℕ) ∧
      (Finset.range (G.degree v)).image e = Finset.univ.filter (fun d : G.Dart => d.fst = v) := by
  set F := Finset.univ.filter (fun d : G.Dart => d.fst = v) with hF
  have hFk : F.card = G.degree v := G.dart_fst_fiber_card_eq_degree v
  obtain ⟨e0, he0⟩ : ∃ e0, e0 ∈ F := Finset.card_pos.1 (by omega)
  have he0v : e0.fst = v := (Finset.mem_filter.1 he0).2
  have hcard : (cls (SameCycle.setoid M.rot) e0).card = G.degree v := by
    rw [card_cls_rot M e0, he0v]
  refine ⟨fun n => (M.rot ^ n) e0, fun n => by simp only [pow_succ', Perm.mul_apply], ?_,
    fun n => (fst_rot_pow M e0 n).trans he0v, ?_, ?_⟩
  · have := pow_card_cls M.rot e0
    rw [hcard] at this
    simpa using this
  · intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    have key : ∀ a b, a < b → b < G.degree v → (M.rot ^ a) e0 = (M.rot ^ b) e0 → False := by
      intro a b hab hb heq
      have hp : (M.rot ^ (b - a)) e0 = e0 := by
        apply (M.rot ^ a).injective
        rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
        exact heq.symm
      have := card_cls_le_of_pow M.rot e0 (by omega) hp
      omega
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i j h hj hij
    · exact key j i h hi hij.symm
  · refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro z hz
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hz
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (fst_rot_pow M e0 n).trans he0v⟩
    · rw [Finset.card_image_of_injOn (by
        intro i hi j hj hij
        simp only [Finset.coe_range, Set.mem_Iio] at hi hj
        by_contra hne
        have key : ∀ a b, a < b → b < G.degree v → (M.rot ^ a) e0 = (M.rot ^ b) e0 → False := by
          intro a b hab hb heq
          have hp : (M.rot ^ (b - a)) e0 = e0 := by
            apply (M.rot ^ a).injective
            rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
            exact heq.symm
          have := card_cls_le_of_pow M.rot e0 (by omega) hp
          omega
        rcases lt_or_gt_of_ne hne with h | h
        · exact key i j h hj hij
        · exact key j i h hi hij.symm), hFk]
      simp

/-! ### Vertices -/

theorem vertex_nonneg (hδ : ∀ v, 5 ≤ G.degree v) (hns : NoStar (G := G)) (v : V) :
    0 ≤ ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v),
      ((1 - 6 / (G.degree d.fst : ℚ)) + gg M d.symm - gg M d + bigF M d.symm) := by
  have hδ2 : ∀ v, 2 ≤ G.degree v := fun v => by have := hδ v; omega
  set F := Finset.univ.filter (fun d : G.Dart => d.fst = v) with hF
  have hFk : F.card = G.degree v := G.dart_fst_fiber_card_eq_degree v
  have hk5 : 5 ≤ G.degree v := hδ v
  have hkpos : (0 : ℚ) < G.degree v := by exact_mod_cast (by omega : 0 < G.degree v)
  have hmemF : ∀ d ∈ F, d.fst = v := fun d hd => (Finset.mem_filter.1 hd).2
  have hbig0 : ∀ d : G.Dart, 0 ≤ bigF M d := fun d => by unfold bigF; split_ifs <;> norm_num
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hA : ∑ d ∈ F, (1 - 6 / (G.degree d.fst : ℚ)) = G.degree v - 6 := by
    rw [Finset.sum_congr rfl (fun d hd => show (1 - 6 / (G.degree d.fst : ℚ)) =
      1 - 6 / (G.degree v : ℚ) by rw [hmemF d hd]), Finset.sum_const, hFk, nsmul_eq_mul]
    field_simp
  rw [hA]
  have hB0 : 0 ≤ ∑ d ∈ F, bigF M d.symm := Finset.sum_nonneg (fun d _ => hbig0 _)
  have hsend0 : G.degree v ≤ 6 → ∑ d ∈ F, gg M d = 0 := fun h =>
    Finset.sum_eq_zero (fun d hd => by
      unfold gg sL sR aa
      rw [hmemF d hd]
      simp [show G.degree v ≠ 7 by omega, show ¬ 8 ≤ G.degree v by omega])
  have hrecv0 : G.degree v ≠ 5 → ∑ d ∈ F, gg M d.symm = 0 := fun h =>
    Finset.sum_eq_zero (fun d hd => by
      unfold gg
      rw [show d.symm.snd = v from hmemF d hd, if_neg h])
  obtain ⟨e, hsucc, hper, hfst, hinj, himg⟩ := enum M v (by omega)
  have hsumF : ∀ f : G.Dart → ℚ, ∑ d ∈ F, f d = ∑ n ∈ Finset.range (G.degree v), f (e n) :=
    fun f => by rw [show F = _ from himg.symm, Finset.sum_image hinj]
  -- the corner between `e n` and `e (n + 1)`
  have hlenS : ∀ n, fLen M (e (n + 1)) = fLen M (e n).symm := fun n => by
    rw [hsucc, rot_eq, fLen_facePerm]
  have hthird : ∀ n, fLen M (e n).symm = 3 → (M.facePerm (e (n + 1))).snd = (e n).snd :=
    fun n h => by
      rw [hsucc, rot_eq]
      exact third_tri M h
  have h3 : ∀ n, 3 ≤ fLen M (e n).symm := fun n => three_le_fLen M hδ2 _
  rcases (show G.degree v = 5 ∨ G.degree v = 6 ∨ 7 ≤ G.degree v by omega) with h5 | h6 | h7
  · -- a `5`-vertex receives at least `1`
    rw [hsend0 (by omega)]
    have hcorner : ∀ n, sL M (e n).symm + sR M (e (n + 1)).symm + bigF M (e n).symm =
        cvX (G.degree (e n).snd) (G.degree (e (n + 1)).snd) (decide (fLen M (e n).symm = 3)) := by
      intro n
      have hφ : M.facePerm (e n).symm = e (n + 1) := by rw [hsucc, rot_eq]
      have hr : M.rot (e (n + 1)).symm = M.facePerm (e (n + 1)) := by
        rw [M.facePerm_apply]
      unfold sL sR bigF cvX
      rw [SimpleGraph.Dart.symm_symm, hlenS, hr, hφ]
      change (if fLen M (e n).symm = 3 then aa (G.degree (e n).snd) (G.degree (e (n + 1)).snd)
          else aa (G.degree (e n).snd) 6) +
        (if fLen M (e n).symm = 3 then aa (G.degree (e (n + 1)).snd)
          (G.degree (M.facePerm (e (n + 1))).snd) else aa (G.degree (e (n + 1)).snd) 6) +
        (if 4 ≤ fLen M (e n).symm then 1 / 2 else 0) = _
      by_cases ht : fLen M (e n).symm = 3
      · rw [if_pos ht, if_pos ht, if_neg (by omega), hthird n ht]
        simp [ht]
      · rw [if_neg ht, if_neg ht, if_pos (by have := h3 n; omega)]
        simp [ht]
        try ring
    have hrecv : ∑ d ∈ F, gg M d.symm + ∑ d ∈ F, bigF M d.symm =
        ∑ n ∈ Finset.range 5, cvX (G.degree (e n).snd) (G.degree (e (n + 1)).snd)
          (decide (fLen M (e n).symm = 3)) := by
      have hg : ∀ n, gg M (e n).symm = sL M (e n).symm + sR M (e n).symm := fun n => by
        unfold gg
        rw [if_pos (by rw [show (e n).symm.snd = v from hfst n]; exact h5)]
      rw [hsumF, hsumF, h5]
      simp only [hg, Finset.sum_add_distrib]
      rw [← sum_shift (fun n => sR M (e n).symm) 5 (by rw [← h5, hper])]
      rw [← Finset.sum_congr rfl (fun n _ => hcorner n), Finset.sum_add_distrib,
        Finset.sum_add_distrib]
    -- no light star around `v`
    have hstar : starB ![cl (G.degree (e 0).snd), cl (G.degree (e 1).snd),
        cl (G.degree (e 2).snd), cl (G.degree (e 3).snd), cl (G.degree (e 4).snd)] = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      obtain ⟨i, j, l, hij, hil, hjl, hp⟩ := exists_of_starB hc
      have hvec : ∀ i : Fin 5, (![cl (G.degree (e 0).snd), cl (G.degree (e 1).snd),
          cl (G.degree (e 2).snd), cl (G.degree (e 3).snd), cl (G.degree (e 4).snd)] : Fin 5 → ℕ) i =
          cl (G.degree (e i.val).snd) := by
        intro i
        fin_cases i <;> rfl
      rw [hvec, hvec, hvec] at hp
      have hpat := pat_cl (hδ _) (hδ _) (hδ _) hp
      have hadj : ∀ i : Fin 5, G.Adj v (e i.val).snd := fun i => by
        have := (e i.val).adj
        rwa [hfst] at this
      have hne : ∀ i j : Fin 5, i ≠ j → (e i.val).snd ≠ (e j.val).snd := by
        intro i j hij hs
        apply hij
        have hd : e i.val = e j.val := by
          rw [SimpleGraph.Dart.ext_iff]
          exact Prod.ext ((hfst _).trans (hfst _).symm) hs
        have := hinj (by simp [h5]) (by simp [h5]) hd
        exact Fin.ext this
      exact hns v _ _ _ (hadj i) (hadj j) (hadj l) (hne i j hij) (hne i l hil) (hne j l hjl) h5 hpat
    have hlocal := one_le_sum_cvX _ _ _ _ _ (decide (fLen M (e 0).symm = 3))
      (decide (fLen M (e 1).symm = 3)) (decide (fLen M (e 2).symm = 3))
      (decide (fLen M (e 3).symm = 3)) (decide (fLen M (e 4).symm = 3))
      (hδ _) (hδ _) (hδ _) (hδ _) (hδ _) hstar
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd] at hrecv
    have he5 : e 5 = e 0 := by rw [← h5]; exact hper
    rw [he5] at hrecv
    rw [h5] at ⊢
    push_cast
    linarith
  · -- a `6`-vertex
    rw [hsend0 (by omega), hrecv0 (by omega), h6]
    push_cast
    linarith
  · -- a vertex of degree at least seven
    rw [hrecv0 (by omega)]
    have hcorner : ∀ n, (if G.degree (e n).snd = 5 then sR M (e n) else 0) +
        (if G.degree (e (n + 1)).snd = 5 then sL M (e (n + 1)) else 0) - bigF M (e n).symm =
        lossG (G.degree v) (G.degree (e n).snd) (G.degree (e (n + 1)).snd)
          (decide (fLen M (e n).symm = 3)) := by
      intro n
      unfold sR sL bigF lossG
      rw [hlenS, hfst, hfst, ← hsucc]
      by_cases ht : fLen M (e n).symm = 3
      · simp [ht]
        rw [show (M.facePerm (e (n + 1))).toProd.2 = (e n).toProd.2 from hthird n ht]
      · have h4 : 4 ≤ fLen M (e n).symm := by have := h3 n; omega
        simp [ht, h4]
    have hsend : ∑ d ∈ F, gg M d - ∑ d ∈ F, bigF M d.symm =
        ∑ n ∈ Finset.range (G.degree v), lossG (G.degree v) (G.degree (e n).snd)
          (G.degree (e (n + 1)).snd) (decide (fLen M (e n).symm = 3)) := by
      have hg : ∀ n, gg M (e n) = (if G.degree (e n).snd = 5 then sR M (e n) else 0) +
          (if G.degree (e n).snd = 5 then sL M (e n) else 0) := fun n => by
        unfold gg
        split_ifs <;> ring
      rw [hsumF, hsumF]
      simp only [hg, Finset.sum_add_distrib]
      rw [← sum_shift (fun n => if G.degree (e n).snd = 5 then sL M (e n) else 0) _
        (by beta_reduce; rw [hper])]
      rw [← Finset.sum_congr rfl (fun n _ => hcorner n), Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
    rcases (show G.degree v = 7 ∨ 8 ≤ G.degree v by omega) with h7' | h8
    · have hloss := sum_loss7_le _ _ _ _ _ _ _ (decide (fLen M (e 0).symm = 3))
        (decide (fLen M (e 1).symm = 3)) (decide (fLen M (e 2).symm = 3))
        (decide (fLen M (e 3).symm = 3)) (decide (fLen M (e 4).symm = 3))
        (decide (fLen M (e 5).symm = 3)) (decide (fLen M (e 6).symm = 3))
        (hδ (e 0).snd) (hδ (e 1).snd) (hδ (e 2).snd) (hδ (e 3).snd) (hδ (e 4).snd)
        (hδ (e 5).snd) (hδ (e 6).snd)
      rw [h7'] at hsend
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd] at hsend
      have he7 : e 7 = e 0 := by rw [← h7']; exact hper
      rw [he7] at hsend
      unfold loss7 at hloss
      unfold lossG at hsend
      rw [h7']
      push_cast
      linarith
    · have hle : ∑ n ∈ Finset.range (G.degree v), lossG (G.degree v) (G.degree (e n).snd)
          (G.degree (e (n + 1)).snd) (decide (fLen M (e n).symm = 3)) ≤
          (Finset.range (G.degree v)).card • (1 / 4 : ℚ) :=
        Finset.sum_le_card_nsmul _ _ _ (fun n _ => lossG_le _ h8 (hδ _) (hδ _))
      rw [Finset.card_range, nsmul_eq_mul] at hle
      have h8' : (8 : ℚ) ≤ G.degree v := by exact_mod_cast h8
      linarith

/-! ### The light star -/

theorem exists_light_star [Nonempty V] (hG : IsPlanar G) (hδ : ∀ v, 5 ≤ G.degree v) :
    ¬ NoStar (G := G) := by
  intro hns
  obtain ⟨M⟩ := hG
  obtain ⟨v0⟩ := ‹Nonempty V›
  obtain ⟨u, hu⟩ : ∃ u, G.Adj v0 u := by
    have hpos : 0 < (G.neighborFinset v0).card := by
      rw [G.card_neighborFinset_eq_degree]
      have := hδ v0
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.1 hpos
    exact ⟨u, by simpa using hu⟩
  have hK : (1 : ℚ) ≤ numComponents M.rot (dartSymm G) := by
    exact_mod_cast one_le_numComponents M ⟨(v0, u), hu⟩
  have hsum := sum_charge M
  rw [sum_split M] at hsum
  have hV : 0 ≤ ∑ d : G.Dart, ((1 - 6 / (G.degree d.fst : ℚ)) + gg M d.symm - gg M d +
      bigF M d.symm) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun d : G.Dart => d.fst)]
    exact Finset.sum_nonneg (fun v _ => vertex_nonneg M hδ hns v)
  have hFc : 0 ≤ ∑ x : G.Dart, ((2 - 6 / (fLen M x : ℚ)) - bigF M x) := by
    rw [← sum_avg_cls (SameCycle.setoid M.facePerm)]
    exact Finset.sum_nonneg (fun x _ => div_nonneg (face_orbit_nonneg M hδ x) (Nat.cast_nonneg _))
  linarith

end Lebesgue
