/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Algebra.Order.Positive.Field

public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Test] }


/-!
## IMO 2023 Shortlist A4

Let ℝ>0 be the set of positive reals. Determine all functions f : ℝ>0 → ℝ>0 such that x(f(x)+f(y)) ≥ (f(f(x))+y)f(y)
for all x,y ∈ ℝ>0

-/

namespace imo23SLA4
open NNReal

snip begin
theorem main_thm (f : ℝ≥0 → ℝ≥0) (hb: ∀x, f x > 0) (h: ∀ x>0, ∀y>0, (f (f x) + y)*(f y) ≤ x * (f x + f y)) : ∀x > 0, ∀y > 0, x*(f x) ≥ y * (f y) := by
    have hbound : ∀x>0, ∀n, f^[n] x > 0 := by
      intro x hx n
      induction n with
      | zero => simp; assumption
      | succ d hd =>
        rw [add_comm, Function.iterate_add_apply f 1 d x]
        simp
        apply hb

    have l1 : ∀x>0, f^[2] x ≤ x:= by
      intro x hx
      specialize h x hx x hx
      rw [← two_mul, ← mul_assoc] at h
      rw [mul_le_mul_iff_of_pos_right, mul_two,add_le_add_iff_right] at h
      · assumption
      bound

    have l2 : ∀x>0, ((x - f^[2] x):ℝ) ≤ f x - f^[3] x := by
      intro x hx
      specialize h (f x) (hb x) x hx
      rw [mul_comm, mul_le_mul_iff_of_pos_left] at h
      · rify at h
        nth_rw 2 [add_comm] at h
        rw [add_comm, ← sub_le_sub_iff] at h
        norm_cast
      apply hb



    have h_dec :∀x > 0, ∀n:ℕ, ((x - f^[2] x):ℝ) ≤ f^[n] x - f^[n+2] x := by
      intro x hx n
      induction n with
      | zero => simp
      | succ d hd =>
        specialize hbound x hx
        suffices : (((f^[d] x) - (f^[d + 2] x)):ℝ) ≤ ↑(f^[d + 1] x) - ↑(f^[d + 1 + 2] x)
        · have ht := LE.le.trans hd this
          assumption
        ring_nf
        have i1 := l2 (f^[d] x)
        have i2 := l2 (f^[1+d] x)
        simp only [hbound, true_implies] at i1 i2
        nth_rw 4 [← Function.iterate_one f] at i1 i2
        rw [← Function.iterate_add_apply f, ← Function.iterate_add_apply f,← Function.iterate_add_apply f] at i1 i2
        ring_nf at i1 i2
        have i3 := LE.le.trans i1 i2
        assumption

    have h_dec' : ∀x > 0,∀j:ℕ,(f^[j+2] x) ≤ ((f^[j] x - (x - f^[2] x)):ℝ) := by
        intro x hx j
        ring_nf at h_dec
        specialize h_dec x hx
        rw [le_sub_iff_add_le', ← le_sub_iff_add_le, add_comm]
        apply h_dec j

    have hd : ∀x > 0, ∀k :ℕ, (f^[2*k] x) ≤ ((x - k*(x - f^[2] x)):ℝ) := by
      intro x hx k
      induction k with
      | zero => simp
      | succ k ih =>
        let d:ℝ := (↑x - ↑(f^[2] x))
        have d_pos : 0 ≤ d := by
          specialize l1 x hx
          linarith
        specialize h_dec' x hx
        change ↑(f^[2 * k] x) ≤ ↑x - ↑k * d at ih
        change ↑(f^[2 * (k + 1)] x) ≤ ↑x - ↑(k + 1) * d
        specialize h_dec' (2*k)
        change ↑(f^[2 * k + 2] x) ≤ ↑(f^[2*k] x) - d at h_dec'
        ring_nf
        rw [Function.iterate_add_apply f]
        have i1 : ↑((f^[2] (f^[k * 2] x)):ℝ) ≤ ↑(f^[k * 2] x) := by
          exact l1 ((f^[k * 2] x)) (hbound x hx (k*2))
        push_cast
        rw [add_mul]
        rw [← sub_le_sub_iff_right d] at ih
        ring_nf
        rw [← sub_add_eq_sub_sub, add_comm, sub_add_eq_sub_sub]
        rw [add_comm, Function.iterate_add_apply f] at h_dec'
        have i2 := LE.le.trans h_dec' ih
        rw [mul_comm]
        nth_rw 2 [mul_comm]
        assumption

    have f_invol : ∀x > 0, f^[2] x = x := by
      intro x hx
      let d:ℝ := (↑x - ↑(f^[2] x))
      have d_nonneg : 0 ≤ d := by
        specialize l1 x hx
        linarith
      specialize l1 x hx
      rw [le_iff_eq_or_lt] at l1
      rcases l1 with eq | lt
      · assumption
      by_contra! hgarb'
      have d_pos : 0 < d := by
        linarith
      specialize hd x hx
      change ∀ (k : ℕ), ↑(f^[2 * k] x) ≤ ↑x - ↑k * d at hd
      suffices : ∃k₀:ℕ, ↑x < ↑k₀ * d
      · obtain ⟨k₀, hk₀⟩ := this
        specialize hd k₀
        apply sub_neg_of_lt at hk₀
        have c1 : (f^[2 * k₀] x) < 0 := by linarith
        specialize hbound x hx (2*k₀)
        linarith
      use Nat.ceil ((x+1)/d)
      have h1 := Nat.le_ceil ((x+1)/d)
      have h1a := mul_le_mul_of_nonneg_right h1 d_nonneg
      suffices : ↑x < ((↑x + 1) / d) * d
      · have h2 := lt_of_lt_of_le this h1a
        assumption
      rw [mul_comm, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self]
      · simp
      rw [ne_iff_lt_or_gt]
      right
      assumption

    have hfinal : ∀x > 0, ∀y > 0, x*(f x) ≥ y * (f y) := by
      intro x hx y hy
      specialize h x hx y hy
      specialize f_invol x hx
      simp at f_invol
      rw [f_invol] at h
      ring_nf at h
      simp at h
      simp
      assumption

    assumption
snip end

determine solution_set : Set (ℝ≥0 → ℝ≥0) :=
  { f : ℝ≥0 → ℝ≥0 | ∃ c > 0, f = fun x ↦ c / x }


problem imo_2023_shortlist_A4 (f : ℝ≥0 → ℝ≥0) (hb: ∀x, f x > 0)(y₀:ℝ≥0)(y₀_pos: 0 < y₀)(hg:f 0 = 0):
  f ∈ solution_set ↔
    (∀ x>0, ∀y>0, (f (f x) + y)*(f y) ≤ x * (f x + f y)) := by
  constructor
  · intro hf x hx y hy
    simp at hf
    obtain ⟨c, hc, cf⟩:= hf
    simp [cf]
    field_simp
    rw [add_comm]
  intro h
  have h0 : ∀y > 0, ∀x>0, f x = y * f y / x := by
    intro y ypos x xpos
    have h1 := main_thm f hb h x xpos y ypos
    have h2 := main_thm f hb h y ypos x xpos
    have h3 := le_antisymm h2 h1
    field_simp
    rwa [mul_comm]
  specialize h0 y₀ y₀_pos
  simp
  use y₀ * f y₀
  constructor
  · have : 0 < y₀ * f y₀ := by
      specialize hb y₀
      positivity
    assumption
  funext w
  specialize h0 w
  by_cases hw : w = 0
  · specialize hb w
    change 0 < f w at hb
    rw [hw] at hb
    apply ne_of_gt at hb
    tauto
  push Not at hw
  rw [ne_iff_lt_or_gt] at hw
  rcases hw with lt | gt
  · simp at lt
  apply h0 at gt
  assumption





















end imo23SLA4
