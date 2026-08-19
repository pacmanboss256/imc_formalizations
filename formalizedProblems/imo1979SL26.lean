/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic

public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMO Shortlist 1979 #26
Show f(x+y) = f(x) + f(y) is equivalent to f(x+y+x*y) = f(x)+f(y)+f(x * y) for x,y ∈ ℝ
-/

namespace imo1979SL26
open Real

theorem imo_1979SL26 (f:ℝ → ℝ): (∀x y:ℝ, f (x+y) = f x + f y) ↔ ∀x y:ℝ, f (x + y + x*y) = f x + f y + f (x*y) := by
  constructor
  · intro h x y
    have h1 := h x (y+x*y)
    have h2 := h y (x*y)
    rw [h2, ← add_assoc, ← add_assoc] at h1
    assumption
  intro h
  have f_zero : f 0 = 0 := by
    specialize h 0 0
    simp at h
    assumption
  have f_odd: ∀x, f (-x) = -f (x) := by
    intro x
    have fx1 := h x (-1)
    simp at fx1
    rw [← add_rotate] at fx1
    simp at fx1
    rw [add_eq_zero_iff_eq_neg] at fx1
    assumption
  have f2x : ∀x, f (1 + x*2) = f x * 2 + f (1) := by
    intro x
    have fx2 := h x 1
    ring_nf at fx2
    assumption
  have fcomm : ∀x y, f (x * y) + f (x + y + x * y) = f (x + x*y*2 + y) := by
    intro x y
    have h1 := h (2*x+1) (2*y+1)
    ring_nf at h1
    have LHS: f (3 + x * 4 + x * y * 4 + y * 4) = f (x + y + x * y) * 4 + (f 1) * 3 := by
      nth_rw 1 [show ((3:ℝ) = 1 + 2) by norm_num]
      rw [show  (1 + 2 + x * 4 + x * y * 4 + y * 4 = 1 + (1 + x * 2 + x * y * 2 + y * 2)*2) by ring,f2x (1 + x * 2 + x * y * 2 + y * 2)]
      rw [show (1 + x * 2 + x * y * 2 + y * 2 = 1 + (x + x*y + y)*2) by ring, f2x (x + x*y + y)]
      ring_nf
    rw [LHS] at h1
    have RHS: f (1 + x * 2) + f (1 + y * 2) + f (1 + x * 2 + x * y * 4 + y * 2) = (f x)*2+(f y)*2 + f (x*y*2+x+y)*2 + (f 1)*3 := by
      rw [f2x x, f2x y]
      ring_nf
      rw [show (1 + x * 2 + x * y * 4 + y * 2 = 1 + (x + x*y*2 + y)*2) by ring, f2x (x + x*y*2 + y)]
      ring_nf
    rw [RHS] at h1
    clear LHS RHS
    rw [h x y] at h1
    ring_nf at h1
    nth_rw 4 [← add_comm] at h1
    rw [← add_assoc] at h1
    simp at h1
    rw [show (f x * 4 + f y * 4 = f x * 2 + f y * 2 + f x * 2 + f y * 2) by ring, add_comm] at h1
    repeat rw [←add_assoc] at h1
    simp at h1
    rw [show f (x * y) * 4 = (f (x * y) * 2)*2 by ring] at h1
    repeat rw [← add_mul] at h1
    simp at h1
    rw [mul_two, add_assoc, add_assoc, add_rotate', ← h x y] at h1
    assumption


  have f2xy : ∀x y, f x + f (x * y) * 2 = f (x + x * y * 2) := by
    intro a b
    have hx := f2x (a+b+a*b)
    rw [h a b] at hx
    ring_nf at hx
    have ha2b := h a (2*b+1)
    ring_nf at ha2b
    rw [f2x b] at ha2b
    ring_nf at ha2b
    rw [hx] at ha2b
    rw [show f a * 2 + f b * 2 + f (a * b) * 2 + f 1 = f 1 + (f b * 2 + (f a + (f a + f (a * b) * 2))) by ring] at ha2b
    rw [show f a + f b * 2 + f 1 + f (a + a * b * 2) = f 1 + (f b * 2 + (f a + f (a + a*b*2))) by ring_nf] at ha2b
    rw [add_left_cancel_iff, add_left_cancel_iff, add_left_cancel_iff] at ha2b
    assumption

  have hx2 : ∀x, f (2*x) = f x * 2 := by
    intro x
    have hi := f2xy (2*x) (-1/2)
    ring_nf at hi
    rw [f_zero, f_odd, neg_mul, add_neg_eq_zero] at hi
    ring_nf
    assumption

  have f3 : ∀ x y, f (x + x * y * 2) = f x + f (x * y * 2):= by
    intro x y
    have h1 := f2xy x y
    rw [← hx2 (x*y), ← mul_assoc, mul_rotate] at h1
    symm
    assumption

  intro a b
  specialize f3 a (b/(2*a))
  ring_nf at f3
  by_cases ha : a = 0
  · rw [ha, f_zero]
    simp
  push Not at ha
  rw [mul_assoc, mul_comm, mul_assoc, inv_mul_cancel₀ ha] at f3
  simp at f3
  assumption

end imo1979SL26
