/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.RingTheory.Prime

public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
## IMO Shortlist 1979 #23
Find all natural numbers $n$ for which $2^8 +2^{11} +2^n$ is a perfect square.
-/

namespace imo1973SL23

determine solution_set: Set (ℕ) := {12}

theorem imo1973_SL23 (n:ℕ): n ∈ solution_set ↔ IsSquare (2^8 + 2^11 + 2^n) := by
  constructor
  · simp
    intro hn
    rw [hn]
    simp
    use 80
  intro h
  suffices n_bound : n ≥ 8
  · have : 2^8+2^11+2^n = 2^8 * (1 + 2^3 + 2^(n-8)) := by
      nth_rw 2 [add_assoc]
      rw [mul_add, mul_add, ← pow_add, ← pow_add]
      rw [← add_assoc]
      simp
      rw [add_comm, Nat.sub_add_cancel]
      assumption

    rw [this] at h
    simp at h
    have h256 : IsSquare (256:ℚ) := by use 16; ring
    rw [mul_comm] at h
    have hsq : IsSquare ((9:ℚ) + 2 ^ (n - 8)) := by
      apply IsSquare.inv at h256
      rw [inv_eq_one_div] at h256
      have h0: IsSquare (((9:ℚ) + 2 ^ (n - 8)) * 256) := by exact_mod_cast h
      have h1 : IsSquare ((9 + 2 ^ (n - 8)) * 256 * ((1:ℚ)/256)):= IsSquare.mul h0 h256
      simp at h1
      apply h1
    rw [add_comm] at hsq
    norm_cast at hsq
    have hex := IsSquare.exists_sq (2 ^ (n - 8) + 9) hsq
    obtain ⟨r, hr⟩ := hex
    symm at hr
    have hrp : 3 ≤ r := by
      rw [← pow_le_pow_iff_left₀ (by positivity: 0 ≤ 3) (by positivity: 0 ≤ r) (by positivity: 2 ≠ 0)]
      rw [hr]
      simp
    rw [← Nat.sub_eq_iff_eq_add] at hr
    swap
    · apply mul_self_le_mul_self (by positivity: 0 ≤ 3) at hrp
      simp at hrp
      rwa [← pow_two] at hrp
    change r ^ 2 - 3^2 = 2 ^ (n - 8) at hr
    rw [Nat.sq_sub_sq] at hr
    let r1 := r - 3
    change (r+3)  * r1 = 2 ^ (n-8) at hr
    rw [show (r+3 = r1+6) by dsimp [r1]; rw [show (6=3+3) by decide, ← add_assoc, Nat.sub_add_cancel (hrp)]] at hr
    have hd1 : ∃s, r1 = 2^s := by
      apply Dvd.intro_left at hr
      rw [Nat.dvd_prime_pow] at hr
      · obtain ⟨k, hk1, hk2⟩ := hr
        use k
      decide
    have hd2 : ∃s2, (r1+6) = 2^s2 := by
      apply Dvd.intro at hr
      rw [Nat.dvd_prime_pow] at hr
      · obtain ⟨k, hk1, hk2⟩ := hr
        use k
      decide
    obtain ⟨s1, hs1⟩ := hd1
    obtain ⟨s2, hs2⟩ := hd2
    rw [hs1] at hs2
    have hsg : s1 < s2 := by
      have hs2a := hs2
      apply Nat.le.intro at hs2
      rw [Nat.pow_le_pow_iff_right,le_iff_lt_or_eq] at hs2
      · rcases hs2 with lt | eq
        · assumption
        rw [← add_zero (2^s2),eq] at hs2a
        apply add_left_cancel at hs2a
        contradiction
      decide
    have hsg1 : s1 + 1 < s2:= by
      by_contra! hs'
      apply lt_or_eq_of_le at hs'
      rcases hs' with lt | eq
      · omega
      rw [eq, Nat.two_pow_succ] at hs2
      simp at hs2
      have h2 : 2^2 < 2^s1 := by lia
      have h3 : 2^s1 < 2^3 := by lia
      rw [Nat.pow_lt_pow_iff_right] at h2 h3
      · omega
      · decide
      decide
    rw [← Nat.pow_lt_pow_iff_right (by decide : 1 < 2), Nat.two_pow_succ, ← hs2] at hsg1
    simp at hsg1
    have h6 : 6 < 2^3 := by decide
    replace h6 := LT.lt.trans hsg1 h6
    rw [Nat.pow_lt_pow_iff_right] at h6
    · have s1eq : s1 = 1 := by
        have s1_op : s1 = 0 ∨ s1 = 1 ∨ s1 = 2 := by grind
        rcases s1_op with zero | one | two
        · rw [zero] at hs2
          simp at hs2
          have heven : Even (2^s2) := by
            rw [Nat.even_pow]
            simp
            omega
          rw [← hs2] at heven
          tauto
        · assumption
        rw [two] at hs2
        simp at hs2
        have i1 : 2^3 < 2^s2 := by lia
        have i2 : 2^s2 < 2^4 := by lia
        rw [Nat.pow_lt_pow_iff_right] at i1 i2
        · omega
        · decide
        decide
      rw [s1eq] at hs1
      simp at hs1
      rw [hs1] at hr
      simp at hr
      rw [show 16 = 2^4 by decide, Nat.pow_right_inj] at hr
      · simp
        symm at hr
        apply Nat.eq_add_of_sub_eq at hr
        · simp at hr
          assumption
        assumption
      decide
    decide
  by_contra!
  have n_opts : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by grind
  rename IsSquare (2 ^ 8 + 2 ^ 11 + 2 ^ n) => h1
  rcases n_opts with h | h | h | h | h | h | h | h
  all_goals (rw [h] at h1; simp at h1; norm_num at h1)















































end imo1973SL23
