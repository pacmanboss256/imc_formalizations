/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.Data.PNat.Basic
public import Mathlib.Algebra.Order.Positive.Field
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Lemmas


public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }


/-!
## IMO 2003 Shortlist N3

Determine all functions f : ℕ+ → ℕ+ such that f(m)^2 + f(n) ∣ (m^2 + n)^2
for any m, n in ℕ+

-/

namespace imo2003SLN3
open Int

determine solution_set : Set (ℕ+ → ℕ+) :=
{fun x ↦ x }

problem imo_2003_SLN3 (f: ℕ+ → ℕ+):
f ∈ solution_set ↔ (∀m n:ℕ+, (f m)^2 + (f n) ∣ (m^2 + n)^2) := by
  constructor
  · intro h
    simp at h
    intro m n
    simp [h]

  intro h
  have l1 : f 1 = 1:= by
    specialize h 1 1
    simp at h
    change f 1 ^ 2 + f 1 ∣ 4 at h
    apply PNat.le_of_dvd at h
    by_cases hf : 2 ≤ f 1
    · apply_fun (λx:ℕ+ ↦ x^2 + x) at hf
      · simp at hf
        change 6 ≤ f 1 ^ 2 + f 1 at hf
        have i1 := LE.le.trans hf h
        tauto
      unfold Monotone
      intro a b hab
      simp
      apply Nat.add_le_add
      · apply pow_le_pow
        · assumption
        · grind
        rfl
      assumption
    push Not at hf
    apply PNat.le_sub_one_of_lt at hf
    change f 1 ≤ 1 at hf
    rw [le_one_iff_eq_one] at hf
    assumption


  have l2: ∀p, p.Prime → f (p-1) = p^2 - 1 ∨ f (p-1) = p - 1 := by
    intro p hp
    specialize h 1 (p-1)
    rw [l1] at h
    simp at h
    have : (1+(p-1)) = p := by
      rw [PNat.add_sub_of_lt]
      apply Nat.Prime.one_lt
      assumption
    rw [this] at h
    clear this
    have div := (Nat.Prime.divisors_sq hp)
    have : ((1 + f (p - 1)):ℕ) ∈ Nat.divisors (p^2) := by
      rw [Nat.mem_divisors]
      simp
      norm_cast
      rw [← PNat.dvd_iff]
      assumption
    rw [div] at this
    simp at this
    rcases this with l | r
    · norm_cast at l
      left
      apply_fun (·  - 1) at l
      rw [add_comm] at l
      simp at l
      assumption
    norm_cast at r
    right
    apply_fun (· - 1) at r
    rw [add_comm] at r
    simp at r
    assumption

  have fp: ∀p, p.Prime → f (p - 1) = p - 1 := by
    intro p hp
    specialize l2 p hp
    rcases l2 with h1 | h1
    · specialize h (p-1) 1
      rw [l1, h1] at h
      rw [PNat.dvd_iff] at h
      push_cast at h
      rw [PNat.sub_coe, PNat.sub_coe] at h
      have p1 : 1 < p := by apply PNat.Prime.one_lt hp
      have p2 : 1 < p^2 := by apply Nat.one_lt_pow (by decide : 2 ≠ 0) (p1)
      simp [p1, p2] at h
      apply Nat.le_of_dvd at h
      · simp at h
        rw [Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)] at h
        simp at h
        have : ∀x > 1, (x-1)^2 = x^2 - 2*x + 1 := by
            intro x hx
            zify
            rw [Nat.cast_sub, Nat.cast_sub, sub_sq]
            · simp
            · have xne : x ≠ 1 := by lia
              have h2 := Nat.mul_le_pow xne 2
              rwa [mul_comm]
            lia
        specialize this ((p:ℕ)) p1
        rw [this, add_comm, ←add_assoc, add_comm, ←add_assoc, ← two_mul, mul_one,add_comm] at h
        clear this
        have p_one : (p:ℕ) ≤ 1 := by
            zify at h
            rw [Nat.cast_sub] at h
            · push_cast at h
              rw [← add_zero ((p^2):ℤ),add_sub_assoc, add_assoc, add_le_add_iff_left ((p^2):ℤ), sub_add_comm, add_zero, sub_nonneg] at h
              norm_num at h
              assumption
            have pne : (p:ℕ) ≠ 1 := by
              apply Nat.ne_of_gt at p1
              assumption
            have h2 := Nat.mul_le_pow pne 2
            rwa [mul_comm]
        have p1a : 1 < (p:ℕ) := by apply PNat.Prime.one_lt hp
        apply not_le_of_gt at p1a
        contradiction
      positivity
    assumption

  have hdiv : ∀n, ∀p:ℕ+, p.Prime → (((f n)^2 + (p - 1)):ℤ) ∣ (n^2 - (f n)^2)^2 := by
    intro n p hp
    specialize h n (p-1)
    specialize fp p hp
    rw [fp] at h
    have p1 : 1 < p := by apply PNat.Prime.one_lt hp
    have hmid: (((f n)^2 + (p - 1)):ℤ) ∣ ((n^2 + (p-1)) - ((f n)^2 + (p - 1))) ^ 2 := by
      have i1 : (((f n)^2 + (p - 1)):ℤ) ∣ (2 * (n^2 + (p-1)) * ((f n) ^ 2 + (p - 1))) := by
        apply dvd_mul_left
      have i2 :  (((f n)^2 + (p - 1)):ℤ) ∣ ((f n)^2 + (p - 1))^2 := by
        apply dvd_pow_self
        decide

      rw [PNat.dvd_iff,← Int.natCast_dvd_natCast] at h
      push_cast at h
      rw [PNat.sub_coe] at h
      simp [p1] at h
      generalize (((f n) ^ 2 + (p - 1)):ℤ) = a at h i1 i2
      generalize ((n ^ 2 + (p - 1)):ℤ) = b at h i1 i2
      ring_nf
      rwa [dvd_add_right]
      rwa [dvd_add_right]
      rw [dvd_neg, ← mul_rotate]
      assumption
    simp at hmid
    assumption

  have hdiv_comm : ∀n, ∀p:ℕ+, p.Prime → (((f n)^2 + (p - 1)):ℤ) ∣ ((f n)^2 - n^2)^2 := by
    intro n p hp
    specialize hdiv n p hp
    rwa [sub_sq_comm]

  have feq: ∀n:ℕ+, f n = n := by
    intro N
    obtain lt | eq | gt := lt_trichotomy (f N) N
    · have hpg := Nat.exists_infinite_primes ((N ^ 2 -(f N) ^ 2) ^ 2 + 1)
      norm_cast at hpg
      have hs : f N ^ 2 < N ^ 2 := by
        apply Nat.pow_lt_pow_left
        · simp
          assumption
        decide
      have hpn : ∃ p:ℕ+, (N ^ 2 - (f N) ^ 2) ^ 2 + 1 ≤ p ∧ PNat.Prime p := by
        choose p hp hpp using hpg
        have p_min : 0 < p := by apply Nat.Prime.pos hpp
        let p':ℕ+ := ⟨p, p_min⟩
        use p'
        constructor
        · rw [← PNat.coe_le_coe]
          push_cast
          rw [PNat.sub_coe]
          simp only [hs, if_true]
          apply hp
        apply hpp
      clear hpg
      obtain ⟨p, hp, hpp⟩ := hpn

      have p1 : 1 < p := by apply PNat.Prime.one_lt hpp
      specialize hdiv N p hpp
      apply Int.le_of_dvd at hdiv
      · have hf1 : (1:ℤ) ≤ f N ^2 := by
            simp
            rw [← PNat.one_coe, PNat.coe_le_coe]
            bound
        have hf2 : (N ^ 2 - f N ^ 2) ^ 2 ≤ p - 1 := by
          rw [← add_le_add_iff_right 1]
          have int1 :  p - 1 + 1 = p := by
            apply PNat.sub_add_of_lt
            assumption
          rwa [int1]
        rw [← PNat.coe_le_coe] at hf2
        push_cast at hf2
        rw [PNat.sub_coe, PNat.sub_coe] at hf2
        simp [hs, p1] at hf2
        zify at hf2
        have i1 := Int.le_natCast_sub (N^2) ((f N)^2)
        push_cast at i1
        apply sq_le_sq' at i1
        · have i2 := LE.le.trans i1 hf2
          clear i1 hf2
          have i0 : (1:ℤ) + (↑↑p - 1) ≤ (↑↑N ^ 2 - ↑↑(f N) ^ 2) ^ 2 := by lia
          have i3 := LE.le.trans i0 i2
          simp at i3
        norm_num
        have i0 : ((N ^ 2):ℤ) ≤ N^2 + ↑(N ^ 2 - (f N) ^ 2) := by linarith
        suffices im : ((f N):ℤ) ^ 2 ≤ N^2
        · lia
        norm_cast
        apply le_of_lt at hs
        assumption
      rw [sq_pos_iff, sub_ne_zero]
      norm_num
      push Not
      rw [ne_iff_lt_or_gt]
      right
      assumption

    · assumption
    have hpg := Nat.exists_infinite_primes (((f N) ^ 2 -N ^ 2) ^ 2 + 1)
    norm_cast at hpg
    have hs : N ^ 2 < f N ^ 2 := by
      apply Nat.pow_lt_pow_left
      · simp
        assumption
      decide
    have hpn : ∃ p:ℕ+, ((f N) ^ 2 - N ^ 2) ^ 2 + 1 ≤ p ∧ PNat.Prime p := by
      choose p hp hpp using hpg
      have p_min : 0 < p := by apply Nat.Prime.pos hpp
      let p':ℕ+ := ⟨p, p_min⟩
      use p'
      constructor
      · rw [← PNat.coe_le_coe]
        push_cast
        rw [PNat.sub_coe]
        simp only [hs, if_true]
        apply hp
      apply hpp
    clear hpg
    obtain ⟨p, hp, hpp⟩ := hpn

    have p1 : 1 < p := by apply PNat.Prime.one_lt hpp
    specialize hdiv_comm N p hpp
    apply Int.le_of_dvd at hdiv_comm
    · have hf1 : (1:ℤ) ≤ f N ^2 := by
        simp
        rw [← PNat.one_coe, PNat.coe_le_coe]
        bound
      have hf2 : (f N ^ 2 - N ^ 2) ^ 2 ≤ p - 1 := by
        rw [← add_le_add_iff_right 1]
        have int1 :  p - 1 + 1 = p := by
          apply PNat.sub_add_of_lt
          assumption
        rwa [int1]

      rw [← PNat.coe_le_coe] at hf2
      push_cast at hf2
      rw [PNat.sub_coe, PNat.sub_coe] at hf2
      simp [hs, p1] at hf2
      zify at hf2
      have i1 := Int.le_natCast_sub ((f N)^2) (N^2)
      push_cast at i1
      apply sq_le_sq' at i1
      · have i2 := LE.le.trans i1 hf2
        clear i1 hf2
        have i0 : (1:ℤ) + (↑↑p - 1) ≤ (↑↑(f N) ^ 2 - ↑↑N ^ 2) ^ 2 := by lia
        have i3 := LE.le.trans i0 i2
        simp at i3
      norm_num
      have i0 : ((f N ^ 2):ℤ) ≤ (f N)^2 + ↑((f N) ^ 2 - N ^ 2) := by linarith
      suffices im :  (N:ℤ)^2 ≤ (f N) ^ 2
      · lia
      norm_cast
      apply le_of_lt at hs
      assumption
    rw [sq_pos_iff, sub_ne_zero]
    norm_num
    push Not
    rw [ne_iff_lt_or_gt]
    right
    assumption

  simp
  funext w
  specialize feq w
  assumption





















end imo2003SLN3
