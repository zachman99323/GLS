import Mathlib

set_option linter.unusedVariables false

open Set
open scoped Classical
open Finset BigOperators

namespace Inequality

lemma conv_nat_int_1 (a : ℕ) (ha : a ≥ 2):
Int.ofNat (a*(a-1)*(a-2)) = (Int.ofNat a)*((Int.ofNat a)-1)*((Int.ofNat a)-2) := by
  set x := Int.ofNat a with hxa
  have ha1: Int.ofNat (a-1) = x-1 := by
    rw[hxa]; apply Int.ofNat_sub; linarith
  have ha2: Int.ofNat (a-2) = x-2 := by
    rw[hxa]; apply Int.ofNat_sub; linarith
  have haL0 : Int.ofNat ((a-1)*(a-2)) = (x-1)*(x-2) := by
    have hnear := Mathlib.Tactic.Ring.mul_congr (Eq.symm ha1) (Eq.symm ha2) rfl
    tauto
  have hnear := Mathlib.Tactic.Ring.mul_congr hxa (Eq.symm haL0) rfl
  rw[← mul_assoc] at hnear
  rw[hnear]
  rw[mul_assoc]
  exact Int.ofNat_mul (a) ((a-1)*(a-2))

lemma ineq_1_Z (x y : ℤ) (hx : x ≥ 2) (hy : y ≥ 2): x*(x-1)*(x-2)+y*(y-1)*(y-2) ≤ (x+y)*(x+y-1)*(x+y-2) := by
  suffices: (x+y)*(x+y-1)*(x+y-2) - (x*(x-1)*(x-2)+y*(y-1)*(y-2)) ≥ 0
  . linarith
  have hnear : (x+y)*(x+y-1)*(x+y-2) - (x*(x-1)*(x-2)+y*(y-1)*(y-2)) = 3*x*y*(x+y-2) := by
    ring
  rw[hnear]
  refine Int.mul_nonneg ?_ ?_
  refine Int.mul_nonneg ?_ ?_
  linarith; linarith; linarith

lemma ineq_1_22 (a b : ℕ) (ha: a ≥ 2) (hb: b ≥ 2): a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ (a+b)*(a+b-1)*(a+b-2) := by
  apply Int.ofNat_le.mp
  rw[Int.ofNat_add]

  set x := Int.ofNat a with hxa
  set y := Int.ofNat b with hyb

  have haL := conv_nat_int_1 a ha
  have hbL := conv_nat_int_1 b hb
  have habge2 : a+b ≥ 2 := by linarith
  have habR := conv_nat_int_1 (a+b) habge2

  have hL : ↑(a * (a - 1) * (a - 2)) + ↑(b * (b - 1) * (b - 2)) = x*(x-1)*(x-2)+y*(y-1)*(y-2) := by
    exact Lean.Omega.Int.add_congr haL hbL
  have hR : ↑((a + b) * (a + b - 1) * (a + b - 2)) = (x+y)*(x+y-1)*(x+y-2) := by
    exact habR
  rw[hL]; rw[hR]
  refine ineq_1_Z x y ?_ ?_
  rw[hxa];
  apply Int.ofNat_le.mpr; linarith
  apply Int.ofNat_le.mpr; linarith

lemma ineq_1_1b (a b : ℕ) (ha1 : a = 1): a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ (a+b)*(a+b-1)*(a+b-2) := by
  rw[ha1]
  simp
  refine Nat.mul_le_mul ?h₁ ?h₂
  refine Nat.mul_le_mul ?h₁.h₁ ?h₁.h₂
  linarith
  exact Nat.sub_le b 1
  refine Nat.sub_le_sub_right ?h₂.h 2
  exact Nat.le_add_left b 1

lemma ineq_1_a1 (a b : ℕ) (hb1 : b = 1): a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ (a+b)*(a+b-1)*(a+b-2) := by
  have hnear := ineq_1_1b b a hb1
  rw[add_comm]
  rw[add_comm a b]
  exact hnear

lemma ineq_1 (a b : ℕ): a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ (a+b)*(a+b-1)*(a+b-2) := by
  by_cases hage2: a ≥ 2
  by_cases hbge2: b ≥ 2
  exact ineq_1_22 a b hage2 hbge2
  have hb01 : b = 0 ∨ b = 1 := by
    push_neg at hbge2
    refine Nat.le_one_iff_eq_zero_or_eq_one.mp ?_
    exact Nat.le_of_lt_succ hbge2
  rcases hb01 with (hb0 | hb1)
  rw[hb0]; simp
  exact ineq_1_a1 a b hb1
  have ha01 : a = 0 ∨ a = 1 := by
    push_neg at hage2
    refine Nat.le_one_iff_eq_zero_or_eq_one.mp ?_
    exact Nat.le_of_lt_succ hage2
  rcases ha01 with (ha0 | ha1)
  rw[ha0]; simp
  exact ineq_1_1b a b ha1

lemma ineq_2_Z (x y z : ℤ) (hxge1 : x ≥ 2) (hyge1 : y ≥ 2) (hxlez : x ≤ z) (hylez: y ≤ z):
x*(x-1)*(x-2)+y*(y-1)*(y-2) ≤ z*(z-1)*(z-2)+(x+y-z)*(x+y-z-1)*(x+y-z-2) := by
  suffices: z*(z-1)*(z-2)+(x+y-z)*(x+y-z-1)*(x+y-z-2) - (x*(x-1)*(x-2)+y*(y-1)*(y-2)) ≥ 0
  . exact Int.le_of_sub_nonneg this
  have hnear : (z*(z-1)*(z-2)+(x+y-z)*(x+y-z-1)*(x+y-z-2))-(x*(x-1)*(x-2)+y*(y-1)*(y-2)) = 3*(z-x)*(z-y)*(x+y-2) := by
    ring
  rw[hnear]
  refine Int.mul_nonneg ?_ ?_
  refine Int.mul_nonneg ?_ ?_
  refine Int.mul_nonneg ?_ ?_
  norm_num; linarith; linarith; linarith

lemma ineq_2_noa (b c : ℕ) (hblec : b ≤ c): b*(b-1)*(b-2) ≤ c*(c-1)*(c-2) := by
  refine Nat.mul_le_mul ?_ ?_
  refine Nat.mul_le_mul ?_ ?_
  exact hblec; exact Nat.sub_le_sub_right hblec 1
  exact Nat.sub_le_sub_right hblec 2

lemma ineq_2_alt2 (a b c : ℕ) (halec : a ≤ c) (hblec : b ≤ c) (halt2 : a < 2):
a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ c*(c-1)*(c-2) + (a+b-c)*(a+b-c-1)*(a+b-c-2) := by
  have ha01 : a = 0 ∨ a = 1 := by
    refine Nat.le_one_iff_eq_zero_or_eq_one.mp ?_
    exact Nat.le_of_lt_succ halt2
  rcases ha01 with (ha0 | ha1)
  rw[ha0]; simp
  suffices: b*(b-1)*(b-2) ≤ c*(c-1)*(c-2)
  . exact le_add_right this
  exact ineq_2_noa _ _ hblec
  rw[ha1]; simp
  suffices: b*(b-1)*(b-2) ≤ c*(c-1)*(c-2)
  . exact le_add_right this
  exact ineq_2_noa _ _ hblec

lemma ineq_2_blt2 (a b c : ℕ) (halec : a ≤ c) (hblec : b ≤ c) (hblt2 : b < 2):
a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ c*(c-1)*(c-2) + (a+b-c)*(a+b-c-1)*(a+b-c-2) := by
  have hnear := ineq_2_alt2 b a c hblec halec hblt2
  rw[add_comm a b]
  linarith

lemma ineq_2_age2_bge2_cleab2 (a b c : ℕ) (hage2 : a ≥ 2) (hbge2 : b ≥ 2) (halec : a ≤ c)
(hblec : b ≤ c) (hcleab2 : c ≤ a+b-2):
a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ c*(c-1)*(c-2) + (a+b-c)*(a+b-c-1)*(a+b-c-2) := by
  have hcge2 : c ≥ 2 := by
    exact Nat.le_trans hage2 halec
  have habcge2 : a+b-c ≥ 2 := by
    refine Nat.le_sub_of_add_le ?h
    refine (Nat.le_sub_iff_add_le' ?h.h).mp hcleab2
    exact le_add_right hage2

  have haL := conv_nat_int_1 a hage2
  have hbL := conv_nat_int_1 b hbge2
  have hcR := conv_nat_int_1 c hcge2
  have habcR := conv_nat_int_1 (a+b-c) habcge2
  set x := Int.ofNat a with hxa
  set y := Int.ofNat b with hyb
  set z := Int.ofNat c with hzc
  set w := Int.ofNat (a+b-c) with hwabc

  have hweqxyz : w = x+y-z := by
    dsimp[w,x,y,z]
    suffices: ↑(a+b-c) + ↑ c = ↑ a + ↑ b
    . linarith
    refine Nat.sub_add_cancel ?_
    suffices: a+b-2 ≤ a+b
    . exact Nat.le_trans hcleab2 this
    exact Nat.sub_le (a + b) 2

  have hL : ↑(a * (a - 1) * (a - 2)) + ↑(b * (b - 1) * (b - 2)) = x*(x-1)*(x-2)+y*(y-1)*(y-2) := by
    exact Lean.Omega.Int.add_congr haL hbL
  have hR : ↑(c * (c - 1) * (c - 2) + (a + b - c) * (a + b - c - 1) * (a + b - c - 2))
    = z*(z-1)*(z-2)+w*(w-1)*(w-2) := by
    exact Lean.Omega.Int.add_congr hcR habcR

  apply Int.ofNat_le.mp
  rw[Nat.cast_add]; rw[hL]; rw[hR]

  have hxge2 : x ≥ 2 := by
    dsimp[x]; norm_cast
  have hyge2 : y ≥ 2 := by
    dsimp[y]; norm_cast
  have hxlez : x ≤ z := by
    dsimp[x,z]; norm_cast
  have hylez : y ≤ z := by
    dsimp[y,z]; norm_cast
  have hnear := ineq_2_Z x y z hxge2 hyge2 hxlez hylez
  suffices: w = x+y-z
  . rw[this]; exact hnear
  exact hweqxyz

lemma ineq_1_stronger_Z (x y : ℤ) (hxge2 : x ≥ 2) (hyge2: y ≥ 2):
x*(x-1)*(x-2)+y*(y-1)*(y-2) ≤ (x+y-1)*(x+y-2)*(x+y-3) := by
  suffices: (x+y-1)*(x+y-2)*(x+y-3) - (x*(x-1)*(x-2)+y*(y-1)*(y-2)) ≥ 0
  . linarith
  have hnear : (x+y-1)*(x+y-2)*(x+y-3) - (x*(x-1)*(x-2)+y*(y-1)*(y-2)) = 3*(x-1)*(y-1)*(x+y-2) := by
    ring
  rw[hnear]
  refine Int.mul_nonneg ?_ ?_
  refine Int.mul_nonneg ?_ ?_
  refine Int.mul_nonneg ?_ ?_
  linarith
  linarith
  linarith
  linarith

lemma ineq_1_stronger (a b c : ℕ) (hage2 : a ≥ 2) (hbge2 : b ≥ 2):
a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ (a+b-1)*(a+b-2)*(a+b-3) := by
  apply Int.ofNat_le.mp
  rw[Int.ofNat_add]

  have haL := conv_nat_int_1 a hage2
  have hbL := conv_nat_int_1 b hbge2
  have habge2 : a+b-1 ≥ 2 := by
    have habge4 : a+b ≥ 4 := by
      have hnear := add_le_add hage2 hbge2
      norm_num at hnear; exact hnear
    have hnear : a+b-1 ≥ 3 := by
      exact Nat.le_sub_one_of_lt habge4
    exact Nat.le_of_succ_le hnear
  have habR := conv_nat_int_1 (a+b-1) habge2

  set x := Int.ofNat a with hxa
  set y := Int.ofNat b with hyb
  set z := Int.ofNat (a+b-1) with hzab1

  have hL : ↑(a * (a - 1) * (a - 2)) + ↑(b * (b - 1) * (b - 2)) = x*(x-1)*(x-2)+y*(y-1)*(y-2) := by
    exact Lean.Omega.Int.add_congr haL hbL
  have hR : ↑((a + b - 1) * (a + b - 2) * (a + b - 3)) = z*(z-1)*(z-2) := by
    exact habR
  rw[hL]; rw[hR]

  have hxge2 : x ≥ 2 := by
    dsimp[x]; norm_cast
  have hyge2 : y ≥ 2 := by
    dsimp[y]; norm_cast

  have hnear := ineq_1_stronger_Z x y hxge2 hyge2

  have hzxy1 : z = x+y-1 := by
    dsimp[z,x,y]
    have habge1 : a+b ≥ 1 := by
      have hnear3 : a+b ≥ a := by
        exact Nat.le_add_right a b
      have hage1 : a ≥ 1 := by
        exact Nat.one_le_of_lt hage2
      exact Nat.le_trans hage1 hnear3
    have hnear1 : Int.ofNat (a+b-1) = Int.ofNat (a+b) - 1 := by
      have hnear2 : (Int.ofNat (a+b-1)) + 1 = Int.ofNat (a+b) := by
        have hadd : (a+b-1)+1 = a+b := by
          exact Nat.sub_add_cancel habge1
        exact
          Eq.symm
            ((fun {a b} ↦ Int.neg_inj.mp) (congrArg Neg.neg (congrArg Int.ofNat (id (Eq.symm hadd)))))
      exact eq_sub_of_add_eq hnear2
    exact hnear1

  rw[hzxy1]
  have hnear1 : x+y-1-1 = x+y-2 := by
    ring
  have hnear2 : x+y-1-2 = x+y-3 := by
    ring

  rw[hnear1,hnear2]; exact hnear

lemma ineq_2_age2_bge2_ab1lec (a b c : ℕ) (hage2 : a ≥ 2) (hbge2 : b ≥ 2) (halec : a ≤ c)
(hblec : b ≤ c) (hab1lec : a+b-1 ≤ c):
a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ c*(c-1)*(c-2) + (a+b-c)*(a+b-c-1)*(a+b-c-2) := by
  have h01 : a+b-1-c = 0 := by
    exact Nat.sub_eq_zero_of_le hab1lec
  have heq : a+b-c-1 = a+b-1-c := by
    exact Nat.sub_right_comm (a + b) c 1
  have h0 : a+b-c-1 = 0 := by
    rw[← h01]
    exact heq
  rw[h0]; rw[mul_zero, zero_mul, add_zero]
  have hnear := ineq_1_stronger a b c hage2 hbge2
  suffices: (a+b-1)*(a+b-2)*(a+b-3) ≤ c*(c-1)*(c-2)
  . exact Nat.le_trans hnear this
  refine Nat.mul_le_mul ?_ ?_
  refine Nat.mul_le_mul ?_ ?_
  exact hab1lec; exact Nat.sub_le_sub_right hab1lec 1
  exact Nat.sub_le_sub_right hab1lec 2

lemma ineq_2_age2_bge2 (a b c : ℕ) (hage2 : a ≥ 2) (hbge2 : b ≥ 2) (halec : a ≤ c) (hblec : b ≤ c):
a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ c*(c-1)*(c-2) + (a+b-c)*(a+b-c-1)*(a+b-c-2) := by
  by_cases hcleab2 : c ≤ a+b-2
  exact ineq_2_age2_bge2_cleab2 a b c hage2 hbge2 halec hblec hcleab2
  push_neg at hcleab2
  have hab1lec : a+b-1 ≤ c := by
    exact Nat.le_of_pred_lt hcleab2
  exact ineq_2_age2_bge2_ab1lec a b c hage2 hbge2 halec hblec hab1lec

lemma ineq_2_nod (a b c : ℕ) (halec : a ≤ c) (hblec : b ≤ c):
a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ c*(c-1)*(c-2) + (a+b-c)*(a+b-c-1)*(a+b-c-2) := by
  by_cases hage2 : a ≥ 2
  by_cases hbge2 : b ≥ 2
  exact ineq_2_age2_bge2 _ _ _ hage2 hbge2 halec hblec
  push_neg at hbge2; exact ineq_2_blt2 a b c halec hblec hbge2
  push_neg at hage2; exact ineq_2_alt2 a b c halec hblec hage2

lemma ineq_2 (a b c d : ℕ) (halec : a ≤ c) (hblec : b ≤ c) (habcd : a+b = c+d):
  a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ c*(c-1)*(c-2)+d*(d-1)*(d-2) := by
  have hcleab : c ≤ a+b := by
    rw[habcd]; exact Nat.le_add_right c d
  have hdeq : d = a+b-c := by
    rw[habcd]
    exact Nat.eq_sub_of_add_eq' rfl
  rw[hdeq]
  exact ineq_2_nod a b c halec hblec


end Inequality
