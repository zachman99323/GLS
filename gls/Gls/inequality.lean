import Mathlib

set_option linter.unusedVariables false

open Set
open scoped Classical
open Finset BigOperators

namespace Inequality

--a ≥ b ≥ 1 --> {a 3} + {b 3} ≤ {a+1 3} {b-1 3}
lemma pre_ineq (a b : ℕ) (hageb : a ≥ b):
(a+1)*a*(a-1) + (b+1)*b*(b-1) ≤ (a+2)*(a+1)*a+b*(b-1)*(b-2) := by
  set l1 := (a+1)*a*(a-1) with hl1def
  set l2 := (b+1)*b*(b-1) with hl2def
  set r1 := (a+2)*(a+1)*a with hr1def
  set r2 := b*(b-1)*(b-2) with hr2def
  have hl1ler1: l1 ≤ r1 := by
    rw[hl1def, hr1def]; refine Nat.mul_le_mul ?_ ?_; refine Nat.mul_le_mul ?_ ?_
    exact Nat.le_succ _; exact Nat.le_succ ?_; exact Nat.sub_le _ _
  have hr2lel2: r2 ≤ l2 := by
    rw[hl2def, hr2def]; refine Nat.mul_le_mul ?_ ?_; refine Nat.mul_le_mul ?_ ?_
    exact Nat.le_succ _; exact Nat.sub_le _ _; exact Nat.sub_le_succ_sub b 2
  suffices: l2 ≤ r1+r2-l1
  . refine (Nat.le_sub_iff_add_le' ?_).mp this
    refine le_trans hl1ler1 ?_; exact Nat.le_add_right r1 r2
  have hrw: r1+r2-l1 = (r1-l1)+r2 := by
    exact Nat.sub_add_comm hl1ler1
  rw[hrw]
  suffices: l2-r2 ≤ r1-l1
  . exact Nat.le_add_of_sub_le this

  rw[hl1def, hl2def, hr1def, hr2def]
  have hrwlhs: (b + 1) * b * (b - 1) - b * (b - 1) * (b - 2) = 3*b*(b-1) := by
    suffices: (b + 1) * b * (b - 1) = 3*b*(b-1)+b*(b-1)*(b-2)
    . exact (Nat.sub_eq_iff_eq_add hr2lel2).mpr this
    by_cases hbge2: b ≥ 2
    set bp := b-2 with hbpdef
    have hbp1 : b+1 = bp+3 := by
      rw[hbpdef]; simp only [add_left_inj]; exact (Nat.sub_eq_iff_eq_add hbge2).mp hbpdef
    have hbm1 : b-1 = bp+1 := by
      rw[hbpdef]; refine Nat.pred_eq_succ_iff.mpr ?_
      exact (Nat.sub_eq_iff_eq_add hbge2).mp hbpdef
    rw[hbp1, hbm1]; ring

    push_neg at hbge2
    have hb01 : b = 0 ∨ b = 1 := by
      refine Nat.le_one_iff_eq_zero_or_eq_one.mp ?_; exact Nat.le_of_lt_succ hbge2
    rcases hb01 with (hb0 | hb1)
    rw[hb0]; rw[hb1]

  have hrwrhs : (a + 2) * (a + 1) * a - (a + 1) * a * (a - 1) = 3*(a+1)*a := by
    suffices: (a+2)*(a+1)*a = 3*(a+1)*a + (a+1)*a*(a-1)
    . exact (Nat.sub_eq_iff_eq_add hl1ler1).mpr this
    by_cases hage1 : a ≥ 1

    set ap := a-1 with hapdef
    have hap1 : a+1 = ap+2 := by
      rw[hapdef]; refine Nat.add_right_cancel_iff.mpr ?_
      exact (Nat.sub_eq_iff_eq_add hage1).mp hapdef
    have hap2: a+2 = ap+3 := by
      rw[hapdef]; simp only [add_left_inj]
      exact (Nat.sub_eq_iff_eq_add hage1).mp hapdef
    rw[hap1,hap2]; ring

    push_neg at hage1
    have ha0 : a = 0 := by
      exact Nat.lt_one_iff.mp hage1
    rw[ha0]

  rw[hrwlhs, hrwrhs]; refine Nat.mul_le_mul ?_ ?_; refine Nat.mul_le_mul ?_ ?_; rfl
  refine le_trans hageb ?_; exact Nat.le_add_right _ _; refine Nat.sub_le_of_le_add ?_
  refine le_trans hageb ?_; exact Nat.le_add_right _ _

--just rewriting stuff to finish the proof of ineq_2_no_d_near (in the inductive step case)
lemma ineq_2_no_d_near_finish (a b d a1 b1 : ℕ) (hageb: a ≥ b) (hd1leb: d+1 ≤ b)
(ha1eq : a1 = a+d-1) (hb1eq : b1 = b-d-1)
(hle1: (a1 + 1) * a1 * (a1 - 1) + (b1 + 1) * b1 * (b1 - 1) ≤ (a1 + 2) * (a1 + 1) * a1 + b1 * (b1 - 1) * (b1 - 2)):
(a + d) * (a + d - 1) * (a + d - 2) + (b - d) * (b - d - 1) * (b - d - 2) ≤
(a + (d + 1)) * (a + (d + 1) - 1) * (a + (d + 1) - 2) + (b - (d + 1)) * (b - (d + 1) - 1) * (b - (d + 1) - 2) := by
  have hbge1 : b ≥ 1 := by
    refine le_trans ?_ hd1leb
    exact Nat.le_add_left 1 d
  have hage1 : a ≥ 1 := by
    refine ge_trans hageb hbge1
  have hadge1 : a+d ≥ 1 := by
    refine le_trans hage1 ?_; exact Nat.le_add_right a d

  have heqs1: a1+1 = a+d ∧ a1 = a+d-1 ∧ a1-1 = a+d-2 := by
    apply And.intro; rw[ha1eq]
    refine Nat.sub_add_cancel ?_; exact hadge1
    apply And.intro; rw[ha1eq]; rw[ha1eq]; rfl

  have heqs2: b1+1 = b-d ∧ b1 = b-d-1 ∧ b1-1 = b-d-2 := by
    apply And.intro; rw[hb1eq]; refine Nat.sub_add_cancel ?_; exact Nat.le_sub_of_add_le' hd1leb
    apply And.intro; rw[hb1eq]; rw[hb1eq]; rfl

  have heqs3: a1+2 = a+(d+1) ∧ a1+1 = a+(d+1)-1 ∧ a1 = a+(d+1)-2 := by
    apply And.intro; rw[ha1eq];
    have hL : (a+d-1)+2 = (a+d+2)-1 := by
      symm; exact Nat.sub_add_comm hadge1
    rw[hL]; simp only [Nat.add_succ_sub_one]; rfl
    apply And.intro; rw[ha1eq]; refine Nat.sub_add_cancel ?_; exact hadge1
    rw[ha1eq]; rfl

  have heqs4: b1 = b-(d+1) ∧ b1-1 = b-(d+1)-1 ∧ b1-2 = b-(d+1)-2 := by
    apply And.intro; rw[hb1eq]; rfl; apply And.intro; rw[hb1eq]; rfl; rw[hb1eq]; rfl

  nth_rewrite 1 [heqs1.1] at hle1; nth_rewrite 1 [heqs1.2.1] at hle1; nth_rewrite 1 [heqs1.2.2] at hle1
  nth_rewrite 1 [heqs2.1] at hle1; nth_rewrite 1 [heqs2.2.1] at hle1; nth_rewrite 1 [heqs2.2.2] at hle1
  nth_rewrite 1 [heqs3.1] at hle1; nth_rewrite 1 [heqs3.2.1] at hle1; nth_rewrite 1 [heqs3.2.2] at hle1
  nth_rewrite 1 [heqs4.1] at hle1; nth_rewrite 1 [heqs4.2.1] at hle1; nth_rewrite 1 [heqs4.2.2] at hle1
  exact hle1

--instead of using c, use a+d, and prove by induction on d
lemma ineq_2_no_d_near (a b : ℕ) (hageb : a ≥ b): ∀(d : ℕ), d ≤ b →
a*(a-1)*(a-2) + b*(b-1)*(b-2) ≤ (a+d)*(a+d-1)*(a+d-2) + (b-d)*(b-d-1)*(b-d-2) := by
  intro d
  induction' d with d hd

  --case d=0
  intro hdleb
  simp only [add_zero, tsub_zero, le_refl]

  --case general d
  intro hd1leb
  have hdleb : d ≤ b := by
    exact Nat.le_of_succ_le hd1leb
  have hnear := hd hdleb
  refine le_trans hnear ?_
  set a1 := a+d-1 with ha1def; set b1 := b-d-1 with hb1def
  have ha1geb1 : a1 ≥ b1 := by
    dsimp[a1,b1]
    suffices: a+d ≥ b-d
    . exact Nat.sub_le_sub_right this 1
    refine Nat.sub_le_of_le_add ?this.h
    refine le_trans hageb ?_
    rw[add_assoc]; exact Nat.le_add_right a (d + d)
  have hnear2 := pre_ineq a1 b1 ha1geb1
  exact ineq_2_no_d_near_finish a b d a1 b1 hageb hd1leb ha1def hb1def hnear2

--just a, b, and c, but the case a ≥ b
lemma ineq_2_no_d_case_ageb (a b c : ℕ) (halec : a ≤ c) (hblec : b ≤ c) (hcleab : c ≤ a+b) (hageb: a ≥ b):
a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ c*(c-1)*(c-2) + (a+b-c)*(a+b-c-1)*(a+b-c-2) := by
  have hdleb: c-a ≤ b := by
    exact Nat.sub_le_iff_le_add'.mpr hcleab
  have hnear := ineq_2_no_d_near a b hageb (c-a) hdleb
  refine le_trans hnear ?_
  suffices: a+(c-a) = c ∧ b-(c-a) = a+b-c
  . rw[this.1,this.2]
  apply And.intro; exact Nat.add_sub_of_le halec
  refine (Nat.sub_eq_iff_eq_add hdleb).mpr ?_
  rw[add_comm a b]
  rw[add_comm a b] at hcleab
  rw[← @Nat.sub_add_comm (b+a) (c-a) c hcleab]
  refine Nat.eq_sub_of_add_eq ?this.right.h
  suffices: c = a+(c-a)
  . nth_rewrite 1 [this]; rw[add_assoc]
  exact Eq.symm (Nat.add_sub_of_le halec)

--just a, b, and c
lemma ineq_2_no_d (a b c : ℕ) (halec : a ≤ c) (hblec : b ≤ c) (hcleab : c ≤ a+b):
a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ c*(c-1)*(c-2) + (a+b-c)*(a+b-c-1)*(a+b-c-2) := by
  by_cases hageb : a ≥ b

  exact ineq_2_no_d_case_ageb a b c halec hblec hcleab hageb

  have hbgea : b ≥ a := by
    push_neg at hageb; exact Nat.le_of_succ_le hageb
  rw[add_comm a b] at hcleab
  have hnear := ineq_2_no_d_case_ageb b a c hblec halec hcleab hbgea
  rw[add_comm (b*(b-1)*(b-2)) (a*(a-1)*(a-2))] at hnear
  rw[add_comm b a] at hnear; exact hnear

--the main inequality (with d present)
lemma ineq_2 (a b c d : ℕ) (halec : a ≤ c) (hblec : b ≤ c) (habcd : a+b = c+d):
  a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ c*(c-1)*(c-2)+d*(d-1)*(d-2) := by
  have hcleab : c ≤ a+b := by
    rw[habcd]; exact Nat.le_add_right c d
  have hdeq : d = a+b-c := by
    rw[habcd]
    exact Nat.eq_sub_of_add_eq' rfl
  rw[hdeq]
  exact ineq_2_no_d a b c halec hblec hcleab

lemma ineq_1 (a b : ℕ): a*(a-1)*(a-2)+b*(b-1)*(b-2) ≤ (a+b)*(a+b-1)*(a+b-2) := by
  apply ineq_2 a b (a+b) 0 ?_ ?_ ?_
  exact Nat.le_add_right a b; exact Nat.le_add_left b a; rfl

end Inequality
