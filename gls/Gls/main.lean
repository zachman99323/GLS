import Gls.inequality
import Gls.trivial_lemmas_sets
import Gls.graph_definitions
import Gls.trivial_lemmas_graphs
import Gls.basic_properties_of_G0
import Gls.triangle_decomposition
import Gls.misc
import Gls.key_lemma

import Mathlib

open Inequality
open triv_lem_sets
open graph_defs
open trivial_lems_graphs
open properties_of_G0
open triangle_decomp
open miscellany
open keylem

set_option linter.unusedVariables false

open Set
open scoped Classical
open Finset BigOperators

theorem gls_cases012 (n d : ℕ) (hnle2 : n ≤ 2) (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: (G.1).Finite)
(hnvertices: num_vertices G = n) (hmaxdegd : max_deg_le d G) : ∀(q r : ℕ),
n = q*(d+1)+r ∧ 0 ≤ r ∧ r ≤ d →
6*{T : Set ℕ | is_triangle G T}.ncard ≤ q*(d+1)*d*(d-1) + r*(r-1)*(r-2) := by
  intro q r hnqr
  suffices: {T : Set ℕ | is_triangle G T}.ncard = 0
  . rw[this]; simp only [mul_zero, zero_le]
  suffices: {T | is_triangle G T}=∅
  . rw[this]; exact ncard_empty (Set ℕ)
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro T; simp only [mem_setOf_eq]
  contrapose! hnle2
  dsimp[is_triangle] at hnle2
  rcases hnle2 with ⟨x,y,z,⟨h11,h12,h13⟩,h2,h3,h4,h5⟩
  have hxyzvertices : {x,y,z} ⊆ G.1 := by
    intro t ht
    simp only [mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with (tx | tyz)
    rw[tx]; exact (triv_lem_graphs_1 G hGgraph _ _ h3).1
    rcases tyz with (ty | tz)
    rw[ty]; exact (triv_lem_graphs_1 G hGgraph _ _ h3).2
    rw[tz]; exact (triv_lem_graphs_1 G hGgraph _ _ h4).2
  dsimp[num_vertices] at hnvertices
  rw[← hnvertices]
  have h3len : ({x,y,z} : Set ℕ).ncard ≤ G.1.ncard := by
    exact ncard_le_ncard hxyzvertices hGfin
  suffices: ({x,y,z} : Set ℕ).ncard = 3
  . linarith [h3len, this]
  rw[ncard_eq_three]; use x; use y; use z

lemma case_dv1ler_of_gls (n m q d r a b dv : ℕ) (h1 : n = q*(d+1)+r) (h2 : m = n - (dv+1)) (h3 : dv+1 ≤ r) (h4 : r ≤ d)
(h5 : ∀ (q r : ℕ), m = q * (d + 1) + r ∧ 0 ≤ r ∧ r ≤ d → 6 * a ≤ q * (d + 1) * d * (d - 1) + r * (r - 1) * (r - 2))
(h6 : 6*b ≤ (dv+1)*dv*(dv-1)): 6*(a+b) ≤ q*(d+1)*d*(d-1)+r*(r-1)*(r-2) := by
  set rnew := r-((dv)+1) with hrnewdef
  have hm_ind_hyp1 := h5 q rnew
  have hmqrnew : m = q*(d+1)+rnew := by
    dsimp[rnew]
    rw[h2]
    rw[h1]
    exact Nat.add_sub_assoc h3 (q * (d + 1))
  have hrnewge0 : rnew ≥ 0 := Nat.zero_le rnew
  have hrnewled : rnew ≤ d := by
    dsimp[rnew]
    have hnear: r - (dv + 1) ≤ r := by
      exact Nat.sub_le r (dv + 1)
    exact le_trans hnear h4
  have hm_ind_hyp2 := hm_ind_hyp1 ⟨hmqrnew,hrnewge0,hrnewled⟩
  have hnumtrilostle : 6*b ≤ (dv + 1)*(dv)*(dv - 1) := h6
  suffices: q * (d + 1) * d * (d - 1) + rnew * (rnew - 1) * (rnew - 2)
  + (dv + 1) * dv * (dv - 1) ≤ q * (d + 1) * d * (d - 1) + r * (r - 1) * (r - 2)
  . exact triv_lem_ineq_1 _ _ _ _ _ hm_ind_hyp2 hnumtrilostle this
  suffices: rnew * (rnew - 1) * (rnew - 2) + (dv + 1) * dv * (dv - 1) ≤ r * (r - 1) * (r - 2)
  . have hnear := (add_le_add_iff_left (q * (d + 1) * d * (d - 1))).mpr this
    rw[add_assoc]; exact hnear
  have hrnewdv1 : rnew+(dv+1) = r := by
    have hnear := (@Nat.sub_eq_iff_eq_add (dv+1) r rnew h3).mp (Eq.symm hrnewdef)
    symm; exact hnear
  rw[← hrnewdv1]
  exact ineq_1 rnew (dv+1)

lemma case_dv1gtr_of_gls (n m q d r a b dv : ℕ) (h1 : n = q*(d+1)+r) (h2 : m = n - (dv+1)) (h3 : r < dv+1) (h4 : r ≤ d)
(h5 : ∀ (q r : ℕ), m = q * (d + 1) + r ∧ 0 ≤ r ∧ r ≤ d → 6 * a ≤ q * (d + 1) * d * (d - 1) + r * (r - 1) * (r - 2))
(h6 : 6*b ≤ (dv+1)*dv*(dv-1)) (h7: dv ≤ d) (h8: dv+1 ≤ n): 6*(a+b) ≤ q*(d+1)*d*(d-1)+r*(r-1)*(r-2) := by
  have hqge1 : q ≥ 1 := by
    by_contra hq0; push_neg at hq0; simp only [Nat.lt_one_iff] at hq0
    rw[hq0] at h1; rw[zero_mul, zero_add] at h1; rw[← h1] at h3
    exact (not_lt_of_le h8) h3
  let rnew := d+1+r-(dv+1)
  have hm_ind_hyp1 := h5 (q-1) rnew
  have hmqrnew : m = (q-1)*(d+1)+rnew := by
    dsimp[rnew]; rw[h2]; rw[h1]
    apply triv_lem_eq_1
    --show q ≥ 1
    contrapose! h3
    have hq0 : q = 0 := by exact Nat.lt_one_iff.mp h3
    rw[hq0] at h1; rw[zero_mul] at h1; rw[zero_add] at h1; rw[← h1]
    --exact dv1len G hGgraph hGfin v
    exact h8
    /-exact dv1len G hGgraph hGfin v hv.1-/
    exact h7
    --show r ≤ d
    exact h4
    --show dv+1 > r
    exact h3
  have hrnewge0 : rnew ≥ 0 := Nat.zero_le rnew
  have hrnewled : rnew ≤ d := by
    dsimp[rnew]
    simp only [tsub_le_iff_right]
    suffices: 1+r ≤ dv+1
    . rw[add_assoc]
      exact add_le_add_left this d
    exact Nat.one_add_le_iff.mpr h3
  have hm_ind_hyp2 := hm_ind_hyp1 ⟨hmqrnew,hrnewge0,hrnewled⟩
  have hnumtrilostle : 6*b ≤ (dv + 1)*(dv)*(dv - 1) := h6
  suffices: (q - 1) * (d + 1) * d * (d - 1) + rnew * (rnew - 1) * (rnew - 2)
  + (dv + 1) * dv * (dv - 1) ≤ q * (d + 1) * d * (d - 1) + r * (r - 1) * (r - 2)
  . exact triv_lem_ineq_1 _ _ _ _ _ hm_ind_hyp2 hnumtrilostle this
  suffices: rnew * (rnew - 1) * (rnew - 2) + (dv + 1) * dv * (dv - 1) ≤ (d+1)*d*(d-1)+r*(r-1)*(r-2)
  . exact suffices_lem_for_case_dv1gtr_of_gls rnew dv d r q hqge1 this
  have hrnewdv1_eq_d1r : rnew+(dv+1) = d+1+r := by
    dsimp[rnew]
    refine Nat.sub_add_cancel ?h
    have h1le1r : 1 ≤ 1+r := by
      exact Nat.le_add_right 1 r
    rw[add_assoc]
    exact add_le_add h7 h1le1r
  have hrnewled1 : rnew ≤ d+1 := by
    exact Nat.le_succ_of_le hrnewled
  have hdv1led1 : dv+1 ≤ d+1 := by
    exact Nat.add_le_add_right h7 1
  exact ineq_2 rnew (dv+1) (d+1) r hrnewled1 hdv1led1 hrnewdv1_eq_d1r

theorem gls (n d : ℕ) (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite)
(hnvertices: num_vertices G = n) (hmaxdegd : max_deg_le d G) : ∀(q r : ℕ),
n = q*(d+1)+r ∧ 0 ≤ r ∧ r ≤ d →
6*{T : Set ℕ | is_triangle G T}.ncard ≤ q*(d+1)*d*(d-1) + r*(r-1)*(r-2) := by
  induction' n using Nat.strong_induction_on with n h_ind_hyp generalizing G

  by_cases hnle2 : n ≤ 2

  --case n ≤ 2
  exact gls_cases012 n d hnle2 G hGgraph hGfin hnvertices hmaxdegd

  --case n ≥ 3
  push_neg at hnle2
  have hnge3 : n ≥ 3 := by linarith
  rw[← hnvertices] at hnge3
  have hvkeylem := key_lemma G hGgraph hGfin hnge3
  clear hnge3

  rcases hvkeylem with ⟨v,hv⟩

  set G₀ := G₀def G v with hG₀def
  set m := G₀.1.ncard with hmeq
  set dv := deg G v with hdvdef
  dsimp[num_vertices] at hnvertices; symm at hnvertices
  have hnewhyp := ind_hyp_converter n v m G hGgraph hGfin hmaxdegd hnvertices hnle2 hv.1 hmeq h_ind_hyp
  clear h_ind_hyp

  intro q r ⟨hnqr,hrge0,hrled⟩
  have htricount_decomp := tricount_decomp G hGgraph hGfin v
  rw[htricount_decomp]

  set F₁ := {T | is_triangle G₀ T} with hF₁
  set F₂ := {T | is_triangle G T ∧ T ∩ closed_nbhd G v ≠ ∅} with hF₂

  have hmeqndv1 : m = n-(dv+1) := by
    have hnear := G₀numvertices G hGgraph hGfin v hv.1
    dsimp[num_vertices] at hnear; rw[← hnvertices] at hnear; rw[← hmeq] at hnear; rw[← hdvdef] at hnear
    exact hnear

  by_cases hdv1ler : (deg G v) + 1 ≤ r
  . rw[← hdvdef] at hdv1ler
    exact case_dv1ler_of_gls n m q d r F₁.ncard F₂.ncard dv hnqr hmeqndv1 hdv1ler hrled hnewhyp hv.2

  . push_neg at hdv1ler; rw[← hdvdef] at hdv1ler
    have hdvled : dv ≤ d := by
      dsimp[dv]; dsimp[deg]
      have hnear := hmaxdegd v
      have hnear2 := triv_lem_sets_5 G v
      rw[← hnear2]; exact hnear
    have hdv1len := dv1len G hGgraph hGfin v hv.1
    dsimp[num_vertices] at hdv1len; rw[← hnvertices] at hdv1len; rw[← hdvdef] at hdv1len
    exact case_dv1gtr_of_gls n m q d r F₁.ncard F₂.ncard dv hnqr hmeqndv1 hdv1ler hrled hnewhyp hv.2 hdvled hdv1len
