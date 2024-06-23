import Mathlib

import Gls.graph_definitions
import Gls.trivial_lemmas_graphs
import Gls.trivial_lemmas_sets
import Gls.basic_properties_of_G0
import Gls.triangle_decomposition

open graph_defs
open trivial_lems_graphs
open triv_lem_sets
open properties_of_G0
open triangle_decomp

set_option linter.unusedVariables false

open Set
open scoped Classical
open Finset BigOperators

namespace miscellany

lemma triv_lem_ineq_1 (a b c d e : ℕ) (h1: 6*a ≤ c) (h2: 6*b ≤ d) (h3: c+d ≤ e): 6*(a+b) ≤ e := by linarith

lemma triv_lem_eq_1 (q r d dv : ℕ) (h1 : q ≥ 1) (h2 : dv ≤ d) (h3: r ≤ d) (h4: dv+1 > r):
q * (d + 1) + r - (dv + 1) = (q - 1) * (d + 1) + (d + 1 + r - (dv + 1)) := by
  have hq : q*(d+1) = (q-1)*(d+1) + (d+1) := by
    have hnear: (q-1)*(d+1)+(d+1) = ((q-1)+1)*(d+1) := by ring
    rw[hnear]
    congr
    exact (Nat.sub_eq_iff_eq_add h1).mp rfl
  rw[hq]
  rw[add_assoc]
  have hle : dv+1 ≤ d+1+r := by linarith
  exact Nat.add_sub_assoc hle ((q-1)*(d+1))

lemma ind_hyp_converter (n v m : ℕ) (G : Set ℕ × Set (Set ℕ)) (hGgraph : is_graph G) (hGfin: G.1.Finite)
(hmaxdegd : max_deg_le d G) (hneq : n = G.1.ncard) (hnge2 : 2 < n) (hvinG : v ∈ G.1) (hmeq : m = (G₀def G v).1.ncard)
(hindhyp : ∀m < n, ∀(G : Set ℕ × Set (Set ℕ)), is_graph G → G.1.Finite → num_vertices G = m → max_deg_le d G →
∀ (q r : ℕ), m = q*(d+1)+r ∧ 0 ≤ r ∧ r ≤ d → 6 * {T | is_triangle G T}.ncard ≤ q * (d + 1) * d * (d - 1) + r * (r - 1) * (r - 2)) :
∀ (q r : ℕ), m = q * (d + 1) + r ∧ 0 ≤ r ∧ r ≤ d →
6 * {T | is_triangle (G₀def G v) T}.ncard ≤ q * (d + 1) * d * (d - 1) + r * (r - 1) * (r - 2) := by
  set G₀ := G₀def G v with hG₀def
  have hG₀isgraph := G₀graph G hGgraph v
  have hG₀nvltn := G₀numvertices G hGgraph hGfin v hvinG
  set dv := deg G v with hdvdef
  have hmeq2 : m = n-(dv+1):= by
    rw[hmeq]; rw[hneq]
    exact G₀numvertices G hGgraph hGfin v hvinG
  have hmltn : m < n := by
    rw[hmeq2];
    refine Nat.sub_lt ?_ ?_
    exact Nat.zero_lt_of_lt hnge2
    exact Nat.zero_lt_succ dv
  have hG₀subG := G₀subG G hGgraph v
  have hG₀1subG1 : G₀.1 ⊆ G.1 := by
    dsimp[G₀]; dsimp[G₀def]; exact diff_subset
  have hG₀fin : G₀.1.Finite := by
    exact Finite.subset hGfin hG₀1subG1
  have hG₀maxdegled := G₀maxdeg d G hGgraph hGfin hmaxdegd v
  exact hindhyp m hmltn G₀ hG₀isgraph hG₀fin (Eq.symm hmeq) hG₀maxdegled

lemma suffices_lem_for_case_dv1gtr_of_gls (rnew dv d r q : ℕ) (hqge1 : q ≥ 1)
(h : rnew * (rnew - 1) * (rnew - 2) + (dv + 1) * dv * (dv - 1) ≤ (d + 1) * d * (d - 1) + r * (r - 1) * (r - 2)):
(q - 1) * (d + 1) * d * (d - 1) + rnew * (rnew - 1) * (rnew - 2) + (dv + 1) * dv * (dv - 1) ≤
  q * (d + 1) * d * (d - 1) + r * (r - 1) * (r - 2) := by
  have hq_eq_q1_1 : q = (q-1)+1 := by
    exact (Nat.sub_eq_iff_eq_add hqge1).mp rfl
  nth_rewrite 2 [hq_eq_q1_1]
  linarith

end miscellany
