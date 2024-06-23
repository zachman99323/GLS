import Mathlib

import Gls.graph_definitions
import Gls.trivial_lemmas_graphs
import Gls.trivial_lemmas_sets
import Gls.basic_properties_of_G0
import Gls.triangle_decomposition
import Gls.key_equality

open graph_defs
open trivial_lems_graphs
open triv_lem_sets
open properties_of_G0
open triangle_decomp
open keyeq

set_option linter.unusedVariables false

open Set
open scoped Classical
open Finset BigOperators

-- lemma wgraph_trivial_ineq_1 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite):
-- (Wgraph G).ncard ≥
-- ∑ x ∈ (Finite.toFinset hGfin),
-- ({(u,v,w) : ℕ×ℕ×ℕ | {u,x} ∈ G.2 ∧ {v,x} ∈ G.2 ∧ {w,x} ∈ G.2 ∧ {u,v} ∉ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∉ G.2}).ncard := by
--   have hnear1 := wgraph_trivial_ineq_0 G hGgraph hGfin
--   rw[hnear1]

--   set F := {A | ∃ x ∈ G.1, W1 G x = A} with hFdef
--   have hFfin : F.Finite := by
--     exact Finite.of_surjOn (fun x ↦ W1 G x) (fun ⦃a⦄ a ↦ a) hGfin
--   have hnear2 := ncard_of_disjoint_sUnion F hFfin ?_ ?_
--   rw[hnear2]

--   set F1 := Finite.toFinset hFfin with hF1def
--   set G1 := Finite.toFinset hGfin with hG1def

--   have hW1eqmarg1 : ∀(w1: ℕ), marginal1 (Wgraph G) w1 = W1 G w1 := by
--       intro w1; ext a; apply Iff.intro; intro ha; dsimp[marginal1] at ha; dsimp[W1]
--       rcases ha.2 with ⟨x,y,z,hxyz⟩; use x; use y; use z; use hxyz; have ha1 := ha.1
--       dsimp[Wgraph] at ha1; rw[hxyz] at ha1; exact ha1
--       intro ha; dsimp[W1] at ha; dsimp[marginal1]; rcases ha with ⟨x,y,z,hxyz⟩
--       apply And.intro; swap; use x; use y; use z; exact hxyz.1
--       dsimp[Wgraph]; rw[hxyz.1]; exact hxyz.2

--   have hproj1Wfin : (proj1 (Wgraph G)).Finite := by
--     suffices: proj1 (Wgraph G) ⊆ G.1
--     . exact Finite.subset hGfin this
--     intro w hw; dsimp[proj1] at hw; rcases hw with ⟨x,y,z,hxyz⟩; dsimp[Wgraph] at hxyz
--     exact (triv_lem_graphs_1 G hGgraph x w hxyz.1).2

--   set H := {A | ∃ x ∈ proj1 (Wgraph G), W1 G x = A} with hHdef
--   have hHsubF : H ⊆ F := by
--     rw[hHdef,hFdef]
--     intro A hA; simp only [mem_setOf_eq] at hA; rcases hA with ⟨x,hx⟩
--     simp only [mem_setOf_eq]; use x; apply And.intro; swap; exact hx.2
--     have hx1 := hx.1; clear hx; dsimp[proj1] at hx1; rcases hx1 with ⟨x2,y,z,hx2yz⟩
--     dsimp[Wgraph] at hx2yz; exact (triv_lem_graphs_1 G hGgraph x2 x hx2yz.1).2
--   have hHfin : H.Finite := by
--     suffices: H ⊆ F
--     . exact Finite.subset hFfin this
--     exact hHsubF
--   set H1 := Finite.toFinset hHfin with hH1def
--   have hnear3 : ∑ A ∈ H1, A.ncard = ∑ x ∈ Finite.toFinset (hproj1Wfin) , (W1 G x).ncard := by
--     have hWfin : (Wgraph G).Finite := by
--       exact Wfinite G hGgraph hGfin
--     have hproj1G1 : proj1 (Wgraph G) ⊆ G.1 := by
--       intro w; intro hw; dsimp[proj1] at hw; rcases hw with ⟨x,y,z,hxyz⟩
--       dsimp[Wgraph] at hxyz; exact (triv_lem_graphs_1 G hGgraph x w hxyz.1).2
--     have hproj1G1_finsets : Finite.toFinset (@Afin_imp_proj1Afin ℕ 1 (Wgraph G) hWfin) ⊆ G1 := by
--       exact Finite.toFinset_subset_toFinset.mpr hproj1G1

--     have hnear := @change_summation_index ℕ 1 (Wgraph G) hWfin H ?_ hHfin
--     rw[← hH1def] at hnear; rw[hnear]
--     congr with w
--     congr
--     exact hW1eqmarg1 w

--     dsimp[H]; simp[hW1eqmarg1]
--     ext B; apply Iff.intro; intro hB; simp only [mem_setOf_eq]; simp only [mem_setOf_eq] at hB
--     rcases hB with ⟨w,hw⟩; use w; use hw.1; exact (Eq.symm hw.2); intro hB; simp only [mem_setOf_eq] at hB
--     rcases hB with ⟨w,hw⟩; use w; use hw.1; exact (Eq.symm hw.2)

--   have hnear4 : ∑ A ∈ F1, A.ncard = ∑ A ∈ H1, A.ncard := by
--     have hH1subF1 : H1 ⊆ F1 := by
--       exact Finite.toFinset_subset_toFinset.mpr hHsubF

--     symm; apply Finset.sum_subset_zero_on_sdiff hH1subF1 ?_ ?_

--     swap; intro x hx; rfl

--     --show A.ncard = 0 for all A in F1\H1
--     intro A hA; rw[mem_sdiff] at hA; have hA1 := hA.1; have hA2 := hA.2; clear hA
--     dsimp[F1] at hA1; dsimp[H1] at hA2; simp only [Finite.mem_toFinset] at hA1
--     simp only [Finite.mem_toFinset] at hA2; dsimp[F] at hA1; dsimp[H] at hA2; push_neg at hA2
--     rcases hA1 with ⟨w,hw1,hw2⟩
--     have hwninproj1 : w ∉ proj1 (Wgraph G) := by
--       by_contra hcontra
--       have h := hA2 w hcontra; exact h hw2
--     have hcorr: W1 G w = ∅ := by
--       contrapose! hwninproj1
--       rcases hwninproj1 with ⟨a,ha⟩; dsimp[W1] at ha; rcases ha with ⟨x,y,z,hxyz1,hxyz2⟩
--       dsimp[proj1]; use x; use y; use z; dsimp[Wgraph]; exact hxyz2
--     rw[← hw2]; rw[hcorr]; exact ncard_empty (ℕ × ℕ × ℕ × ℕ)

--   rw[hnear4]; rw[hnear3]
--   set X1 := Finite.toFinset hproj1Wfin

--   have hnear5 : ∑ x ∈ X1, (W1 G x).ncard = ∑ x ∈ G1, (W1 G x).ncard := by
--     have hX1subG1 : X1 ⊆ G1 := by
--       intro x hx; dsimp[X1] at hx; dsimp[G1]; simp only [Finite.mem_toFinset] at hx
--       simp only [Finite.mem_toFinset]; dsimp[proj1] at hx; rcases hx with ⟨x1,y,z,hx1yz1,hx1yz2⟩
--       exact (triv_lem_graphs_1 G hGgraph x1 x hx1yz1).2

--     apply Finset.sum_subset_zero_on_sdiff hX1subG1 ?_ ?_

--     swap; intro x hx; rfl

--     intro x hx; rw[mem_sdiff] at hx; have hx1 := hx.1; have hx2 := hx.2; clear hx
--     dsimp[G1] at hx1; dsimp[X1] at hx2; simp only [Finite.mem_toFinset] at hx1
--     simp only [Finite.mem_toFinset] at hx2; dsimp[proj1] at hx2; push_neg at hx2
--     have hemp : W1 G x = ∅ := by
--       contrapose! hx2
--       rcases hx2 with ⟨a,ha⟩; dsimp[W1] at ha; rcases ha with ⟨x1,y,z,hx1yz1,hx1yz2⟩
--       use x1; use y; use z; dsimp[Wgraph]; exact hx1yz2
--     rw[hemp]; exact ncard_empty (ℕ × ℕ × ℕ × ℕ)


--   rw[hnear5]
--   gcongr with x hxinG1
--   exact trivial_ncard_ineq G hGgraph hGfin x

--   --show ∀A ∈ F, ∀B ∈ F, A ≠ B → Disjoint A B
--   intro A hA B hB hAneB; dsimp[F] at hA; dsimp[F] at hB
--   rcases hA with ⟨xA,hxA1,hxA2⟩; rcases hB with ⟨xB,hxB1,hxB2⟩
--   rw[← hxA2, ← hxB2]
--   have hnear: ∀ a ∈ W1 G xA, a ∉ W1 G xB := by
--     intro ⟨x1,u1,v1,w1⟩ h1
--     dsimp[W1] at h1
--     rcases h1 with ⟨u,v,w,h1,h2⟩
--     have hx1xA : x1 = xA := by injections
--     contrapose! hx1xA
--     dsimp[W1] at hx1xA; rcases hx1xA with ⟨u3,v3,w3,h31,h32⟩
--     have hx1xB : x1 = xB := by
--       injection h31
--     rw[hx1xB]; contrapose! hAneB
--     rw[← hxA2, ← hxB2]; rw[hAneB]
--   exact Set.disjoint_left.mpr hnear

--   --show: ∀ A ∈ F, A.Finite
--   intro A hA; dsimp[F] at hA; rcases hA with ⟨x,hx1,hx2⟩; rw[← hx2]
--   exact W1finite G hGgraph hGfin x
