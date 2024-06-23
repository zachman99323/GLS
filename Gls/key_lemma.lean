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

namespace keylem

--W(G) = {(x,u, v,w) : ux, vx,wx ∈ E,uv,uw, vw ∉ E}.

lemma triv_identity_0 (x : ℕ) (hxge1: x ≥ 1): (x+1)*(x-1) = x^2-1 := by
  suffices: (x+1)*(x-1)+1 = x^2
  . symm; apply Nat.sub_eq_of_eq_add; symm; exact this
  set y := x-1 with hydef
  have hxeqy1 : x = y+1 := by
    rw[hydef]; symm; exact Nat.sub_add_cancel hxge1
  rw[hxeqy1]
  ring

lemma triv_identity_1 (x : ℕ): x^3 = (x+1)*x*(x-1)+x := by
  by_cases hx0 : x = 0
  rw[hx0]; simp
  push_neg at hx0
  have hxge1 : x ≥ 1 := by
    exact Nat.one_le_iff_ne_zero.mpr hx0
  have h : (x+1)*(x-1)+1 = x^2 := by
    refine Eq.symm ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add h).mp) ?h ?_)
    exact Nat.one_le_pow 2 x hxge1
    symm
    exact triv_identity_0 x hxge1
  symm
  calc
    (x+1)*x*(x-1)+x = (x+1)*(x-1)*x+x := by ring
    _= ((x+1)*(x-1)+1)*x := by ring
    _= x^2*x := by rw[h]
    _= x^3 := by ring

lemma Wfinite (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite):
(Wgraph G).Finite := by

  have hnear1 : Wgraph G ⊆ G.1 ×ˢ G.1 ×ˢ G.1 ×ˢ G.1  := by
    intro (x,u,v,w) hxuvw; simp only [mem_prod]
    dsimp[Wgraph] at hxuvw
    use (triv_lem_graphs_1 G hGgraph u x hxuvw.1).2
    use (triv_lem_graphs_1 G hGgraph u x hxuvw.1).1
    use (triv_lem_graphs_1 G hGgraph v x hxuvw.2.1).1
    exact (triv_lem_graphs_1 G hGgraph w x hxuvw.2.2.1).1

  refine Set.Finite.subset ?_ hnear1
  refine Finite.prod hGfin ?_; refine Finite.prod hGfin ?_
  refine Finite.prod hGfin ?_; exact hGfin

lemma Wxfinite (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite) (x : ℕ):
{(u, v, w) | {u, x} ∈ G.2 ∧ {v, x} ∈ G.2 ∧ {w, x} ∈ G.2 ∧ {u,v} ∉ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∉ G.2}.Finite := by
  have hnear := Wfinite G hGgraph hGfin

  let f : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ := fun (u,v,w) ↦ (x,u,v,w)

  refine @Set.Finite.of_finite_image _ _ _ f ?_ ?_

  --show image of f is finite
  suffices: f '' {(u, v, w) | {u, x} ∈ G.2 ∧ {v, x} ∈ G.2 ∧ {w, x} ∈ G.2 ∧ {u,v} ∉ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∉ G.2} ⊆ Wgraph G
  . exact Finite.subset hnear this
  intro a ha; simp only [Set.mem_image, mem_setOf_eq, Prod.exists] at ha
  rcases ha with ⟨u,v,w,huvw1,huvw2⟩; dsimp[f] at huvw2
  rw[← huvw2]; exact huvw1

  --show f injective
  intro (u1,v1,w1) hu1v1w1 (u2,v2,w2) hu2v2w2 hf12
  dsimp[f] at hf12; injection hf12

def W1 (G : Set ℕ × Set (Set ℕ)) (x : ℕ) : Set (ℕ × ℕ × ℕ × ℕ) :=
{a : ℕ × ℕ × ℕ × ℕ | ∃(u v w : ℕ), a = (x,u,v,w) ∧
{u,x} ∈ G.2 ∧ {v,x} ∈ G.2 ∧ {w,x} ∈ G.2 ∧ {u,v} ∉ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∉ G.2}

lemma W1finite (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite) (x : ℕ):
(W1 G x).Finite := by
  have hnear := Wfinite G hGgraph hGfin
  suffices: W1 G x ⊆ Wgraph G
  . exact Finite.subset hnear this
  intro ⟨x1,u1,v1,w1⟩ h; dsimp[W1] at h
  rcases h with ⟨u,v,w,huvw1,huvw2⟩
  rw[huvw1]; exact huvw2

lemma wgraph_trivial_ineq_0 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite):
Wgraph G = ⋃₀{A | ∃x ∈ G.1, W1 G x = A} := by
  apply Set.Subset.antisymm

  intro ⟨x,u,v,w⟩ ha
  simp only [mem_sUnion, mem_setOf_eq, exists_exists_and_eq_and]
  use x
  apply And.intro
  dsimp[Wgraph] at ha; have hux := ha.1; exact (triv_lem_graphs_1 G hGgraph u x hux).2
  dsimp[W1]; use u; use v; use w
  exact ⟨rfl, ha⟩

  intro ⟨x,u,v,w⟩ ha; simp only [mem_sUnion, mem_setOf_eq, exists_exists_and_eq_and] at ha
  rcases ha with ⟨y,hy1,hy2⟩
  dsimp[W1] at hy2
  rcases hy2 with ⟨u1,v1,w1,h1,h2⟩
  rw[h1]; exact h2

lemma trivial_ncard_ineq (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite) (x : ℕ):
{(u, v, w) | {u, x} ∈ G.2 ∧ {v, x} ∈ G.2 ∧ {w, x} ∈ G.2 ∧ {u, v} ∉ G.2 ∧ {u, w} ∉ G.2 ∧ {v, w} ∉ G.2}.ncard ≤
(W1 G x).ncard := by

  set f : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ := fun (u,v,w) ↦ (x,u,v,w)
  apply Set.ncard_le_ncard_of_injOn f ?_ ?_ ?_

  intro ⟨u,v,w⟩ ha; simp only [mem_setOf_eq] at ha
  dsimp[f]; dsimp[W1]; use u; use v; use w

  intro ⟨u1,v1,w1⟩ h1 ⟨u2,v2,w2⟩ h2 hf12; dsimp[f] at hf12
  injections hxx hu1u2 hu1u2 hv1v1 hv1v2 hw1w2; refine Prod.mk.inj_iff.mpr ?_; use hu1u2
  exact Prod.ext hv1v2 hw1w2

  exact W1finite G hGgraph hGfin x

lemma wgraph_trivial_ineq_1 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite):
(Wgraph G).ncard =
∑ x ∈ (Finite.toFinset hGfin),
({(u,v,w) : ℕ×ℕ×ℕ | {u,x} ∈ G.2 ∧ {v,x} ∈ G.2 ∧ {w,x} ∈ G.2 ∧ {u,v} ∉ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∉ G.2}).ncard := by

  have hnear := @ncard_projections_2 ℕ 1 (Wgraph G) (Wfinite G hGgraph hGfin) G.1 hGfin ?_
  rw[hnear]; congr with w
  exact @ncard_projections_trivial ℕ 1 (Wgraph G) (Wfinite G hGgraph hGfin) w

  intro w hw; dsimp[proj1] at hw; rcases hw with ⟨x,y,z,hxyz⟩; dsimp[Wgraph] at hxyz
  exact (triv_lem_graphs_1 G hGgraph x w hxyz.1).2

lemma wgraph_trivial_ineq (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite):
(Wgraph G).ncard ≥ ∑ x ∈ (Finite.toFinset hGfin), deg G x := by

  have hnear1 := wgraph_trivial_ineq_1 G hGgraph hGfin
  rw[hnear1]
  gcongr with x hx
  rw[deg]

  set f : ℕ → ℕ × ℕ × ℕ := fun u ↦ (u,u,u) with hfdef
  refine Set.ncard_le_ncard_of_injOn f ?_ ?_ ?_

  --show f maps LHS into RHS
  intro u hu; rw[mem_setOf_eq] at hu
  simp only [mem_setOf_eq, and_self]; use hu; use hu; use hu
  by_contra huu
  have hnear2 := triv_lem_graphs_2 G hGgraph u u huu; exact hnear2 rfl

  --show f is injective on LHS
  intro u1 hu1 u2 hu2 hfu1u2; rw[mem_setOf_eq] at hu1; rw[mem_setOf_eq] at hu2
  rw[hfdef] at hfu1u2; simp only [Prod.mk.injEq, and_self] at hfu1u2; exact hfu1u2

  --show RHS finite
  exact Wxfinite G hGgraph hGfin x

lemma avg_nbhd_ineq (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite) (hnge3 : num_vertices G ≥ 3):
∑ v ∈ (Finite.toFinset hGfin), 6*{T : Set ℕ | (is_triangle G T) ∧ (T ∩ closed_nbhd G v ≠ ∅)}.ncard
≤ ∑ v ∈ (Finite.toFinset hGfin), ((deg G v)+1)*(deg G v)*((deg G v)-1) := by

  have heq := key_equality G hGgraph hGfin
  have htriv_ineq := wgraph_trivial_ineq G hGgraph hGfin

  set A := ∑ v ∈ (Finite.toFinset hGfin), 6*{T : Set ℕ | (is_triangle G T) ∧ (T ∩ closed_nbhd G v ≠ ∅)}.ncard with hAdef

  suffices: A+(Wgraph G).ncard ≤ ∑ v ∈ hGfin.toFinset, (deg G v + 1) * deg G v * (deg G v - 1) + (Wgraph G).ncard
  . exact Nat.add_le_add_iff_right.mp this

  rw[heq]

  have hsplitcube : ∑ v ∈ hGfin.toFinset, deg G v ^ 3 =
  ∑ v ∈ hGfin.toFinset, (deg G v + 1)*(deg G v)*(deg G v - 1) + ∑ v ∈ hGfin.toFinset, deg G v := by
    rw[← Finset.sum_add_distrib]
    congr; ext v
    exact triv_identity_1 (deg G v)

  rw[hsplitcube]
  apply Nat.add_le_add_iff_left.mpr
  exact htriv_ineq

theorem key_lemma (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite) (hnge3: num_vertices G ≥ 3): ∃(v : ℕ), v ∈ G.1 ∧
6*{T : Set ℕ | (is_triangle G T) ∧ (T ∩ closed_nbhd G v ≠ ∅)}.ncard ≤ ((deg G v)+1)*(deg G v)*((deg G v)-1) := by

  have hnear := avg_nbhd_ineq G hGgraph hGfin hnge3

  set G1f := Finite.toFinset hGfin with hG1fdef

  contrapose! hnear

  refine Finset.sum_lt_sum_of_nonempty ?_ ?_

  --show G1f.Nonempty
  dsimp[num_vertices] at hnge3
  apply (Set.Finite.toFinset_nonempty hGfin).mpr
  refine Set.nonempty_of_ncard_ne_zero ?_
  exact Nat.not_eq_zero_of_lt hnge3

  --show pointwise inequality, but for v in G1f instead of v in G.1
  intro u hu
  have huinG1 : u ∈ G.1 := by
    rw[hG1fdef] at hu
    simp only [Finite.mem_toFinset] at hu
    exact hu
  exact hnear u huinG1

end keylem
