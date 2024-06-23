import Mathlib

import Gls.graph_definitions
import Gls.trivial_lemmas_graphs
import Gls.trivial_lemmas_sets

open graph_defs
open trivial_lems_graphs
open triv_lem_sets

set_option linter.unusedVariables false

open Set
open scoped Classical
open Finset BigOperators

namespace properties_of_G0


def G₀def (G : Set ℕ × Set (Set ℕ)) (v : ℕ) : Set ℕ × Set (Set ℕ) :=
(G.1 \ (closed_nbhd G v) , {e : Set ℕ | ∃(x y : ℕ), e = {x,y} ∧ e ∈ G.2 ∧ x ∉ closed_nbhd G v ∧ y ∉ closed_nbhd G v})

lemma G₀graph (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (v : ℕ): is_graph (G₀def G v) := by
  dsimp[is_graph]; intro e heinG₀;
  dsimp[G₀def] at heinG₀
  rcases heinG₀ with ⟨x,y,h1,h2,h3,h4⟩; rw[h1] at h2
  have hxG1 := triv_lem_graphs_1 G hGgraph x y h2
  use x; use y; apply And.intro; dsimp[G₀def]; tauto
  apply And.intro; dsimp[G₀def]; tauto; apply And.intro
  exact triv_lem_graphs_2 G hGgraph x y h2; exact h1

lemma G₀vertices (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (v : ℕ) : (G₀def G v).1 = G.1\(closed_nbhd G v) := by
  dsimp[G₀def]

lemma nbhd_fin (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: (G.1).Finite) (v : ℕ) :
{u : ℕ | {u,v} ∈ G.2}.Finite := by
  suffices: {u : ℕ | {u,v} ∈ G.2} ⊆ G.1
  . exact Finite.subset hGfin this
  intro u hu; rw[mem_setOf_eq] at hu
  exact (triv_lem_graphs_1 G hGgraph u v hu).1

lemma dv1len (G : Set ℕ × Set (Set ℕ)) (hGgraph : is_graph G) (hGfin: G.1.Finite) (v : ℕ) (hvinG : v ∈ G.1):
deg G v +1 ≤ num_vertices G := by
  dsimp[deg]
  dsimp[num_vertices]
  have hvnotinnbhd : v ∉ {u | {u,v} ∈ G.2} := by
    by_contra hcontra; simp only [mem_setOf_eq, mem_singleton_iff, Set.insert_eq_of_mem] at hcontra
    have hcontra2 := hGgraph {v} hcontra; rcases hcontra2 with ⟨x,y,hxy3,hxy4,hxy1,hxy2⟩
    contrapose! hxy1
    have hxv : x = v := by
      have hxinxy := (triv_lem_1 x y).1
      rw[← hxy2] at hxinxy; exact hxinxy
    have hyv : y = v := by
      have hyinxy := (triv_lem_1 x y).2
      rw[← hxy2] at hyinxy; exact hyinxy
    rw[hxv,hyv]
  set Nv := {v} ∪ {u | {u,v} ∈ G.2} with hNvdef
  have hNvncard : Nv.ncard = deg G v + 1 := by
    dsimp[Nv]
    exact Set.ncard_insert_of_not_mem hvnotinnbhd (nbhd_fin G hGgraph hGfin v)
  dsimp[deg] at hNvncard
  rw[← hNvncard]
  suffices: Nv ⊆ G.1
  . exact Set.ncard_le_ncard this hGfin
  intro u hu; dsimp[Nv] at hu; simp only [mem_insert_iff,mem_setOf_eq] at hu
  rcases hu with (huv | hunv)
  rw[huv]; exact hvinG
  exact (triv_lem_graphs_1 G hGgraph u v hunv).1

lemma G₀numvertices (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite) (v : ℕ) (hvinG : v ∈ G.1):
num_vertices (G₀def G v) = num_vertices G - ((deg G v) + 1) := by
  set G₀ := G₀def G v with hG₀def
  set Nv := closed_nbhd G v with hNvdef
  set dv := deg G v with hdvdef
  have hndecomp := G₀vertices G hGgraph v
  have hsub : Nv ⊆ G.1 := by
    intro u hu; dsimp[Nv] at hu; dsimp[closed_nbhd] at hu; simp only [mem_insert_iff,mem_setOf_eq] at hu
    rcases hu with (huv | hunv)
    rw[huv]; exact hvinG
    exact (triv_lem_graphs_1 G hGgraph u v hunv).1
  have hnear := Set.ncard_diff hsub hGfin
  rw[← hndecomp] at hnear
  rw[← hG₀def] at hnear
  dsimp[num_vertices]
  suffices: Nv.ncard = dv + 1
  . rw[this] at hnear; exact hnear
  rw[hdvdef]; dsimp[deg]; dsimp[Nv]; dsimp[closed_nbhd]
  have hnbhdfin : {u | {u,v} ∈ G.2}.Finite := by
    exact nbhd_fin G hGgraph hGfin v
  suffices: v ∉ {u | {u,v} ∈ G.2}
  . exact Set.ncard_insert_of_not_mem this hnbhdfin
  by_contra hcontra; simp only [mem_setOf_eq, mem_singleton_iff, Set.insert_eq_of_mem] at hcontra
  have hcontra2 := hGgraph {v} hcontra; rcases hcontra2 with ⟨x,y,hxy3,hxy4,hxy1,hxy2⟩
  contrapose! hxy1
  have hxv : x = v := by
    have hxinxy := (triv_lem_1 x y).1
    rw[← hxy2] at hxinxy; exact hxinxy
  have hyv : y = v := by
    have hyinxy := (triv_lem_1 x y).2
    rw[← hxy2] at hyinxy; exact hyinxy
  rw[hxv,hyv]

lemma G₀subG (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (v : ℕ) : (G₀def G v).2 ⊆ G.2 := by
  set G₀ := G₀def G v with hG₀def
  intro e he
  dsimp[G₀] at he
  rcases he with ⟨x,y,hxy1,hxy2,hxy3,hxy4⟩
  exact hxy2

lemma G₀maxdeg (d : ℕ) (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: (G.1).Finite) (hmaxdegd : max_deg_le d G) (v : ℕ) : max_deg_le d (G₀def G v) := by
  dsimp[max_deg_le]; intro x
  set G₀ := G₀def G v with hG₀def
  have hG₀subG := G₀subG G hGgraph v
  have hnbhdsub : {y | {x, y} ∈ G₀.2} ⊆ {y | {x,y} ∈ G.2} := by
    intro y hy; rw[mem_setOf_eq] at hy; rw[mem_setOf_eq]
    exact hG₀subG hy
  have hnbhdled : {y | {x,y} ∈ G.2}.ncard ≤ d := by
    exact hmaxdegd x
  have hnbhdfin : {y | {x,y} ∈ G.2}.Finite := by
    let f : ℕ → Set ℕ := fun y ↦ {x,y}
    have hfInjOn : InjOn f {y | {x,y} ∈ G.2} := by
      dsimp[InjOn]
      intro x1 hx1 x2 hx2 hfx1x2
      dsimp[f] at hfx1x2
      exact triv_lem_sets_1 G hGgraph x x1 x2 hx1 hfx1x2
    have hfrangesubG: f '' {y | {x,y} ∈ G.2} ⊆ G.2 := by
      intro e he
      dsimp[f] at he; simp only [Set.mem_image, mem_setOf_eq] at he
      rcases he with ⟨x1,hx11,hx12⟩
      rw[← hx12]; exact hx11
    have hfrangefin : (f '' {y | {x,y} ∈ G.2}).Finite := by
      exact Finite.subset (G1fin_imp_G2fin G hGgraph hGfin) hfrangesubG
    exact (Set.finite_image_iff hfInjOn).mp hfrangefin
  have hnear := ncard_le_ncard hnbhdsub hnbhdfin
  linarith

end properties_of_G0
