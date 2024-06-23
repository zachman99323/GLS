import Mathlib

import Gls.graph_definitions
import Gls.trivial_lemmas_graphs
import Gls.trivial_lemmas_sets
import Gls.basic_properties_of_G0

open graph_defs
open trivial_lems_graphs
open triv_lem_sets
open properties_of_G0

set_option linter.unusedVariables false

open Set
open scoped Classical
open Finset BigOperators

namespace triangle_decomp

lemma tri_decomp_part_1 (G : Set ℕ × Set (Set ℕ)) (hGgraph : is_graph G) (v : ℕ) :
{T | is_triangle G T} ⊆ {T | is_triangle (G₀def G v) T} ∪ {T | is_triangle G T ∧ T ∩ closed_nbhd G v ≠ ∅} := by
  set G₀ := G₀def G v with hG₀def
  intro T hT; simp at hT; simp
  by_contra hcontra; push_neg at hcontra
  have hcontra1 := hcontra.1; have hcontra2 := hcontra.2; clear hcontra
  contrapose! hcontra1
  have hcontra := hcontra2 hT; clear hcontra2; clear hcontra1
  set Nv := closed_nbhd G v with hNvdef
  dsimp[is_triangle] at hT; rcases hT with ⟨x,y,z,⟨hxney,hxnez,hynez⟩,hT,hxyG₀,hxzG₀,hyzG₀⟩
  dsimp[is_triangle]; use x; use y; use z; apply And.intro; tauto
  apply And.intro; tauto; apply And.intro
  . dsimp[G₀]; dsimp[G₀def]; use x; use y; apply And.intro; tauto; apply And.intro; tauto
    contrapose hcontra
    have hcontraequiv : x ∈ Nv ∨ y ∈ Nv := by
      rw[← hNvdef] at hcontra
      exact Decidable.or_iff_not_and_not.mpr hcontra
    push_neg
    rcases hcontraequiv with (hxNv | hyNv); use x; apply And.intro; rw[hT]; tauto; tauto
    use y; apply And.intro; rw[hT]; tauto; tauto
  . apply And.intro
    . dsimp[G₀]; dsimp[G₀def]; use x; use z; apply And.intro; tauto; apply And.intro; tauto
      contrapose hcontra
      have hcontraequiv : x ∈ Nv ∨ z ∈ Nv := by
        rw[← hNvdef] at hcontra
        exact Decidable.or_iff_not_and_not.mpr hcontra
      push_neg
      rcases hcontraequiv with (hxNv | hyNv); use x; apply And.intro; rw[hT]; tauto; tauto
      use z; apply And.intro; rw[hT]; tauto; tauto
    . dsimp[G₀]; dsimp[G₀def]; use y; use z; apply And.intro; tauto; apply And.intro; tauto
      contrapose hcontra
      have hcontraequiv : y ∈ Nv ∨ z ∈ Nv := by
        rw[← hNvdef] at hcontra
        exact Decidable.or_iff_not_and_not.mpr hcontra
      push_neg
      rcases hcontraequiv with (hxNv | hyNv); use y; apply And.intro; rw[hT]; tauto; tauto
      use z; apply And.intro; rw[hT]; tauto; tauto

lemma tri_decomp_part_2 (G : Set ℕ × Set (Set ℕ)) (hGgraph : is_graph G) (v : ℕ) :
{T | is_triangle (G₀def G v) T} ∪ {T | is_triangle G T ∧ T ∩ closed_nbhd G v ≠ ∅} ⊆ {T | is_triangle G T} := by
  set G₀ := G₀def G v with hG₀def
  intro T hT; simp at hT; rcases hT with (hT1 | hT2)
  simp; dsimp[is_triangle] at hT1; rcases hT1 with ⟨x,y,z,⟨hxney,hxnez,hynez⟩,hT,hxyG₀,hxzG₀,hyzG₀⟩
  use x; use y; use z; apply And.intro; tauto; apply And.intro; tauto
  have hxyG := (G₀subG G hGgraph v) hxyG₀
  have hxzG := (G₀subG G hGgraph v) hxzG₀
  have hyzG := (G₀subG G hGgraph v) hyzG₀
  tauto
  simp; tauto

lemma tri_decomp (G : Set ℕ × Set (Set ℕ)) (hGgraph : is_graph G) (v : ℕ) :
{T | is_triangle G T} = {T | is_triangle (G₀def G v) T} ∪ {T | is_triangle G T ∧ T ∩ closed_nbhd G v ≠ ∅} := by
  set G₀ := G₀def G v with hG₀def
  apply Set.Subset.antisymm
  exact tri_decomp_part_1 G hGgraph v
  exact tri_decomp_part_2 G hGgraph v

lemma tri_disjoint (G : Set ℕ × Set (Set ℕ)) (hGgraph : is_graph G) (v : ℕ):
{T | is_triangle (G₀def G v) T} ∩ {T | is_triangle G T ∧ T ∩ closed_nbhd G v ≠ ∅} = ∅ := by
  set G₀ := G₀def G v with hG₀def
  dsimp[G₀def] at hG₀def
  set F₁ := {T | is_triangle G₀ T} with hF₁
  set F₂ := {T | is_triangle G T ∧ T ∩ closed_nbhd G v ≠ ∅} with hF₂
  suffices : F₂ ∩ F₁ = ∅
  . exact triv_lem_about_disj F₂ F₁ this
  suffices h₀ (T : Set ℕ): is_triangle G T ∧ (T ∩ closed_nbhd G v ≠ ∅) → ¬(is_triangle G₀ T)
  . exact lem_about_disj {T | is_triangle G T ∧ T ∩ closed_nbhd G v ≠ ∅} {T | is_triangle G₀ T} h₀
  intro ⟨hT1,hT2⟩
  dsimp[is_triangle]
  by_contra hcontra; rcases hcontra with ⟨x,y,z,⟨hxney,hxnez,hynez⟩,hT,hxyG₀,hxzG₀,hyzG₀⟩
  set Nv := closed_nbhd G v with hNvdef
  rw[hT] at hT2
  rcases hT2 with h
  simp only [ne_eq] at hT2; push_neg at hT2
  rcases hT2 with ⟨t,ht1,ht2⟩
  simp only [mem_insert_iff, mem_singleton_iff] at ht1
  rcases ht1 with (htx | htyz)
  dsimp[G₀] at hxyG₀; dsimp[G₀def] at hxyG₀
  rcases hxyG₀ with ⟨x1,y1,hx1y11,hx1y12,hx1y13,hx1y14⟩
  have hx1ory1x : x1 = x ∨ y1 = x := by
    exact triv_lem_sets_2 G hGgraph x y x1 y1 hx1y12 hx1y11
  rw[htx] at ht2
  rcases hx1ory1x with (hx1x|hy1x)
  rw[← hNvdef] at hx1y13; rw[hx1x] at hx1y13; exact hx1y13 ht2
  rw[← hNvdef] at hx1y14; rw[hy1x] at hx1y14; exact hx1y14 ht2
  dsimp[G₀] at hyzG₀; dsimp[G₀def] at hyzG₀
  rcases htyz with (hty | htz)
  rw[hty] at ht2
  rcases hyzG₀ with ⟨x1,y1,hx1y11,hx1y12,hx1y13,hx1y14⟩
  have hx1ory1x : x1 = y ∨ y1 = y := by
    exact triv_lem_sets_2 G hGgraph y z x1 y1 hx1y12 hx1y11
  rcases hx1ory1x with (hx1x|hy1x)
  rw[← hNvdef] at hx1y13; rw[hx1x] at hx1y13; exact hx1y13 ht2
  rw[← hNvdef] at hx1y14; rw[hy1x] at hx1y14; exact hx1y14 ht2
  rw[htz] at ht2
  rcases hyzG₀ with ⟨x1,y1,hx1y11,hx1y12,hx1y13,hx1y14⟩
  have hx1ory1x : x1 = z ∨ y1 = z := by
    have hyzzy : ({y,z} : Set ℕ) = ({z,y} : Set ℕ) := by
      exact Set.pair_comm y z
    rw[hyzzy] at hx1y11; rw[hyzzy] at hx1y12
    exact triv_lem_sets_2 G hGgraph z y x1 y1 hx1y12 hx1y11
  rcases hx1ory1x with (hx1x|hy1x)
  rw[← hNvdef] at hx1y13; rw[hx1x] at hx1y13; exact hx1y13 ht2
  rw[← hNvdef] at hx1y14; rw[hy1x] at hx1y14; exact hx1y14 ht2

lemma tricounts_finite_0 (G : Set ℕ × Set (Set ℕ)) (hGgraph : is_graph G) (hGfin: G.1.Finite):
{T | is_triangle G T}.Finite := by
  --create injection from {T | is_triangle G T} to G × G × G
  let f : Set ℕ → (Set ℕ) × (Set ℕ) × (Set ℕ) := fun T ↦
    if h: ∃a : ℕ × ℕ × ℕ, T = {a.1,a.2.1,a.2.2} then
      ( {h.choose.1 , h.choose.2.1} , {h.choose.1, h.choose.2.2} , {h.choose.2.1,h.choose.2.2} )
    else (∅,∅,∅)
  set B : Set ((Set ℕ) × (Set ℕ) × (Set ℕ)) :=
    {(e1,e2,e3) :  (Set ℕ) × (Set ℕ) × (Set ℕ)| e1 ∈ G.2 ∧ e2 ∈ G.2 ∧ e3 ∈ G.2} with hBdef

  have h_istri_prop (T : Set ℕ) : is_triangle G T →  ∃a : ℕ × ℕ × ℕ, T = {a.1,a.2.1,a.2.2} := by
    intro h
    dsimp[is_triangle] at h
    rcases h with ⟨x,y,z,⟨hxney,hxnez,hynez⟩,hT,hxyG₀,hxzG₀,hyzG₀⟩
    use (x,y,z)

  have hfinjon : InjOn f {T | is_triangle G T} := by
    dsimp[InjOn]; intro T1 hT1 T2 hT2 hfT1T2
    have ha1 := h_istri_prop T1 hT1
    have ha2 := h_istri_prop T2 hT2
    have ha1prop := ha1.choose_spec
    have ha2prop := ha2.choose_spec
    rw[ha1prop, ha2prop]
    set a1 := ha1.choose with ha1def
    set a2 := ha2.choose with ha2def
    have hfT1: f T1 = ({a1.1,a1.2.1},{a1.1,a1.2.2},{a1.2.1,a1.2.2}) := by
      dsimp[f]
      simp[ha1]
    have hfT2: f T2 = ({a2.1,a2.2.1},{a2.1,a2.2.2},{a2.2.1,a2.2.2}) := by
      dsimp[f]
      simp[ha2]
    rw[hfT1] at hfT1T2; rw[hfT2] at hfT1T2
    exact triv_lem_sets_4 _ _ _ _ _ _ hfT1T2

  have hrange : f '' {T | is_triangle G T} ⊆ B := by
    intro zeta hzeta; simp at hzeta; rcases hzeta with ⟨T,hT1,hT2⟩
    have hT3 := h_istri_prop T hT1
    dsimp[f] at hT2
    simp[hT3] at hT2
    have hT3prop := hT3.choose_spec
    set a := hT3.choose with hadef
    rcases hT1 with ⟨x,y,z,⟨hxney,hxnez,hynez⟩,hT,hxyG₀,hxzG₀,hyzG₀⟩
    rw[← hT2]; dsimp[B]; rw[hT3prop] at hT
    exact triv_lem_graphs_4_0 G hGgraph a.1 a.2.1 a.2.2 x y z hxney hxnez hynez hT hxyG₀ hxzG₀ hyzG₀

  have hfinB : B.Finite := by
    dsimp[B]
    have hG2fin := G1fin_imp_G2fin G hGgraph hGfin
    have h_cart : (G.2 ×ˢ G.2 ×ˢ G.2).Finite := Set.Finite.prod hG2fin (Set.Finite.prod hG2fin hG2fin)
    apply Set.Finite.subset h_cart
    intro x hx
    simp; tauto
  have hrangefin : (f '' {T | is_triangle G T}).Finite := by
    exact Finite.subset hfinB hrange

  exact (Set.finite_image_iff hfinjon).mp hrangefin

lemma tricounts_finite_1 (G : Set ℕ × Set (Set ℕ)) (hGgraph : is_graph G) (hGfin: G.1.Finite) (v : ℕ):
{T | is_triangle (G₀def G v) T}.Finite := by
  set G₀ := G₀def G v with hG₀def
  suffices: {T | is_triangle (G₀def G v) T} ⊆ {T | is_triangle G T}
  . have hfin0 := tricounts_finite_0 G hGgraph hGfin
    exact Finite.subset hfin0 this
  intro T hT; simp at hT; simp
  dsimp[is_triangle] at hT; rcases hT with ⟨x,y,z,⟨hxney,hxnez,hynez⟩,hT,hxyG₀,hxzG₀,hyzG₀⟩
  use x; use y; use z; apply And.intro; tauto; apply And.intro; tauto
  have hxyG := (G₀subG G hGgraph v) hxyG₀
  have hxzG := (G₀subG G hGgraph v) hxzG₀
  have hyzG := (G₀subG G hGgraph v) hyzG₀
  tauto

lemma tricounts_finite_2 (G : Set ℕ × Set (Set ℕ)) (hGgraph : is_graph G) (hGfin: G.1.Finite) (v : ℕ):
{T | is_triangle G T ∧ T ∩ closed_nbhd G v ≠ ∅}.Finite := by
  have hfin0 := tricounts_finite_0 G hGgraph hGfin
  have hsub : {T | is_triangle G T ∧ T ∩ closed_nbhd G v ≠ ∅} ⊆ {T | is_triangle G T} := by
    simp; tauto
  exact Finite.subset hfin0 hsub

lemma tricount_decomp (G : Set ℕ × Set (Set ℕ)) (hGgraph : is_graph G) (hGfin: G.1.Finite) (v : ℕ):
{T | is_triangle G T}.ncard = {T | is_triangle (G₀def G v) T}.ncard + {T | is_triangle G T ∧ T ∩ closed_nbhd G v ≠ ∅}.ncard := by
  have hdecomp := tri_decomp G hGgraph v
  rw[hdecomp]; clear hdecomp
  have hfin1 := tricounts_finite_1 G hGgraph hGfin v
  have hfin2 := tricounts_finite_2 G hGgraph hGfin v
  have hnear := Set.ncard_union_add_ncard_inter {T | is_triangle (G₀def G v) T} {T | is_triangle G T ∧ T ∩ closed_nbhd G v ≠ ∅} hfin1 hfin2
  suffices: ({T | is_triangle (G₀def G v) T} ∩ {T | is_triangle G T ∧ T ∩ closed_nbhd G v ≠ ∅}).ncard = 0
  . rw[this] at hnear; rw[add_zero] at hnear; exact hnear
  have hdisj := tri_disjoint G hGgraph v
  rw[hdisj]; exact ncard_empty (Set ℕ)


end triangle_decomp
