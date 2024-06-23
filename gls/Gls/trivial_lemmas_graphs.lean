import Gls.graph_definitions
import Gls.trivial_lemmas_sets

import Mathlib

open graph_defs
open triv_lem_sets

set_option linter.unusedVariables false

open Set
open scoped Classical
open Finset BigOperators

namespace trivial_lems_graphs

lemma triv_lem_graphs_1 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (x y : ℕ) (hxy : ({x,y} : Set ℕ) ∈ G.2):
x ∈ G.1 ∧ y ∈ G.1 := by
  have h := hGgraph {x,y} hxy
  rcases h with ⟨a,b,hab1,hab2,hab3,hab4⟩; apply And.intro
  have hxinxy := (triv_lem_1 x y).1; rw[hab4] at hxinxy;
  simp only [mem_insert_iff,mem_singleton_iff] at hxinxy
  rcases hxinxy with (hxa | hxb)
  rw[hxa]; exact hab1; rw[hxb]; exact hab2
  have hyinxy := (triv_lem_1 x y).2; rw[hab4] at hyinxy;
  simp only [mem_insert_iff,mem_singleton_iff] at hyinxy
  rcases hyinxy with (hya | hyb)
  rw[hya]; exact hab1; rw[hyb]; exact hab2

lemma triv_lem_graphs_2 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (x y : ℕ) (hxy : ({x,y} : Set ℕ) ∈ G.2):
x ≠ y := by
  have h := hGgraph {x,y} hxy
  rcases h with ⟨a,b,hab1,hab2,hab3,hab4⟩
  have hxinxy := (triv_lem_1 x y).1; rw[hab4] at hxinxy;
  simp only [mem_insert_iff,mem_singleton_iff] at hxinxy
  have hyinxy := (triv_lem_1 x y).2; rw[hab4] at hyinxy;
  simp only [mem_insert_iff,mem_singleton_iff] at hyinxy
  have hainab:= (triv_lem_1 a b).1; rw[← hab4] at hainab
  simp only [mem_insert_iff,mem_singleton_iff] at hainab
  have hbinab:= (triv_lem_1 a b).2; rw[← hab4] at hbinab
  simp only [mem_insert_iff,mem_singleton_iff] at hbinab
  rcases hxinxy with (hxa | hxb)
  rcases hyinxy with (hya | hyb)
  rcases hbinab with (hbx | hby)
  rw[← hxa] at hab3; rw[hbx] at hab3; exact fun a ↦ hab3 rfl
  rw[hxa]; rw[← hby]; exact hab3
  rw[hxa]; rw[hyb]; exact hab3
  rcases hyinxy with (hya | hyb)
  rw[hxb]; rw[hya]; apply Ne.symm; exact hab3
  rcases hainab with (hax | hay)
  rw[hax] at hab3; rw[← hxb] at hab3; exact fun a ↦ hab3 rfl
  rw[hxb]; rw[← hay]; apply Ne.symm; exact hab3

lemma triv_lem_graphs_3 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (x y : ℕ) (hxy : ({x,y} : Set ℕ) ∈ G.2):
{y,x} ∈ G.2 := by
  have hnear : {y,x} = ({x,y} : Set ℕ) := by
    exact Set.pair_comm y x
  rw[hnear]; exact hxy


lemma triv_lem_graphs_4_0 (G : Set ℕ × Set (Set ℕ)) (hGgraph : is_graph G)
(a b c x y z : ℕ) (hxney : x ≠ y) (hxnez : x ≠ z) (hynez : y ≠ z)
(habcxyz : ({a,b,c} : Set ℕ) = ({x,y,z} : Set ℕ))
(hxyG : {x,y} ∈ G.2) (hxzG : {x,z} ∈ G.2) (hyzG : {y,z} ∈ G.2):
{a,b} ∈ G.2 ∧ {a,c} ∈ G.2 ∧ {b,c} ∈ G.2 := by
  apply And.intro
  have hab := triv_lem_sets_3_1 a b c x y z habcxyz hxney hxnez hynez
  rcases hab with (habxy | habxz | habyz)
  rw[habxy]; exact hxyG; rw[habxz]; exact hxzG; rw[habyz]; exact hyzG
  apply And.intro
  have habc_eq_acb : ({a,b,c} : Set ℕ) = ({a,c,b} : Set ℕ) := by
    ext t; apply Iff.intro; intro h; rcases h with (ta | tb | tc)
    left; exact ta; right; right; exact tb; right; left; exact tc
    intro h; rcases h with (ta | tc | tb); left; exact ta; right
    right; exact tc; right; left; exact tb
  rw[habc_eq_acb] at habcxyz
  have hac := triv_lem_sets_3_1 a c b x y z habcxyz hxney hxnez hynez
  rcases hac with (hacxy | hacxz | hacyz)
  rw[hacxy]; exact hxyG; rw[hacxz]; exact hxzG; rw[hacyz]; exact hyzG
  have habc_eq_bca : ({a,b,c} : Set ℕ) = ({b,c,a} : Set ℕ) := by
    ext t; apply Iff.intro; intro h; rcases h with (hx | hyz | hz)
    right; right; exact hx; left; exact hyz; right; left; exact hz
    intro h; rcases h with (hz | hx | hy); right; left; exact hz
    right; right; exact hx; left; exact hy
  rw[habc_eq_bca] at habcxyz
  have hbc := triv_lem_sets_3_1 b c a x y z habcxyz hxney hxnez hynez
  rcases hbc with (hbcxy | hbcxz | hbcyz)
  rw[hbcxy]; exact hxyG; rw[hbcxz]; exact hxzG; rw[hbcyz]; exact hyzG


lemma triv_lem_graphs_4 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (x y z : ℕ)
(hxyztri: is_triangle G ({x,y,z} : Set ℕ)): {x,y} ∈ G.2 ∧ {x,z} ∈ G.2 ∧ {y,z} ∈ G.2 := by
  dsimp[is_triangle] at hxyztri; rcases hxyztri with ⟨x1,y1,z1,h1,h2,h3⟩
  exact triv_lem_graphs_4_0 G hGgraph x y z x1 y1 z1 h1.1 h1.2.1 h1.2.2 h2 h3.1 h3.2.1 h3.2.2


lemma G1fin_imp_G2fin (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite): G.2.Finite := by
  dsimp[is_graph] at hGgraph
  let f : Set ℕ → ℕ × ℕ := fun e ↦
    if h: ∃a : ℕ × ℕ, e = {a.1,a.2} then h.choose
    else (0,0)
  have hfinjon : InjOn f G.2 := by
    dsimp[InjOn]; intro e1 he1 e2 he2 hfe1e2
    have he11 := hGgraph e1 he1; rcases he11 with ⟨x,y,hxy1,hxy2,hxy3,hxy4⟩
    have he21 := hGgraph e2 he2; rcases he21 with ⟨w,z,hwz1,hwz2,hwz3,hwz4⟩
    have hexistsa : ∃(a : ℕ × ℕ), e1 = {a.1,a.2} := by use (x,y)
    have hexistsb : ∃(b : ℕ × ℕ), e2 = {b.1,b.2} := by use (w,z)
    have haprop := hexistsa.choose_spec
    have hbprop := hexistsb.choose_spec
    set a := hexistsa.choose with hadef
    set b := hexistsb.choose with hbdef
    have hfe1 : f e1 = (a.1,a.2) := by
      dsimp[f]; simp[hexistsa]
    have hfe2 : f e2 = (b.1,b.2) := by
      dsimp[f]; simp[hexistsb]
    rw[hfe1] at hfe1e2; rw[hfe2] at hfe1e2
    rw[haprop]; rw[hbprop]
    have ha1b1 : a.1 = b.1 := by injections
    have ha2b2 : a.2 = b.2 := by injections
    rw[ha1b1]; rw[ha2b2]
  set B : Set (ℕ × ℕ) := {(x,y) : ℕ × ℕ | x ∈ G.1 ∧ y ∈ G.1} with hBdef
  have hfrange : f '' G.2 ⊆ B := by
    intro zeta hzeta; rw[Set.mem_image] at hzeta
    rcases hzeta with ⟨e,he1,he2⟩
    rw[← he2]; dsimp[B]
    have he := hGgraph e he1; rcases he with ⟨x,y,hxy1,hxy2,hxy3,hxy4⟩
    set a : ℕ × ℕ := (x,y) with hadef
    have hea : e = {a.1,a.2} := by tauto
    have hexistsa : ∃ (a : ℕ × ℕ), e = {a.1,a.2} := by
      use a
    have hprop := hexistsa.choose_spec
    set u := hexistsa.choose.1 with hudef; set v := hexistsa.choose.2 with hvdef
    have hf : (f e).1 = u ∧ (f e).2 = v := by
      apply And.intro; dsimp[f]; simp[hexistsa]
      dsimp[f]; simp[hexistsa]
    rw[hf.1,hf.2]
    rw[hprop] at he1
    exact triv_lem_graphs_1 G hGgraph u v he1
  have hBfin : B.Finite := by
    dsimp[B]
    have hnear := Set.Finite.prod hGfin hGfin
    exact hnear
  have hfrangefin : (f '' G.2).Finite := by
    exact Finite.subset hBfin hfrange

  exact (Set.finite_image_iff hfinjon).mp hfrangefin



end trivial_lems_graphs
