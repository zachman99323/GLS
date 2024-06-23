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

namespace keyeq

def Omega (G : Set ℕ × Set (Set ℕ)) : Set (ℕ × ℕ × ℕ × ℕ) :=
{(z,u,v,w) | {u,v} ∈ G.2 ∧ {u,w} ∈ G.2 ∧ {v,w} ∈ G.2 ∧
({z,u} ∈ G.2 ∨ {z,v} ∈ G.2 ∨ {z,w} ∈ G.2)}

def Sigma (G : Set ℕ × Set (Set ℕ)): Set (ℕ × ℕ × ℕ × ℕ) :=
{(x,u,v,w) | {x,u} ∈ G.2 ∧ {x,v} ∈ G.2 ∧ {x,w} ∈ G.2}

--G finite implies Omega(G) finite
lemma Omegafin (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite):
(Omega G).Finite := by
  have hnear1 : Omega G ⊆ G.1 ×ˢ G.1 ×ˢ G.1 ×ˢ G.1  := by
    intro (x,u,v,w) hxuvw; simp only [mem_prod]
    dsimp[Omega] at hxuvw; apply And.intro; swap
    use (triv_lem_graphs_1 G hGgraph u v hxuvw.1).1
    use (triv_lem_graphs_1 G hGgraph u v hxuvw.1).2
    use (triv_lem_graphs_1 G hGgraph u w hxuvw.2.1).2
    have hxuvw4 := hxuvw.2.2.2
    rcases hxuvw4 with (hxu | hxv | hxw)
    exact (triv_lem_graphs_1 G hGgraph x u hxu).1; exact (triv_lem_graphs_1 G hGgraph x v hxv).1
    exact (triv_lem_graphs_1 G hGgraph x w hxw).1

  refine Set.Finite.subset ?_ hnear1
  refine Finite.prod hGfin ?_; refine Finite.prod hGfin ?_
  refine Finite.prod hGfin ?_; exact hGfin

--G finite implies Sigma(G) finite
lemma Sigmafin (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite):
(Sigma G).Finite := by
  have hnear1 : Sigma G ⊆ G.1 ×ˢ G.1 ×ˢ G.1 ×ˢ G.1  := by
    intro ⟨x,u,v,w⟩ hxuvw; simp only [mem_prod]
    dsimp[Sigma] at hxuvw; use (triv_lem_graphs_1 G hGgraph x u hxuvw.1).1
    use (triv_lem_graphs_1 G hGgraph x u hxuvw.1).2; use (triv_lem_graphs_1 G hGgraph x v hxuvw.2.1).2
    exact (triv_lem_graphs_1 G hGgraph x w hxuvw.2.2).2

  refine Set.Finite.subset ?_ hnear1
  refine Finite.prod hGfin ?_; refine Finite.prod hGfin ?_
  refine Finite.prod hGfin ?_; exact hGfin

lemma six_options_0_0 (x y z : ℕ) (a : ℕ × ℕ × ℕ) (hne: x ≠ y ∧ x ≠ z ∧ y ≠ z)
(haeqxyz: {a.1, a.2.1, a.2.2} = ({x, y, z} : Set ℕ)):
a.1 ≠ a.2.1 := by
  by_contra hcontra
  have hxeqa : x = a.1 ∨ x = a.2.1 ∨ x = a.2.2 := by
    have hxina : x ∈ ({a.1,a.2.1,a.2.2} : Set ℕ) := by
      rw[haeqxyz]; exact Set.mem_insert x {y, z}
    exact hxina
  have hyeqa : y = a.1 ∨ y = a.2.1 ∨ y = a.2.2  := by
    have hyina : y ∈ ({a.1,a.2.1,a.2.2} : Set ℕ) := by
      rw[haeqxyz]; refine mem_insert_iff.mpr ?_; right; exact Set.mem_insert y {z}
    exact hyina
  have hzeqa : z = a.1 ∨ z = a.2.1 ∨ z = a.2.2 := by
    have hzina : z ∈ ({a.1,a.2.1,a.2.2} : Set ℕ) := by
      rw[haeqxyz]; refine mem_insert_iff.mpr ?_; right; exact Set.mem_insert_of_mem y rfl
    exact hzina
  have ha21eqxyz : a.2.1 = x ∨ a.2.1 = y ∨ a.2.1 = z := by
    have ha21inxyz : a.2.1 ∈ ({x,y,z} : Set ℕ) := by
      rw[← haeqxyz]; refine mem_insert_iff.mpr ?_; right; exact Set.mem_insert a.2.1 {a.2.2}
    exact ha21inxyz
  have ha22eqxyz: a.2.2 = x ∨ a.2.2 = y ∨ a.2.2 = z := by
    have ha22inxyz : a.2.2 ∈ ({x,y,z} : Set ℕ) := by
      rw[← haeqxyz]; refine mem_insert_iff.mpr ?_; right; exact Set.mem_insert_of_mem a.2.1 rfl
    exact ha22inxyz

  have hxnea1 : x ≠ a.1 := by
    by_contra hxa1
    rcases hyeqa with (hya1 | hya21 | hya22)
    rw[← hya1] at hxa1; exact hne.1 hxa1
    rw[hcontra] at hxa1; rw[← hya21] at hxa1; exact hne.1 hxa1
    rcases hzeqa with (hza1 | hza21 | hza22)
    rw[← hza1] at hxa1; exact hne.2.1 hxa1
    rw[← hcontra] at hza21; rw[← hza21] at hxa1; exact hne.2.1 hxa1
    rw[← hza22] at hya22; exact hne.2.2 hya22
  rcases hxeqa with (hxa1 | hxa21 | hxa22)
  exact hxnea1 hxa1; rw[← hcontra] at hxa21; exact hxnea1 hxa21
  have hynea1 : y ≠ a.1 := by
    by_contra hya1
    rcases hzeqa with (hza1 | hza21 | hza22)
    rw[← hza1] at hya1; exact hne.2.2 hya1
    rw[← hcontra] at hza21; rw[← hza21] at hya1; exact hne.2.2 hya1
    rw[← hza22] at hxa22; exact hne.2.1 hxa22
  rcases hyeqa with (hya1 | hya21 | hya22)
  exact hynea1 hya1; rw[← hcontra] at hya21; exact hynea1 hya21
  rw[← hya22] at hxa22; exact hne.1 hxa22

lemma six_options_0 (x y z : ℕ) (a : ℕ × ℕ × ℕ) (hne: x ≠ y ∧ x ≠ z ∧ y ≠ z)
(haeqxyz: {a.1, a.2.1, a.2.2} = ({x, y, z} : Set ℕ)):
a.1 ≠ a.2.1 ∧ a.1 ≠ a.2.2 ∧ a.2.1 ≠ a.2.2 := by
  apply And.intro
  exact six_options_0_0 x y z a hne haeqxyz
  apply And.intro
  let b := (a.1,a.2.2,a.2.1)
  have hbeqxyz : {b.1,b.2.1,b.2.2} = ({x,y,z} : Set ℕ) := by
    dsimp[b]; rw[← haeqxyz]
    suffices: {a.2.2,a.2.1} = ({a.2.1,a.2.2} : Set ℕ)
    . exact congrArg (insert a.1) this
    exact Set.pair_comm a.2.2 a.2.1
  have hnear := six_options_0_0 x y z b hne hbeqxyz; dsimp[b] at hnear; exact hnear
  let b := (a.2.1,a.2.2,a.1)
  have hbeqxyz : {b.1,b.2.1,b.2.2} = ({x,y,z} : Set ℕ) := by
    dsimp[b]; rw[← haeqxyz]; ext x; apply Iff.intro; intro hx; rcases hx with (h1 | h2 | h3); right; left
    exact h1; right; right; exact h2; left; exact h3; intro hx; rcases hx with (h1 | h2 | h3); right; right
    exact h1; left; exact h2; right; left; exact h3
  have hnear := six_options_0_0 x y z b hne hbeqxyz; dsimp[b] at hnear; exact hnear

lemma six_options_1 (x y z : ℕ) (a : ℕ × ℕ × ℕ) (hne: x ≠ y ∧ x ≠ z ∧ y ≠ z)
(haeqxyz: {a.1, a.2.1, a.2.2} = ({x, y, z} : Set ℕ)) (ha1x : a.1 = x):
a ∈ ({(x, y, z), (x, z, y), (y, x, z), (y, z, x), (z, x, y), (z, y, x)} : Set (ℕ × ℕ × ℕ)) := by
  have hxeqa : x = a.1 ∨ x = a.2.1 ∨ x = a.2.2 := by
    have hxina : x ∈ ({a.1,a.2.1,a.2.2} : Set ℕ) := by
      rw[haeqxyz]; exact Set.mem_insert x {y, z}
    exact hxina
  have hyeqa : y = a.1 ∨ y = a.2.1 ∨ y = a.2.2  := by
    have hyina : y ∈ ({a.1,a.2.1,a.2.2} : Set ℕ) := by
      rw[haeqxyz]; refine mem_insert_iff.mpr ?_; right; exact Set.mem_insert y {z}
    exact hyina
  have hzeqa : z = a.1 ∨ z = a.2.1 ∨ z = a.2.2 := by
    have hzina : z ∈ ({a.1,a.2.1,a.2.2} : Set ℕ) := by
      rw[haeqxyz]; refine mem_insert_iff.mpr ?_; right; exact Set.mem_insert_of_mem y rfl
    exact hzina
  have ha1eqxyz : a.1 = x ∨ a.1 = y ∨ a.1 = z := by
    have ha1inxyz : a.1 ∈ ({x,y,z} : Set ℕ) := by
      rw[← haeqxyz]; left; rfl
    exact ha1inxyz
  have ha21eqxyz : a.2.1 = x ∨ a.2.1 = y ∨ a.2.1 = z := by
    have ha21inxyz : a.2.1 ∈ ({x,y,z} : Set ℕ) := by
      rw[← haeqxyz]; refine mem_insert_iff.mpr ?_; right; exact Set.mem_insert a.2.1 {a.2.2}
    exact ha21inxyz
  have ha22eqxyz: a.2.2 = x ∨ a.2.2 = y ∨ a.2.2 = z := by
    have ha22inxyz : a.2.2 ∈ ({x,y,z} : Set ℕ) := by
      rw[← haeqxyz]; refine mem_insert_iff.mpr ?_; right; exact Set.mem_insert_of_mem a.2.1 rfl
    exact ha22inxyz

  have hane := six_options_0 x y z a hne haeqxyz

  rcases ha21eqxyz with (ha21x | ha21y | ha21z)
  rw[← ha21x] at ha1x; exact False.elim (hane.1 ha1x)
  rcases ha22eqxyz with (ha22x | ha22y | ha22z)
  rw[← ha22x] at ha1x; exact False.elim (hane.2.1 ha1x)
  rw[← ha22y] at ha21y; exact False.elim (hane.2.2 ha21y)
  left; rw[← ha1x, ← ha21y, ← ha22z]
  rcases ha22eqxyz with (ha22x | ha22y | ha22z)
  rw[← ha22x] at ha1x; exact False.elim (hane.2.1 ha1x)
  right; left; rw[← ha1x, ← ha21z, ← ha22y]
  rw[← ha22z] at ha21z; exact False.elim (hane.2.2 ha21z)

lemma six_options (x y z : ℕ) (a : ℕ × ℕ × ℕ) (hne: x ≠ y ∧ x ≠ z ∧ y ≠ z)
(haeqxyz: {a.1, a.2.1, a.2.2} = ({x, y, z} : Set ℕ)):
a ∈ ({(x, y, z), (x, z, y), (y, x, z), (y, z, x), (z, x, y), (z, y, x)} : Set (ℕ × ℕ × ℕ)) := by
  have hxeqa : x = a.1 ∨ x = a.2.1 ∨ x = a.2.2 := by
    have hxina : x ∈ ({a.1,a.2.1,a.2.2} : Set ℕ) := by
      rw[haeqxyz]; exact Set.mem_insert x {y, z}
    exact hxina
  have hyeqa : y = a.1 ∨ y = a.2.1 ∨ y = a.2.2  := by
    have hyina : y ∈ ({a.1,a.2.1,a.2.2} : Set ℕ) := by
      rw[haeqxyz]; refine mem_insert_iff.mpr ?_; right; exact Set.mem_insert y {z}
    exact hyina
  have hzeqa : z = a.1 ∨ z = a.2.1 ∨ z = a.2.2 := by
    have hzina : z ∈ ({a.1,a.2.1,a.2.2} : Set ℕ) := by
      rw[haeqxyz]; refine mem_insert_iff.mpr ?_; right; exact Set.mem_insert_of_mem y rfl
    exact hzina
  have ha1eqxyz : a.1 = x ∨ a.1 = y ∨ a.1 = z := by
    have ha1inxyz : a.1 ∈ ({x,y,z} : Set ℕ) := by
      rw[← haeqxyz]; left; rfl
    exact ha1inxyz
  have ha21eqxyz : a.2.1 = x ∨ a.2.1 = y ∨ a.2.1 = z := by
    have ha21inxyz : a.2.1 ∈ ({x,y,z} : Set ℕ) := by
      rw[← haeqxyz]; refine mem_insert_iff.mpr ?_; right; exact Set.mem_insert a.2.1 {a.2.2}
    exact ha21inxyz
  have ha22eqxyz: a.2.2 = x ∨ a.2.2 = y ∨ a.2.2 = z := by
    have ha22inxyz : a.2.2 ∈ ({x,y,z} : Set ℕ) := by
      rw[← haeqxyz]; refine mem_insert_iff.mpr ?_; right; exact Set.mem_insert_of_mem a.2.1 rfl
    exact ha22inxyz

  have hane := six_options_0 x y z a hne haeqxyz

  rcases ha1eqxyz with (ha1x | ha1y | ha1z)
  exact six_options_1 x y z a hne haeqxyz ha1x

  have hnear := six_options_1 y x z a ?_ ?_ ha1y
  swap; apply And.intro; symm; exact hne.1; apply And.intro; exact hne.2.2; exact hne.2.1
  swap; rw[haeqxyz]; exact insert_comm x y {z}
  rcases hnear with (h1 | h2 | h3 | h4 | h5 | h6)
  right; right; left; exact h1; right; right; right; left; exact h2; left; exact h3
  right; left; exact h4; right; right; right; right; right; exact h5; right; right;
  right; right; left; exact h6

  have hnear := six_options_1 z x y a ?_ ?_ ha1z
  swap; apply And.intro; symm; exact hne.2.1; apply And.intro; symm; exact hne.2.2; exact hne.1
  rcases hnear with (h1 | h2 | h3 | h4 | h5 | h6)
  right; right; right; right; left; exact h1; right; right; right; right; right; exact h2
  right; left; exact h3; left; exact h4; right; right; right; left; exact h5; right
  right; left; exact h6
  rw[haeqxyz]; ext t; apply Iff.intro; intro ht; rcases ht with (htx | hty | htz); right
  left; exact htx; right; right; exact hty; left; exact htz; intro ht
  rcases ht with (htx | hty | htz); right; right; exact htx; left; exact hty; right
  left; exact htz

lemma ncard_six (x y z : ℕ) (hne : x ≠ y ∧ x ≠ z ∧ y ≠ z):
({(x, y, z), (x, z, y), (y, x, z), (y, z, x), (z, x, y), (z, y, x)} : Set (ℕ × ℕ × ℕ)).ncard = 6 := by
  let T := ({(x, z, y), (y, x, z), (y, z, x), (z, x, y), (z, y, x)}: Set (ℕ × ℕ × ℕ))
  refine (ncard_eq_succ ?_).mpr ?_
  exact toFinite {(x, y, z), (x, z, y), (y, x, z), (y, z, x), (z, x, y), (z, y, x)}
  use (x,y,z); use {(x, z, y), (y, x, z), (y, z, x), (z, x, y), (z, y, x)}
  apply And.intro; swap; apply And.intro; rfl; refine (ncard_eq_succ ?_).mpr ?_
  exact toFinite {(x, z, y), (y, x, z), (y, z, x), (z, x, y), (z, y, x)}; use (x,z,y)
  use {(y, x, z), (y, z, x), (z, x, y), (z, y, x)}; apply And.intro; swap; apply And.intro
  rfl; refine (ncard_eq_succ ?_).mpr ?_; exact toFinite {(y, x, z), (y, z, x), (z, x, y), (z, y, x)}
  use (y,x,z); use {(y, z, x), (z, x, y), (z, y, x)}; apply And.intro; swap; apply And.intro
  rfl; refine (ncard_eq_succ ?_).mpr ?_; exact toFinite {(y, z, x), (z, x, y), (z, y, x)}
  use (y,z,x); use {(z, x, y), (z, y, x)}; apply And.intro; swap; apply And.intro; rfl
  refine ncard_pair ?h.right.right.h; by_contra hcontra; injections h1 h2 h3; exact hne.1 h3
  by_contra hcontra; rcases hcontra with (h1 | h2); injections h1; exact hne.2.2 h1
  injections h2; exact hne.2.2 h2; by_contra hcontra; rcases hcontra with (h1 | h2 | h3)
  injections ha hb hb; exact hne.2.1 hb; injections h2; exact hne.2.2 h2; injections h3
  exact hne.2.2 h3; by_contra hcontra; rcases hcontra with (h1 | h2 | h3 | h4)
  injections h1; exact hne.1 h1; injections h2; exact hne.1 h2; injections h3; exact hne.2.1 h3
  injections h4; exact hne.2.1 h4; by_contra hcontra; rcases hcontra with (h1 | h2 | h3 | h4 | h5)
  injections h1 ha ha; exact hne.2.2 ha; injections h2; exact hne.1 h2; injections h3; exact hne.1 h3
  injections h4; exact hne.2.1 h4; injections h5; exact hne.2.1 h5

lemma or_elim_triv (P Q : Prop) (h1: ¬ P) (h2: P ∨ Q) : Q := by
  tauto

lemma powset_finite (E : Set ℕ) (hEfin: E.Finite) (A : Set (Set ℕ)) (hAE : ∀ T ∈ A, T ⊆ E): A.Finite := by
  let E1 := Finite.toFinset hEfin
  let F1 := Finset.powerset E1

  have hTfin : ∀ T ∈ A, T.Finite := by
    intro T hT
    exact Finite.subset hEfin (hAE T hT)
  let A1 : Set (Finset ℕ) := {T1 | ∃(T : Set ℕ) (h: T ∈ A), T1 = Finite.toFinset (hTfin T h)}

  have hAsubF1 : A1 ⊆ F1 := by
    intro T1 hT1; dsimp[F1]; simp only [coe_powerset, Set.mem_preimage, mem_powerset_iff,Finset.coe_subset]
    dsimp[A1] at hT1; rcases hT1 with ⟨T,hT⟩; rcases hT with ⟨hTinA,hT1eq⟩; rw[hT1eq];
    simp only [Finite.toFinset_subset]; have hnear := hAE T hTinA; intro t ht; have htinE := hnear ht
    norm_cast; exact (Finite.mem_toFinset hEfin).mpr (hAE T hTinA ht)
  have hA1fin : A1.Finite := by
    refine Finite.subset ?_ hAsubF1
    exact finite_toSet F1

  let f : Set ℕ → Finset ℕ := fun T ↦
    if h: T ∈ A then Finite.toFinset (hTfin T h)
    else ∅

  apply (@Set.finite_image_iff (Set ℕ) (Finset ℕ) A f ?_).mp

  --show f '' A Finite
  suffices: f '' A ⊆ A1
  . exact Finite.subset hA1fin this
  intro T1 hT1; simp only [Set.mem_image] at hT1; rcases hT1 with ⟨T,hT1,hT2⟩
  dsimp[f] at hT2; simp only [hT1] at hT2; simp only [↓reduceDite] at hT2
  dsimp[A1]; use T; use hT1; symm; exact hT2

  --show f is injective
  intro T1 hT1 T2 hT2 hf12
  dsimp[f] at hf12; simp only [hT1,hT2] at hf12; simp only [↓reduceDite, Finite.toFinset_inj] at hf12
  exact hf12

lemma times_6 (P : Set ℕ → Prop) (E : Set ℕ) (hEfin : E.Finite) (A : Set (Set ℕ))
(hAE : ∀ T ∈ A, ∀x ∈ T, x ∈ E)
:
6*{a ∈ A | ∃ (x y z : ℕ), (x ≠ y ∧ x ≠ z ∧ y ≠ z) ∧ a = {x,y,z} ∧ P a}.ncard
= {(x,y,z) | (x ≠ y ∧ x ≠ z ∧ y ≠ z) ∧ {x,y,z} ∈ A ∧ P {x,y,z}}.ncard := by
  set C := {(x,y,z) | (x ≠ y ∧ x ≠ z ∧ y ≠ z) ∧ {x,y,z} ∈ A ∧ P {x,y,z}}
  set D := {a ∈ A | ∃ (x y z : ℕ), (x ≠ y ∧ x ≠ z ∧ y ≠ z) ∧ a = {x,y,z} ∧ P a}
  let f : ℕ × ℕ × ℕ → Set ℕ :=
  fun (x,y,z) ↦ {x,y,z}

  symm
  apply ncard_m_to_1 C D ?_ ?_ 6 f ?_ ?_

  --show first set finite
  suffices: C ⊆ E ×ˢ E ×ˢ E
  . refine Finite.subset ?_ this
    refine Finite.prod hEfin ?_; exact Finite.prod hEfin hEfin
  dsimp[C]; intro ⟨x,y,z⟩ hxyz; simp only [mem_setOf] at hxyz; simp only [mem_prod]
  apply And.intro; refine hAE {x,y,z} hxyz.2.1 x ?_; exact Set.mem_insert x {y, z}
  apply And.intro; refine hAE {x,y,z} hxyz.2.1 y ?_; refine mem_insert_iff.mpr ?_
  right; exact Set.mem_insert y {z}; refine hAE {x,y,z} hxyz.2.1 z ?_; refine mem_insert_iff.mpr ?_
  right; exact Set.mem_insert_of_mem y rfl

  --show second set finite
  have hAfin: A.Finite := by
    exact powset_finite E hEfin A hAE
  refine Finite.subset hAfin ?_
  intro a ha; dsimp[D] at ha; exact ha.1

  --show f maps first set into second set
  intro a ha; simp only [mem_setOf] at ha; dsimp[f]; dsimp[C] at ha; dsimp[D]
  set x := a.1; set y := a.2.1; set z := a.2.2; use ha.2.1; use x; use y; use z; use ha.1;
  use rfl; exact ha.2.2

  --show f is 6-to-1
  intro b hb; simp only [mem_setOf] at hb; have hb1 := hb.1; have hb2 := hb.2; clear hb
  rcases hb2 with ⟨x,y,z,hxyz1,hxyz2⟩
  have hnear : {a | a ∈ C ∧ f a = b} = {(x,y,z),(x,z,y),(y,x,z),(y,z,x),(z,x,y),(z,y,x)} := by

    have hxzy : {x,z,y} = ({x,y,z} : Set ℕ) := by
      suffices: {z,y} = ({y,z} : Set ℕ)
      . exact congrArg (insert x) this
      exact Set.pair_comm z y
    have hyxz : {y,x,z} = ({x,y,z} : Set ℕ) := by
      exact insert_comm y x {z}
    have hyzx : {y,z,x} = ({x,y,z} : Set ℕ) := by
      ext t; apply Iff.intro; intro ht; rcases ht with (h | h | h); right; left
      exact h; right; right; exact h; left; exact h; intro ht
      rcases ht with (h | h | h); right; right; exact h; left; exact h; right; left; exact h
    have hzxy : {z,x,y} = ({x,y,z} : Set ℕ) := by
      ext t; apply Iff.intro; intro ht; rcases ht with (h|h|h); right; right; exact h;
      left; exact h; right; left; exact h; intro ht; rcases ht with (h|h|h); right; left
      exact h; right; right; exact h; left; exact h
    have hzyx : {z,y,x} = ({x,y,z} : Set ℕ) := by
      ext t; apply Iff.intro; intro ht; rcases ht with (h|h|h); right; right; exact h;
      right; left; exact h; left; exact h; intro ht; rcases ht with (h|h|h); right; right;
      exact h; right; left; exact h; left; exact h

    apply Set.Subset.antisymm

    intro a ha; rw[mem_setOf] at ha; have ha1 := ha.1; have ha2 := ha.2; clear ha
    dsimp[f] at ha2; rw[hxyz2.1] at ha2
    exact six_options x y z a hxyz1 ha2

    intro a ha; rw[mem_setOf]; dsimp[C]
    rcases ha with (ha1 | ha2 | ha3 | ha4 | ha5 | ha6)
    rw[ha1]; simp only; apply And.intro; swap; dsimp[f]; symm; exact hxyz2.1
    use hxyz1; rw[hxyz2.1] at hb1; use hb1; rw[← hxyz2.1]; exact hxyz2.2

    rw[ha2]; simp only; apply And.intro; apply And.intro; apply And.intro; exact hxyz1.2.1
    apply And.intro; exact hxyz1.1; push_neg; symm; exact hxyz1.2.2; apply And.intro
    rw[hxyz2.1] at hb1
    rw[hxzy]; exact hb1
    rw[hxzy]; rw[hxyz2.1] at hxyz2; exact hxyz2.2
    dsimp[f]; rw[hxyz2.1]; exact hxzy

    rw[ha3]; simp only; apply And.intro; swap; dsimp[f]; rw[hxyz2.1]; exact hyxz; apply And.intro
    apply And.intro; push_neg; symm; exact hxyz1.1; apply And.intro; exact hxyz1.2.2; exact hxyz1.2.1
    apply And.intro; rw[hxyz2.1] at hb1; rw[hyxz]; exact hb1; rw[hxyz2.1] at hxyz2; rw[hyxz]
    exact hxyz2.2

    rw[ha4]; simp only; apply And.intro; swap; dsimp[f]; rw[hyzx]; symm; exact hxyz2.1
    apply And.intro; apply And.intro; exact hxyz1.2.2; apply And.intro; push_neg; symm
    exact hxyz1.1; push_neg; symm; exact hxyz1.2.1; apply And.intro; rw[hyzx]; rw[← hxyz2.1]
    exact hb1; rw[hyzx]; rw[hxyz2.1] at hxyz2; exact hxyz2.2

    rw[ha5]; simp only; apply And.intro; swap; dsimp[f]; rw[hzxy]; symm; exact hxyz2.1
    apply And.intro; apply And.intro; push_neg; symm; exact hxyz1.2.1; apply And.intro
    push_neg; symm; exact hxyz1.2.2; exact hxyz1.1; apply And.intro; rw[hzxy]; rw[hxyz2.1] at hb1
    exact hb1; rw[hzxy]; rw[hxyz2.1] at hxyz2; exact hxyz2.2

    rw[ha6]; simp only; apply And.intro; swap; dsimp[f]; rw[hzyx]; symm; exact hxyz2.1
    apply And.intro; apply And.intro; push_neg; symm; exact hxyz1.2.2; apply And.intro
    push_neg; symm; exact hxyz1.2.1; push_neg; symm; exact hxyz1.1; apply And.intro
    rw[hzyx]; rw[hxyz2.1] at hb1; exact hb1; rw[hzyx]; rw[hxyz2.1] at hxyz2; exact hxyz2.2

  rw[hnear]
  exact ncard_six x y z hxyz1

--in order to change from 6*sum_v |N_{T[v]}| to |Omega(G)|, show for each w, that
--6*|N_{T[w]}| = |marginal1 Omega(G) w|
lemma to_Omega_0 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite) (w : ℕ):
(marginal1 (Omega G) w).ncard = 6 * {T | is_triangle G T ∧ T ∩ closed_nbhd G w ≠ ∅}.ncard := by
  --dsimp[is_triangle, closed_nbhd]
  symm
  let P : Set ℕ → Prop := fun T ↦ is_triangle G T ∧ T ∩ closed_nbhd G w ≠ ∅
  let A : Set (Set ℕ) := {a : Set ℕ | ∃(x y z : ℕ), a = {x,y,z} ∧ (x ∈ G.1 ∧ y ∈ G.1 ∧ z ∈ G.1)}
  have hAE : ∀ T ∈ A, ∀x ∈ T, x ∈ G.1 := by
    intro T hT; intro x hx; dsimp[A] at hT; rcases hT with ⟨x1,y1,z1,h1,h2⟩
    rw[h1] at hx; rcases hx with (hx1 | hx2 | hx3); rw[hx1]; exact h2.1; rw[hx2]; exact h2.2.1
    rw[hx3]; exact h2.2.2
  have hnear := times_6 P G.1 hGfin A hAE
  have hlhs: {T | is_triangle G T ∧ ¬T ∩ closed_nbhd G w = ∅} =
  {a | a ∈ A ∧ ∃ x y z, (x ≠ y ∧ x ≠ z ∧ y ≠ z) ∧ a = {x, y, z} ∧ P a} := by
    apply Set.Subset.antisymm
    . intro T hT; simp only [mem_setOf] at hT; simp only [mem_setOf]
      have hT1 := hT.1; have hT2 := hT.2; clear hT;
      have hPt: P T := by
        dsimp[P]; use hT1
      dsimp[is_triangle] at hT1
      rcases hT1 with ⟨x,y,z,hxyz1,hxyz2,hxyz3⟩; apply And.intro; dsimp[A]; use x; use y; use z; use hxyz2
      use (triv_lem_graphs_1 G hGgraph x y hxyz3.1).1; exact triv_lem_graphs_1 G hGgraph y z hxyz3.2.2
      use x; use y; use z
    . intro a ha; simp only [mem_setOf] at ha; simp only [mem_setOf]; have ha1 := ha.1; have ha2 := ha.2
      clear ha; rcases ha2 with ⟨x,y,z,hxyz1,hxyz2,hxyz3⟩; dsimp[P] at hxyz3; exact hxyz3
  rw[hlhs]; rw[hnear]
  have hrhsnear := @ncard_projections_trivial ℕ 1 (Omega G) (Omegafin G hGgraph hGfin) w
  rw[hrhsnear]; congr

  ext ⟨x,y,z⟩; apply Iff.intro;
  . intro hxyz; simp only [mem_setOf] at hxyz; simp only [mem_setOf]
    have hxyz1 := hxyz.1; have hxyz2 := hxyz.2.1; have hxyz3 := hxyz.2.2; clear hxyz
    dsimp[Omega]; dsimp[P] at hxyz3; have hxyz4 := hxyz3.1; have hxyz5 := hxyz3.2; clear hxyz3
    have hedges := triv_lem_graphs_4 G hGgraph x y z hxyz4; use hedges.1; use hedges.2.1; use hedges.2.2
    push_neg at hxyz5
    let Nw := closed_nbhd G w
    have hxoryorz : x ∈ Nw ∨ y ∈ Nw ∨ z ∈ Nw := by
      rcases hxyz5 with ⟨t,ht⟩
      have htxyz : t = x ∨ t = y ∨ t = z := ht.1
      rcases htxyz with (htx | hty | htz)
      left; rw[← htx]; exact ht.2
      right; left; rw[← hty]; exact ht.2;
      right; right; rw[← htz]; exact ht.2
    rcases hxoryorz with (hx | hy | hz)

    dsimp[Nw, closed_nbhd] at hx; by_cases hxw: x = w; swap; left;
    simp only [mem_insert_iff, mem_setOf_eq] at hx; refine triv_lem_graphs_3 G hGgraph x w ?_
    exact or_elim_triv _ _ hxw hx; right; left; rw[← hxw]; exact hedges.1

    by_cases hyw: y = w; swap; right; left; dsimp[Nw, closed_nbhd] at hy
    simp only [mem_insert_iff, mem_setOf_eq] at hy; refine triv_lem_graphs_3 G hGgraph y w ?_
    exact or_elim_triv _ _ hyw hy; right; right; rw[← hyw]; exact hedges.2.2

    by_cases hzw: z = w; swap; right; right; dsimp[Nw, closed_nbhd] at hz
    simp only [mem_insert_iff, mem_setOf_eq] at hz; refine triv_lem_graphs_3 G hGgraph z w ?_
    exact or_elim_triv _ _ hzw hz; left; rw[← hzw]; refine triv_lem_graphs_3 G hGgraph x z ?_
    exact hedges.2.1
  . intro hxyz; simp only [mem_setOf] at hxyz; simp only [mem_setOf]
    have hne: x ≠ y ∧ x ≠ z ∧ y ≠ z := by
      apply And.intro; exact triv_lem_graphs_2 G hGgraph x y hxyz.1
      apply And.intro; exact triv_lem_graphs_2 G hGgraph x z hxyz.2.1
      exact triv_lem_graphs_2 G hGgraph y z hxyz.2.2.1
    dsimp[Omega] at hxyz; apply And.intro; exact hne
    apply And.intro; dsimp[A]; use x; use y; use z
    apply And.intro; rfl; apply And.intro; exact (triv_lem_graphs_1 G hGgraph x y hxyz.1).1
    exact triv_lem_graphs_1 G hGgraph y z hxyz.2.2.1
    dsimp[P]; apply And.intro; dsimp[is_triangle]; use x; use y; use z; apply And.intro
    exact hne; use rfl; exact ⟨hxyz.1,hxyz.2.1,hxyz.2.2.1⟩
    rcases hxyz.2.2.2 with (hx | hy | hz)
    . push_neg; use x; apply And.intro;
      exact Set.mem_insert x {y, z}; dsimp[closed_nbhd];
      have hx1 := triv_lem_graphs_3 G hGgraph w x hx; exact Set.mem_insert_of_mem w hx1
    . push_neg; use y; apply And.intro; refine mem_insert_iff.mpr ?h.left.a; right;
      exact Set.mem_insert y {z}; dsimp[closed_nbhd];
      have hy1 := triv_lem_graphs_3 G hGgraph w y hy; exact Set.mem_insert_of_mem w hy1
    . push_neg; use z; apply And.intro; refine mem_insert_iff.mpr ?_; right
      exact Set.mem_insert_of_mem y rfl; dsimp[closed_nbhd];
      have hz1 := triv_lem_graphs_3 G hGgraph w z hz; exact Set.mem_insert_of_mem w hz1

--change from 6*sum_v |N_{T[v]}| to |Omega(G)|
lemma to_Omega (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite):
∑ v ∈ (Finite.toFinset hGfin), 6*{T : Set ℕ | (is_triangle G T) ∧ (T ∩ closed_nbhd G v ≠ ∅)}.ncard
= (Omega G).ncard := by
  symm
  have hnear := @ncard_projections_2 ℕ 1 (Omega G) (Omegafin G hGgraph hGfin) G.1 hGfin ?_
  rw[hnear]; congr with w
  exact to_Omega_0 G hGgraph hGfin w

  --finish by showing proj1 Omega(G) ⊆ G.1
  intro w hw; dsimp[proj1] at hw; rcases hw with ⟨x,y,z,hxyz⟩; dsimp[Omega] at hxyz
  have hxyz4 := hxyz.2.2.2; rcases hxyz4 with (hwx | hwy | hwz)
  exact (triv_lem_graphs_1 G hGgraph w x hwx).1; exact (triv_lem_graphs_1 G hGgraph w y hwy).1
  exact (triv_lem_graphs_1 G hGgraph w z hwz).1

--d(x)^3 = {(u,v,w) : u,v,w in N(x)}.ncard
lemma to_Sigma_0_0 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite) (x : ℕ):
{u | {u, x} ∈ G.2}.ncard ^ 3 = {(u,v,w) | {u,x} ∈ G.2 ∧ {v,x} ∈ G.2 ∧ {w,x} ∈ G.2}.ncard := by
  set Nx := {u | {u, x} ∈ G.2} with hNxdef
  have hnear: {(u,v,w) | {u,x} ∈ G.2 ∧ {v,x} ∈ G.2 ∧ {w,x} ∈ G.2} = Nx ×ˢ Nx ×ˢ Nx := rfl
  rw[hnear]

  have hNxfin : Nx.Finite := by
    exact nbhd_fin G hGgraph hGfin x

  set Nx1 := Finite.toFinset hNxfin

  have hnear1 : (Nx1 ×ˢ Nx1 ×ˢ Nx1).card = (Nx1.card)^3 := by
    have hnear10 := Finset.card_product Nx1 (Nx1 ×ˢ Nx1)
    rw[hnear10]
    have hnear11 := Finset.card_product Nx1 Nx1
    rw[hnear11]
    exact Eq.symm (pow_three Nx1.card)
  have hnear2 : Nx.ncard = Nx1.card := by
    exact ncard_eq_toFinset_card Nx hNxfin
  rw[hnear2]; rw[← hnear1]
  have hprodfin : (Nx ×ˢ Nx ×ˢ Nx).Finite := by
    refine Finite.prod hNxfin ?_; exact Finite.prod hNxfin hNxfin
  suffices: Nx1 ×ˢ Nx1 ×ˢ Nx1 = Finite.toFinset hprodfin
  . rw[this]
    exact Eq.symm (ncard_eq_toFinset_card (Nx ×ˢ Nx ×ˢ Nx) hprodfin)
  refine Finset.ext_iff.mpr ?_
  intro a; apply Iff.intro; intro ha; dsimp[Nx1] at ha; simp only [mem_product,Finite.mem_toFinset] at ha
  simp only [Finite.mem_toFinset, mem_prod]; exact ha; intro ha; simp only [mem_product]
  simp only [Finite.mem_toFinset,mem_prod] at ha; apply And.intro;
  refine (Finite.mem_toFinset hNxfin).mpr ?_; exact ha.1; apply And.intro
  refine (Finite.mem_toFinset hNxfin).mpr ?_; exact ha.2.1
  refine (Finite.mem_toFinset hNxfin).mpr ?_; exact ha.2.2

--change {u,x} to {x,u} etc.
lemma to_Sigma_0_1 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite) (x : ℕ):
{(u,v,w) | {u,x} ∈ G.2 ∧ {v,x} ∈ G.2 ∧ {w,x} ∈ G.2}.ncard =
{(u,v,w) | {x,u} ∈ G.2 ∧ {x,v} ∈ G.2 ∧ {x,w} ∈ G.2}.ncard := by
  congr; ext ⟨u,v,w⟩; apply Iff.intro; intro huvw; simp only [mem_setOf_eq] at huvw
  simp only [mem_setOf_eq]; apply And.intro; exact triv_lem_graphs_3 G hGgraph u x huvw.1
  use triv_lem_graphs_3 G hGgraph v x huvw.2.1; exact triv_lem_graphs_3 G hGgraph w x huvw.2.2
  intro huvw; simp only [mem_setOf_eq] at huvw; simp only [mem_setOf_eq]
  use triv_lem_graphs_3 G hGgraph x u huvw.1; use triv_lem_graphs_3 G hGgraph x v huvw.2.1
  exact triv_lem_graphs_3 G hGgraph x w huvw.2.2

--include x in the tuple (and perserve ncard)
lemma to_Sigma_0_2 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite) (x : ℕ):
{(u,v,w) | {x,u} ∈ G.2 ∧ {x,v} ∈ G.2 ∧ {x,w} ∈ G.2}.ncard =
{a : ℕ × ℕ × ℕ × ℕ | ∃(u v w : ℕ), a = (x,u,v,w) ∧ {x,u} ∈ G.2 ∧ {x,v} ∈ G.2 ∧ {x,w} ∈ G.2}.ncard := by
  let s := {(u,v,w) | {x,u} ∈ G.2 ∧ {x,v} ∈ G.2 ∧ {x,w} ∈ G.2}
  let t := {a : ℕ × ℕ × ℕ × ℕ | ∃(u v w : ℕ), a = (x,u,v,w) ∧ {x,u} ∈ G.2 ∧ {x,v} ∈ G.2 ∧ {x,w} ∈ G.2}
  let f : (b : ℕ × ℕ × ℕ) → (b ∈ s) →  ℕ × ℕ × ℕ × ℕ := fun b ↦ fun hbins ↦ (x,b.1,b.2.1,b.2.2)
  apply Set.ncard_congr f ?_ ?_ ?_

  intro a ha; dsimp[s] at ha; simp only [mem_setOf_eq]; set u := a.1; set v := a.2.1; set w := a.2.2;
  use u; use v; use w

  intro a b hains hbins hfab; dsimp[s] at hains; dsimp[s] at hbins; dsimp[f] at hfab
  set u1 := a.1; set v1 := a.2.1; set w1 := a.2.2; set u2 := b.1; set v2 := b.2.1; set w2 := b.2.2
  injection hfab

  intro b hb; simp only [mem_setOf_eq] at hb; rcases hb with ⟨u,v,w,huvw1,huvw2⟩; use (u,v,w); use huvw2
  dsimp[f]; symm; exact huvw1

--in order to change from sum_v d(v)^3 to |Sigma(G)|, show d(x)^3 = |marginal Sigma(G) x|
lemma to_Sigma_0 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite) (x : ℕ):
deg G x ^ 3 = (marginal1 (Sigma G) x).ncard := by
  dsimp[deg]

  have hlhs1: {u | {u, x} ∈ G.2}.ncard ^ 3 = {(u,v,w) | {u,x} ∈ G.2 ∧ {v,x} ∈ G.2 ∧ {w,x} ∈ G.2}.ncard := by
    exact to_Sigma_0_0 G hGgraph hGfin x
  have hlhs2: {(u,v,w) | {u,x} ∈ G.2 ∧ {v,x} ∈ G.2 ∧ {w,x} ∈ G.2}.ncard =
  {(u,v,w) | {x,u} ∈ G.2 ∧ {x,v} ∈ G.2 ∧ {x,w} ∈ G.2}.ncard := by
    exact to_Sigma_0_1 G hGgraph hGfin x
  have hlhs3: {(u,v,w) | {x,u} ∈ G.2 ∧ {x,v} ∈ G.2 ∧ {x,w} ∈ G.2}.ncard =
  {a : ℕ × ℕ × ℕ × ℕ | ∃(u v w : ℕ), a = (x,u,v,w) ∧ {x,u} ∈ G.2 ∧ {x,v} ∈ G.2 ∧ {x,w} ∈ G.2}.ncard := by
    exact to_Sigma_0_2 G hGgraph hGfin x

  rw[hlhs1, hlhs2,hlhs3]; congr; dsimp[marginal1, Sigma]; ext a; apply Iff.intro
  intro ha; rw[mem_setOf] at ha; rw[mem_setOf]; rcases ha with ⟨u,v,w,huvw⟩; rw[huvw.1]
  simp only [Prod.mk.injEq, true_and, exists_and_left, exists_eq', and_true]
  exact huvw.2; intro ha; rw[mem_setOf] at ha; rw[mem_setOf]; have ha1 := ha.1; have ha2 := ha.2; clear ha
  rcases ha2 with ⟨u,v,w,huvw⟩; use u; use v; use w; use huvw; rw[huvw] at ha1; exact ha1

--change from sum_v d(v)^3 to |Sigma(G)|
lemma to_Sigma (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite):
∑ v ∈ (Finite.toFinset hGfin), (deg G v)^3 = (Sigma G).ncard := by
  have hnear := @ncard_projections_2 ℕ 1 (Sigma G) (Sigmafin G hGgraph hGfin) G.1 hGfin ?_
  rw[hnear]; congr with x; exact to_Sigma_0 G hGgraph hGfin x

  --finish by showing proj1 Sigma(G) ⊆ G.1
  intro x hx; dsimp[proj1] at hx; rcases hx with ⟨u,v,w,huvw⟩; dsimp[Sigma] at huvw
  exact (triv_lem_graphs_1 G hGgraph x u huvw.1).1

lemma basic_logic_lem_1 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (u v w : ℕ)
(h2new : {u, v} ∉ G.2 → {u, w} ∉ G.2 → {v, w} ∈ G.2)
(hc1 : ¬({u, v} ∈ G.2 ∧ {u, w} ∉ G.2 ∧ {v, w} ∉ G.2))
(hc2 : ¬({u, v} ∉ G.2 ∧ {u, w} ∈ G.2 ∧ {v, w} ∉ G.2))
(hc3 : ¬({u, v} ∉ G.2 ∧ {u, w} ∉ G.2 ∧ {v, w} ∈ G.2))
(hc4 : ¬({u, v} ∈ G.2 ∧ {u, w} ∈ G.2 ∧ {v, w} ∉ G.2))
(hc5 : ¬({u, v} ∈ G.2 ∧ {u, w} ∉ G.2 ∧ {v, w} ∈ G.2))
(hc6 : ¬({u, v} ∉ G.2 ∧ {u, w} ∈ G.2 ∧ {v, w} ∈ G.2))
: {u, v} ∈ G.2 ∧ {u, w} ∈ G.2 ∧ {v, w} ∈ G.2 := by

  have h2 : {u,v} ∈ G.2 ∨ {u,w} ∈ G.2 ∨ {v,w} ∈ G.2 := by
    contrapose! h2new; use h2new.1; use h2new.2.1; exact h2new.2.2
  clear h2new
  push_neg at hc1; push_neg at hc2; push_neg at hc3; push_neg at hc4; push_neg at hc5
  push_neg at hc6

  rcases h2 with (huv | huw | hvw)
  . use huv; have hc1new := hc1 huv; clear hc1; have hc4new := hc4 huv; clear hc4
    have hc5new := hc5 huv; clear hc5;
    have huw : {u,w} ∈ G.2 := not_mem_compl_iff.mp fun a ↦ hc5new a (hc1new a)
    apply And.intro; exact huw; exact hc4new huw
  . have huv : {u,v} ∈ G.2 := by
      tauto
    use huv; use huw; exact hc4 huv huw
  . have huv: {u,v} ∈ G.2 := by
      tauto
    use huv; apply And.intro; swap; exact hvw; have hc5new := hc5 huv; clear hc5
    exact not_mem_compl_iff.mp fun a ↦ hc5new a hvw

lemma basic_logic_lem_2 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (z u v w : ℕ)
(h2 : {z, u} ∈ G.2 ∨ {z, v} ∈ G.2 ∨ {z, w} ∈ G.2)
(hc1 : ¬({z, u} ∈ G.2 ∧ {z, v} ∉ G.2 ∧ {z, w} ∉ G.2))
(hc2 : ¬({z, u} ∉ G.2 ∧ {z, v} ∈ G.2 ∧ {z, w} ∉ G.2))
(hc3 : ¬({z, u} ∉ G.2 ∧ {z, v} ∉ G.2 ∧ {z, w} ∈ G.2))
(hc4 : ¬({z, u} ∈ G.2 ∧ {z, v} ∈ G.2 ∧ {z, w} ∉ G.2))
(hc5 : ¬({z, u} ∈ G.2 ∧ {z, v} ∉ G.2 ∧ {z, w} ∈ G.2))
(hc6 : ¬({z, u} ∉ G.2 ∧ {z, v} ∈ G.2 ∧ {z, w} ∈ G.2)):
{z, u} ∈ G.2 ∧ {z, v} ∈ G.2 ∧ {z, w} ∈ G.2 := by
  push_neg at hc1; push_neg at hc2; push_neg at hc3; push_neg at hc4; push_neg at hc5; push_neg at hc6
  rcases h2 with (hzu | hzv | hzw)
  . use hzu; have hc1new := hc1 hzu; have hc4new := hc4 hzu; have hc5new := hc5 hzu; clear hc1; clear hc4
    clear hc5; have hzv : {z,v} ∈ G.2 := not_mem_compl_iff.mp fun a ↦ hc5new a (hc1new a); use hzv
    exact hc4new hzv
  . have hzu : {z,u} ∈ G.2 := by
      tauto
    use hzu; use hzv; exact hc4 hzu hzv
  . have hzu: {z,u} ∈ G.2 := by
      tauto
    have hzv : {z,v} ∈ G.2 := by
      tauto
    use hzu

noncomputable def funct (G : Set ℕ × Set (Set ℕ)) : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ := fun (x,u,v,w) ↦
    if {u,v} ∈ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∉ G.2 then (w,x,u,v)
    else if {u,v} ∉ G.2 ∧ {u,w} ∈ G.2 ∧ {v,w} ∉ G.2 then (v,w,x,u)
    else if {u,v} ∉ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∈ G.2 then ⟨u,v,w,x⟩
    else if {u,v} ∈ G.2 ∧ {u,w} ∈ G.2 ∧ {v,w} ∉ G.2 then (w,x,u,v)
    else if {u,v} ∈ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∈ G.2 then (w,u,v,x)
    else if {u,v} ∉ G.2 ∧ {u,w} ∈ G.2 ∧ {v,w} ∈ G.2 then (u,w,v,x)
    else (x,u,v,w)

lemma f_permutes_1 (G : Set ℕ × Set (Set ℕ)) (x u v w : ℕ):
(funct G) (x,u,v,w) ∈
({(w,x,u,v),(v,w,x,u),(u,v,w,x),(w,x,u,v),(w,u,v,x),(u,w,v,x),(x,u,v,w)} : Set (ℕ × ℕ × ℕ × ℕ)):= by
  dsimp[funct]; by_cases hc1: {u,v} ∈ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∉ G.2; simp only [hc1];
  simp only [not_false_eq_true, and_self, ↓reduceIte, mem_insert_iff, Prod.mk.injEq, true_and,
    mem_singleton_iff, true_or, or_true, Set.insert_eq_of_mem]
  by_cases hc2: {u,v} ∉ G.2 ∧ {u,w} ∈ G.2 ∧ {v,w} ∉ G.2; simp only [hc2];
  simp only [not_true_eq_false, not_false_eq_true, and_true, and_self, ↓reduceIte, mem_insert_iff,
    Prod.mk.injEq, true_and, mem_singleton_iff, true_or, or_true, Set.insert_eq_of_mem]
  by_cases hc3: {u,v} ∉ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∈ G.2; simp only [hc3]
  simp only [not_false_eq_true, not_true_eq_false, and_false, and_self, ↓reduceIte, mem_insert_iff,
    Prod.mk.injEq, true_and, mem_singleton_iff, true_or, or_true, Set.insert_eq_of_mem, and_true]
  by_cases hc4: {u,v} ∈ G.2 ∧ {u,w} ∈ G.2 ∧ {v,w} ∉ G.2; simp only [hc4]
  simp only [not_true_eq_false, not_false_eq_true, and_true, and_false, ↓reduceIte, and_self,
    mem_insert_iff, Prod.mk.injEq, true_and, mem_singleton_iff, true_or, or_true,
    Set.insert_eq_of_mem]
  by_cases hc5: {u,v} ∈ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∈ G.2; simp only [hc5]
  simp only [not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self, and_true,
    mem_insert_iff, Prod.mk.injEq, true_and, mem_singleton_iff, true_or, or_true,
    Set.insert_eq_of_mem]
  by_cases hc6: {u,v} ∉ G.2 ∧ {u,w} ∈ G.2 ∧ {v,w} ∈ G.2; simp only [hc6]
  simp only [not_true_eq_false, and_self, ↓reduceIte, not_false_eq_true, and_false, and_true,
    mem_insert_iff, Prod.mk.injEq, true_and, mem_singleton_iff, true_or, or_true,
    Set.insert_eq_of_mem]
  simp only [hc1, hc2, hc3, hc4, hc5, hc6]
  simp only [↓reduceIte, mem_insert_iff, Prod.mk.injEq, true_and, mem_singleton_iff, true_or,
    or_true, Set.insert_eq_of_mem]

lemma f_injective (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G):
InjOn (funct G) ((Sigma G) \ (Wgraph G)) := by
  intro ⟨x1,u1,v1,w1⟩ h1 ⟨x2,u2,v2,w2⟩ h2 hf12

  have h11 := h1.1; have h12 := h1.2; clear h1; have h21 := h2.1; have h22 := h2.2; clear h2

  dsimp[Sigma] at h11; dsimp[Wgraph] at h12; dsimp[Sigma] at h21; dsimp[Wgraph] at h22


  by_cases hc1: {u1,v1} ∈ G.2 ∧ {u1,w1} ∉ G.2 ∧ {v1,w1} ∉ G.2
  by_cases hc11: {u2,v2} ∈ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc12: {u2,v2} ∉ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; simp only [hc1,hc12] at hf12; aesop
  by_cases hc13: {u2,v2} ∉ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; simp only [hc1,hc13] at hf12; aesop
  by_cases hc14: {u2,v2} ∈ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; simp only [hc1,hc14] at hf12; aesop
  by_cases hc15: {u2,v2} ∈ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; simp only [hc1,hc15] at hf12; aesop
  by_cases hc16: {u2,v2} ∉ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; simp only [hc1,hc16] at hf12; aesop
  dsimp[funct] at hf12; simp only [hc1,hc11,hc12,hc13,hc14,hc15,hc16] at hf12
  simp only [not_false_eq_true, and_self, ↓reduceIte, Prod.mk.injEq] at hf12
  apply False.elim; rw[hf12.1, hf12.2.2.1] at hc1;
  exact hc1.2.1 (triv_lem_graphs_3 G hGgraph _ _ h21.2.1)

  by_cases hc2: {u1,v1} ∉ G.2 ∧ {u1,w1} ∈ G.2 ∧ {v1,w1} ∉ G.2
  by_cases hc21: {u2,v2} ∈ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc22: {u2,v2} ∉ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; simp only [hc2,hc22] at hf12; aesop
  by_cases hc23: {u2,v2} ∉ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; simp only [hc2,hc23] at hf12; aesop
  by_cases hc24: {u2,v2} ∈ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; simp only [hc2,hc24] at hf12;
  simp only [↓reduceIte, not_true_eq_false, not_false_eq_true, and_true, and_false, and_self] at hf12
  injections h1 h2 h2 h3 h3 h4; apply False.elim; rw[h1,h2] at hc2
  exact hc2.2.2 (triv_lem_graphs_3 G hGgraph _ _ h21.2.2)
  by_cases hc25: {u2,v2} ∈ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc26: {u2,v2} ∉ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; aesop
  dsimp[funct] at hf12; simp only [hc2,hc21,hc22,hc23,hc24,hc25,hc26] at hf12
  simp only [not_true_eq_false, not_false_eq_true, and_true, and_self, ↓reduceIte, Prod.mk.injEq] at hf12
  aesop

  by_cases hc3: {u1,v1} ∉ G.2 ∧ {u1,w1} ∉ G.2 ∧ {v1,w1} ∈ G.2
  by_cases hc31: {u2,v2} ∈ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc32: {u2,v2} ∉ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; simp only [hc3,hc32] at hf12; aesop
  by_cases hc33: {u2,v2} ∉ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; simp only [hc3,hc33] at hf12; aesop
  by_cases hc34: {u2,v2} ∈ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; simp only [hc3,hc34] at hf12;
  simp only [↓reduceIte, not_true_eq_false, not_false_eq_true, and_true, and_false, and_self] at hf12
  injections h1 h2 h2 h3 h3 h4; apply False.elim; rw[h1,h2] at hc3
  exact hc3.1 (triv_lem_graphs_3 G hGgraph _ _ h21.2.2)
  by_cases hc35: {u2,v2} ∈ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; simp only [hc3,hc35] at hf12
  simp only [not_false_eq_true, not_true_eq_false, and_false, and_self, ↓reduceIte, and_true,Prod.mk.injEq] at hf12
  apply False.elim; rw[hf12.1, hf12.2.2.1] at hc3; exact hc3.2.1 (triv_lem_graphs_3 G hGgraph _ _ hc35.2.2)
  by_cases hc36: {u2,v2} ∉ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; aesop
  dsimp[funct] at hf12; simp only [hc3,hc31,hc32,hc33,hc34,hc35,hc36] at hf12
  simp only [not_true_eq_false, not_false_eq_true, and_true, and_self, ↓reduceIte, Prod.mk.injEq] at hf12
  aesop

  by_cases hc4: {u1,v1} ∈ G.2 ∧ {u1,w1} ∈ G.2 ∧ {v1,w1} ∉ G.2
  by_cases hc41: {u2,v2} ∈ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc42: {u2,v2} ∉ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; simp only [hc4,hc42] at hf12
  simp only [not_true_eq_false, not_false_eq_true, and_true, and_false, ↓reduceIte, and_self, Prod.mk.injEq] at hf12
  apply False.elim; rw[← hf12.1, ← hf12.2.1] at hc42; exact hc42.2.2 (triv_lem_graphs_3 G hGgraph _ _ h11.2.2)
  by_cases hc43: {u2,v2} ∉ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; simp only [hc4,hc43] at hf12; aesop
  by_cases hc44: {u2,v2} ∈ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc45: {u2,v2} ∈ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc46: {u2,v2} ∉ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; aesop
  dsimp[funct] at hf12; simp only [hc4,hc41,hc42,hc43,hc44,hc45,hc46] at hf12
  simp only [not_true_eq_false, not_false_eq_true, and_true, and_false, ↓reduceIte, and_self,
    Prod.mk.injEq] at hf12
  apply False.elim; rw[hf12.1, hf12.2.2.2] at hc4; exact hc4.2.2 (triv_lem_graphs_3 G hGgraph _ _ h21.2.2)

  by_cases hc5: {u1,v1} ∈ G.2 ∧ {u1,w1} ∉ G.2 ∧ {v1,w1} ∈ G.2
  by_cases hc51: {u2,v2} ∈ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc52: {u2,v2} ∉ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc53: {u2,v2} ∉ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; simp only [hc5,hc53] at hf12
  simp only [not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self, and_true, Prod.mk.injEq] at hf12
  apply False.elim; rw[hf12.1, hf12.2.2.1] at hc5; exact hc53.2.1 (triv_lem_graphs_3 G hGgraph _ _ hc5.2.2)
  by_cases hc54: {u2,v2} ∈ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc55: {u2,v2} ∈ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc56: {u2,v2} ∉ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; simp only [hc5,hc56] at hf12
  simp only [not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self, and_true, Prod.mk.injEq] at hf12
  apply False.elim; rw[hf12.1, hf12.2.1] at hc5; exact hc5.2.1 (triv_lem_graphs_3 G hGgraph _ _ hc56.2.1)
  dsimp[funct] at hf12; simp only [hc5,hc51,hc52,hc53,hc54,hc55,hc56] at hf12
  simp only [not_true_eq_false, not_false_eq_true, and_true, and_false, ↓reduceIte, and_self,
    Prod.mk.injEq] at hf12
  apply False.elim; rw[hf12.1,hf12.2.1] at hc5; exact hc5.2.1 (triv_lem_graphs_3 G hGgraph _ _ h21.1)

  by_cases hc6: {u1,v1} ∉ G.2 ∧ {u1,w1} ∈ G.2 ∧ {v1,w1} ∈ G.2
  by_cases hc61: {u2,v2} ∈ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc62: {u2,v2} ∉ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc63: {u2,v2} ∉ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc64: {u2,v2} ∈ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∉ G.2
  dsimp[funct] at hf12; aesop
  by_cases hc65: {u2,v2} ∈ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; simp only [hc6,hc65] at hf12
  simp only [not_true_eq_false, and_self, ↓reduceIte, not_false_eq_true, and_false, and_true, Prod.mk.injEq] at hf12
  apply False.elim; rw[hf12.1, hf12.2.2.1] at hc6; exact hc6.1 (triv_lem_graphs_3 G hGgraph _ _ hc65.2.2)
  by_cases hc66: {u2,v2} ∉ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∈ G.2
  dsimp[funct] at hf12; aesop
  dsimp[funct] at hf12; aesop

  dsimp[funct] at hf12; simp only [hc1,hc2,hc3,hc4,hc5,hc6] at hf12; simp only [↓reduceIte] at hf12
  by_cases hc71: {u2,v2} ∈ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∉ G.2
  simp only [hc71] at hf12; simp only [not_false_eq_true, and_self, ↓reduceIte, Prod.mk.injEq] at hf12
  apply False.elim; rw[← hf12.1, ← hf12.2.2.1] at hc71; exact hc71.2.1 (triv_lem_graphs_3 G hGgraph _ _ h11.2.1)
  by_cases hc72: {u2,v2} ∉ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∉ G.2
  aesop
  by_cases hc73: {u2,v2} ∉ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∈ G.2
  simp only [hc73] at hf12;
  simp only [not_false_eq_true, not_true_eq_false, and_false, and_self, ↓reduceIte, Prod.mk.injEq] at hf12
  rw[← hf12.1, ← hf12.2.1] at hc73; apply False.elim; exact hc73.1 h11.1
  by_cases hc74: {u2,v2} ∈ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∉ G.2
  simp only [hc74] at hf12;
  simp only [not_true_eq_false, not_false_eq_true, and_true, and_false, ↓reduceIte, and_self, Prod.mk.injEq] at hf12
  apply False.elim; rw[← hf12.1, ← hf12.2.2.2] at hc74; exact hc74.2.2 (triv_lem_graphs_3 G hGgraph _ _ h11.2.2)
  by_cases hc75: {u2,v2} ∈ G.2 ∧ {u2,w2} ∉ G.2 ∧ {v2,w2} ∈ G.2
  simp only [hc75] at hf12
  simp only [not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self, and_true, Prod.mk.injEq] at hf12
  apply False.elim; rw[← hf12.1, ← hf12.2.1] at hc75; exact hc75.2.1 (triv_lem_graphs_3 G hGgraph _ _ h11.1)
  by_cases hc76: {u2,v2} ∉ G.2 ∧ {u2,w2} ∈ G.2 ∧ {v2,w2} ∈ G.2
  simp only [hc76] at hf12;
  simp only [not_true_eq_false, and_self, ↓reduceIte, not_false_eq_true, and_false, and_true, Prod.mk.injEq] at hf12
  aesop
  simp only [hc71,hc72,hc73,hc74,hc75,hc76] at hf12; simp only [↓reduceIte, Prod.mk.injEq] at hf12
  refine Prod.mk.inj_iff.mpr ?_; use hf12.1; refine Prod.mk.inj_iff.mpr ?_; use hf12.2.1
  refine Prod.mk.inj_iff.mpr ?_; use hf12.2.2.1; exact hf12.2.2.2

lemma f_maps_to_Omega (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G):
(funct G) '' (Sigma G \ Wgraph G) ⊆ Omega G := by
  intro ⟨a,b,c,d⟩ habcd; simp only [Set.mem_image, mem_diff, Prod.exists] at habcd
  rcases habcd with ⟨x,u,v,w,⟨h1,h2⟩,h3⟩; dsimp[Sigma] at h1; dsimp[Wgraph] at h2
  push_neg at h2

  have hux : {u,x} ∈ G.2 := triv_lem_graphs_3 G hGgraph x u h1.1
  have hvx : {v,x} ∈ G.2 := triv_lem_graphs_3 G hGgraph x v h1.2.1
  have hwx : {w,x} ∈ G.2 := triv_lem_graphs_3 G hGgraph x w h1.2.2
  have h2new := h2 hux hvx hwx; clear h2

  by_cases hc1: {u,v} ∈ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∉ G.2
  dsimp[funct] at h3; simp only [hc1, not_false_eq_true, and_self, ↓reduceIte] at h3;  rw[← h3]
  dsimp[Omega]; use h1.1; use h1.2.1; use hc1.1; left; exact hwx

  by_cases hc2: {u,v} ∉ G.2 ∧ {u,w} ∈ G.2 ∧ {v,w} ∉ G.2
  dsimp[funct] at h3; simp only [hc2, not_true_eq_false, not_false_eq_true, and_true, and_self, ↓reduceIte] at h3
  rw[← h3]; dsimp[Omega]; use hwx; use triv_lem_graphs_3 G hGgraph u w hc2.2.1; use h1.1; right; left
  exact hvx

  by_cases hc3: {u,v} ∉ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∈ G.2
  dsimp[funct] at h3; simp only [hc3, not_false_eq_true, not_true_eq_false, and_false, and_self, ↓reduceIte] at h3
  rw[← h3]; dsimp[Omega]; use hc3.2.2; use hvx; use hwx; right; right; exact hux

  by_cases hc4: {u,v} ∈ G.2 ∧ {u,w} ∈ G.2 ∧ {v,w} ∉ G.2
  dsimp[funct] at h3; simp only [hc4, not_true_eq_false, not_false_eq_true, and_true, and_false, ↓reduceIte, and_self] at h3;
  rw[← h3]; dsimp[Omega]; use h1.1; use h1.2.1; use hc4.1; left; exact hwx

  by_cases hc5: {u,v} ∈ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∈ G.2
  dsimp[funct] at h3; simp only [hc5, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self, and_true] at h3;
  rw[← h3]; dsimp[Omega]; use hc5.1; use hux; use hvx; right; left; exact triv_lem_graphs_3 G hGgraph v w hc5.2.2

  by_cases hc6: {u,v} ∉ G.2 ∧ {u,w} ∈ G.2 ∧ {v,w} ∈ G.2
  dsimp[funct] at h3; simp only [hc6, not_true_eq_false, and_self, ↓reduceIte, not_false_eq_true, and_false, and_true] at h3;
  rw[← h3]; dsimp[Omega]; use triv_lem_graphs_3 G hGgraph v w hc6.2.2; use hwx; use hvx; left; exact hc6.2.1

  have hc7: {u,v} ∈ G.2 ∧ {u,w} ∈ G.2 ∧ {v,w} ∈ G.2 := by
    exact basic_logic_lem_1 G hGgraph u v w h2new hc1 hc2 hc3 hc4 hc5 hc6
  dsimp[funct] at h3; simp only [hc1,hc2,hc3,hc4,hc5,hc6] at h3; simp only [↓reduceIte] at h3
  rw[← h3]; dsimp[Omega]; use hc7.1; use hc7.2.1; use hc7.2.2; left; exact h1.1

lemma f_surjective (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G):
Omega G ⊆ (funct G) '' (Sigma G \ Wgraph G) := by
  intro ⟨z,u,v,w⟩ h; dsimp[Omega] at h; have huv := h.1; have huw := h.2.1; have hvw := h.2.2.1

  have hvu := triv_lem_graphs_3 G hGgraph u v huv
  have hwu := triv_lem_graphs_3 G hGgraph u w huw
  have hwv := triv_lem_graphs_3 G hGgraph v w hvw

  have h2 := h.2.2.2; clear h
  simp only [Set.mem_image, mem_diff, Prod.exists]

  by_cases hc1: {z,u} ∈ G.2 ∧ {z,v} ∉ G.2 ∧ {z,w} ∉ G.2
  use u; use v; use w; use z; apply And.intro; swap; dsimp[funct]
  have h: {v,w} ∈ G.2 ∧ {v,z} ∉ G.2 ∧ {w,z} ∉ G.2 := by
    apply And.intro; exact hvw; apply And.intro; by_contra hcontra
    have hnear := triv_lem_graphs_3 G hGgraph v z hcontra; exact hc1.2.1 hnear
    by_contra hcontra; have hnear := triv_lem_graphs_3 G hGgraph w z hcontra; exact hc1.2.2 hnear
  simp only [h]; simp only [not_true_eq_false, not_false_eq_true, and_true, and_false, ↓reduceIte, and_self]
  have hsigma: (u,v,w,z) ∈ Sigma G := by
    dsimp[Sigma]; use huv; use huw; exact triv_lem_graphs_3 G hGgraph z u hc1.1
  apply And.intro; exact hsigma; dsimp[Wgraph]; push_neg; intro h00 h01 h02 h03 h04
  exact False.elim (h03 hvw)

  by_cases hc2: {z,u} ∉ G.2 ∧ {z,v} ∈ G.2 ∧ {z,w} ∉ G.2
  use v; use w; use z; use u; apply And.intro; swap; dsimp[funct]
  have h: {w, z} ∉ G.2 ∧ {w, u} ∈ G.2 ∧ {z, u} ∉ G.2 := by
    apply And.intro; by_contra hcontra; have hnear := triv_lem_graphs_3 G hGgraph _ _ hcontra
    exact hc2.2.2 hnear; use hwu; exact hc2.1
  simp only [h]; simp only [not_true_eq_false, not_false_eq_true, and_true, and_self, ↓reduceIte]
  have hsigma: (v, w, z, u) ∈ Sigma G := by
    dsimp[Sigma]; use hvw; use triv_lem_graphs_3 G hGgraph _ _ hc2.2.1
  apply And.intro; exact hsigma; dsimp[Wgraph]; push_neg; intro h00 h01 h02 h03 h04; exact False.elim (h04 hwu)

  by_cases hc3: {z,u} ∉ G.2 ∧ {z,v} ∉ G.2 ∧ {z,w} ∈ G.2
  use w; use z; use u; use v; apply And.intro; swap; dsimp[funct]
  have h: {z, u} ∉ G.2 ∧ {z, v} ∉ G.2 ∧ {u, v} ∈ G.2 := by
    apply And.intro; exact hc3.1; apply And.intro; exact hc3.2.1; exact huv
  simp only[h]; simp only [not_false_eq_true, not_true_eq_false, and_false, and_self, ↓reduceIte]
  have hsigma: (w, z, u, v) ∈ Sigma G := by
    dsimp[Sigma]; use triv_lem_graphs_3 G hGgraph _ _ hc3.2.2
  apply And.intro; exact hsigma; dsimp[Wgraph]; push_neg; intro h00 h01 h02 h03 h04; exact huv

  by_cases hc4: {z,u} ∈ G.2 ∧ {z,v} ∈ G.2 ∧ {z,w} ∉ G.2
  use u; use v; use w; use z; apply And.intro; swap; dsimp[funct]
  have h: {v, w} ∈ G.2 ∧ {v, z} ∈ G.2 ∧ {w, z} ∉ G.2 := by
    use hvw; use triv_lem_graphs_3 G hGgraph _ _ hc4.2.1; by_contra hcontra
    have hnear := triv_lem_graphs_3 G hGgraph _ _ hcontra; exact hc4.2.2 hnear
  simp only [h]; simp only [not_true_eq_false, not_false_eq_true, and_true, and_false, ↓reduceIte, and_self]
  apply And.intro; dsimp[Sigma]; use huv; use huw; exact triv_lem_graphs_3 G hGgraph _ _ hc4.1
  dsimp[Wgraph]; push_neg; intro h00 h01 h02 h03 h04; exact False.elim (h03 hvw)

  by_cases hc5: {z,u} ∈ G.2 ∧ {z,v} ∉ G.2 ∧ {z,w} ∈ G.2
  use w; use z; use v; use u; apply And.intro; swap; dsimp[funct]
  have h: {z, v} ∉ G.2 ∧ {z, u} ∈ G.2 ∧ {v, u} ∈ G.2 := by
    use hc5.2.1; use hc5.1
  simp only [h]; simp only [not_true_eq_false, and_self, ↓reduceIte, not_false_eq_true, and_false, and_true]
  apply And.intro; dsimp[Sigma]; use triv_lem_graphs_3 G hGgraph _ _ hc5.2.2; dsimp[Wgraph]; push_neg; intro h00 h01 h02 h03 h04; exact hvu

  by_cases hc6: {z,u} ∉ G.2 ∧ {z,v} ∈ G.2 ∧ {z,w} ∈ G.2
  use w; use u; use v; use z; apply And.intro; swap; dsimp[funct]
  have h: {u, v} ∈ G.2 ∧ {u, z} ∉ G.2 ∧ {v, z} ∈ G.2 := by
    use huv; apply And.intro; by_contra hcontra; have hnear := triv_lem_graphs_3 G hGgraph _ _ hcontra
    exact hc6.1 hnear; exact triv_lem_graphs_3 G hGgraph _ _ hc6.2.1
  simp only [h]; simp only [not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self, and_true]
  apply And.intro; dsimp[Sigma]; use hwu; use hwv; exact triv_lem_graphs_3 G hGgraph _ _ hc6.2.2
  dsimp[Wgraph]; push_neg; intro h00 h01 h02 h03 h04; exact False.elim (h03 huv)

  have hc7: {z,u} ∈ G.2 ∧ {z,v} ∈ G.2 ∧ {z,w} ∈ G.2 := by
    exact basic_logic_lem_2 G hGgraph z u v w h2 hc1 hc2 hc3 hc4 hc5 hc6
  use z; use u; use v; use w; apply And.intro; swap; dsimp[funct]
  have h: {u, v} ∈ G.2 ∧ {u, w} ∈ G.2 ∧ {v, w} ∈ G.2 := by
    use huv
  simp only [h]; simp only [not_true_eq_false, and_self, and_false, ↓reduceIte, and_true]
  apply And.intro; dsimp[Sigma]; exact hc7; dsimp[Wgraph]; push_neg; intro h00 h01 h02 h03 h04; exact hvw

lemma key_equality (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (hGfin: G.1.Finite):
∑ v ∈ (Finite.toFinset hGfin), 6*{T : Set ℕ | (is_triangle G T) ∧ (T ∩ closed_nbhd G v ≠ ∅)}.ncard
+ (Wgraph G).ncard = ∑ v ∈ (Finite.toFinset hGfin), (deg G v)^3 := by

  rw[to_Omega G hGgraph hGfin, to_Sigma G hGgraph hGfin]

  suffices: (Omega G).ncard = ((Sigma G)\(Wgraph G)).ncard
  . rw[this]; apply Set.ncard_diff_add_ncard_of_subset ?_ ?_; swap; exact Sigmafin G hGgraph hGfin
    intro ⟨w,x,y,z⟩ ha; dsimp[Wgraph] at ha; dsimp[Sigma]; apply And.intro
    exact triv_lem_graphs_3 G hGgraph x w ha.1; apply And.intro; exact triv_lem_graphs_3 G hGgraph y w ha.2.1
    exact triv_lem_graphs_3 G hGgraph z w ha.2.2.1

  have hnear := @Set.ncard_image_of_injOn _ _ ((Sigma G) \ (Wgraph G)) (funct G) (f_injective G hGgraph)
  rw[← hnear]; congr; clear hnear

  --show f '' = Omega
  apply Set.Subset.antisymm; swap

  --show the range is contained in Omega
  exact f_maps_to_Omega G hGgraph

  --show Omega is contained in the range
  exact f_surjective G hGgraph

end keyeq
