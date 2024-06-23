import Gls.graph_definitions

import Mathlib

open graph_defs

set_option linter.unusedVariables false

open Set
open scoped Classical
open Finset BigOperators

namespace triv_lem_sets

lemma triv_lem_sets_0 (x x1 y z : ℕ) (hynez : y ≠ z) (hxx1yz : ({x,x1} : Set ℕ) = ({y,z} : Set ℕ)):
(y = x ∧ z = x1) ∨ (y = x1 ∧ z = x) := by
  have hyinyz : y ∈ ({y,z} : Set ℕ) := by tauto
  have hyinxx1 : y ∈ ({x,x1} : Set ℕ) := by rw[← hxx1yz] at hyinyz; tauto
  have hzinyz : z ∈ ({y,z} : Set ℕ) := by tauto
  have hzinxx1 : z ∈ ({x,x1} : Set ℕ) := by rw[← hxx1yz] at hzinyz; tauto
  simp at hyinxx1; simp at hzinxx1
  rcases hyinxx1 with (hyx | hyx1)
  rcases hzinxx1 with (hzx | hzx1)
  rw[hyx] at hynez; rw[hzx] at hynez; tauto
  left; tauto
  rcases hzinxx1 with (hzx | hzx1)
  right; tauto
  rw[hyx1] at hynez; rw[hzx1] at hynez; tauto

lemma triv_lem_sets_1 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (x x1 x2 : ℕ) (hxx1inG : {x,x1} ∈ G.2)
(hxx1xx2 : ({x,x1} : Set ℕ) = ({x,x2} : Set ℕ)) : x1 = x2 := by
  have hxx1 := hGgraph _ hxx1inG
  rcases hxx1 with ⟨y,z,hyz3,hyz4,hyz1,hyz2⟩
  have hyzcases1 := triv_lem_sets_0 x x1 y z hyz1 hyz2
  have hyz3 : ({x,x2} : Set ℕ) = ({y,z} : Set ℕ) := by
    rw[hxx1xx2] at hyz2
    exact hyz2
  have hyzcases2 := triv_lem_sets_0 x x2 y z hyz1 hyz3
  rcases hyzcases1 with (hyx | hyx1)
  rcases hyzcases2 with (h1 | h2)
  rw[← hyx.2]; tauto
  rw[hyx.1] at hyz1; rw[h2.2] at hyz1; tauto
  rcases hyzcases2 with (h1 | h2)
  rw[h1.1] at hyz1; rw[hyx1.2] at hyz1; tauto
  rw[← hyx1.1]; tauto

lemma triv_lem_sets_2 (G : Set ℕ × Set (Set ℕ)) (hGgraph: is_graph G) (x y x1 y1 : ℕ) (hxyinG : {x,y} ∈ G.2)
(hxyx1y1 : ({x,y} : Set ℕ) = ({x1,y1} : Set ℕ)) : x1 = x ∨ y1 = x := by
  have hxinxy : x ∈ ({x,y} : Set ℕ) := by tauto
  have hxinx1y1 : x ∈ ({x1,y1} : Set ℕ) := by
    rw[← hxyx1y1]; exact hxinxy
  simp at hxinx1y1; tauto

lemma triv_lem_1 (x y: ℕ): x ∈ ({x,y} : Set ℕ) ∧ y ∈ ({x,y} : Set ℕ) := by
  tauto

lemma triv_lem_2 (x y z : ℕ): x ∈ ({x,y,z} : Set ℕ) ∧ y ∈ ({x,y,z} : Set ℕ) ∧ z ∈ ({x,y,z} : Set ℕ) := by
  tauto

lemma triv_lem_sets_3_0 (a b c x y z : ℕ) (habcxyz: ({a,b,c} : Set ℕ) = ({x,y,z} : Set ℕ)) (hxney : x ≠ y)
(hxnez : x ≠ z) (hynez : y ≠ z) (hax : a = x):
({a,b} : Set ℕ) = ({x,y} : Set ℕ) ∨ ({a,b} : Set ℕ) = ({x,z} : Set ℕ) ∨ ({a,b} : Set ℕ) = ({y,z} : Set ℕ) := by
  have hainabc : a ∈ ({a,b,c} : Set ℕ) := (triv_lem_2 a b c).1
  have hainxyz : a ∈ ({x,y,z} : Set ℕ) := by
    rw[habcxyz] at hainabc; exact hainabc
  clear hainabc
  simp only [mem_insert_iff, mem_singleton_iff] at hainxyz
  have hbinabc : b ∈ ({a,b,c} : Set ℕ) := (triv_lem_2 a b c).2.1
  have hbinxyz : b ∈ ({x,y,z} : Set ℕ) := by
    rw[habcxyz] at hbinabc; exact hbinabc
  clear hbinabc
  simp only [mem_insert_iff, mem_singleton_iff] at hbinxyz
  have hcinabc : c ∈ ({a,b,c} : Set ℕ) := (triv_lem_2 a b c).2.2
  have hcinxyz : c ∈ ({x,y,z} : Set ℕ) := by
    rw[habcxyz] at hcinabc; exact hcinabc
  clear hcinabc
  simp only [mem_insert_iff, mem_singleton_iff] at hcinxyz
  have hxinxyz : x ∈ ({x,y,z} : Set ℕ) := (triv_lem_2 x y z).1
  have hxinabc : x ∈ ({a,b,c} : Set ℕ) := by
    rw[← habcxyz] at hxinxyz; exact hxinxyz
  clear hxinxyz
  simp only [mem_insert_iff, mem_singleton_iff] at hxinabc
  have hyinxyz : y ∈ ({x,y,z} : Set ℕ) := (triv_lem_2 x y z).2.1
  have hyinabc : y ∈ ({a,b,c} : Set ℕ) := by
    rw[← habcxyz] at hyinxyz; exact hyinxyz
  clear hyinxyz
  simp only [mem_insert_iff, mem_singleton_iff] at hyinabc
  have hzinxyz : z ∈ ({x,y,z} : Set ℕ) := (triv_lem_2 x y z).2.2
  have hzinabc : z ∈ ({a,b,c} : Set ℕ) := by
    rw[← habcxyz] at hzinxyz; exact hzinxyz
  clear hzinxyz
  simp only [mem_insert_iff, mem_singleton_iff] at hzinabc
  rcases hbinxyz with (hbx | hbyz)
  rcases hyinabc with (hya | hybc)
  left; rw[hbx]; rw[hya]; exact Set.pair_comm a x
  rcases hybc with (hyb | hyc)
  left; rw[hyb]; rw[hax]
  rcases hzinabc with (hza | hzbc)
  right; left; rw[hza]; rw[hbx]; exact Set.pair_comm a x
  rcases hzbc with (hzb | hzc)
  right; left; rw[hzb]; rw[hax]
  rw[hyc] at hynez; rw[hzc] at hynez; exact False.elim (hynez rfl)
  rcases hbyz with (hby | hbz)
  left; rw[hax]; rw[hby]
  right; left; rw[hax]; rw[hbz]

lemma triv_lem_sets_3_1 (a b c x y z : ℕ) (habcxyz: ({a,b,c} : Set ℕ) = ({x,y,z} : Set ℕ)) (hxney : x ≠ y)
(hxnez : x ≠ z) (hynez : y ≠ z):
({a,b} : Set ℕ) = ({x,y} : Set ℕ) ∨ ({a,b} : Set ℕ) = ({x,z} : Set ℕ) ∨ ({a,b} : Set ℕ) = ({y,z} : Set ℕ) := by
  have hainabc : a ∈ ({a,b,c} : Set ℕ) := (triv_lem_2 a b c).1
  have hainxyz : a ∈ ({x,y,z} : Set ℕ) := by
    rw[habcxyz] at hainabc; exact hainabc
  clear hainabc
  simp only [mem_insert_iff, mem_singleton_iff] at hainxyz
  have hbinabc : b ∈ ({a,b,c} : Set ℕ) := (triv_lem_2 a b c).2.1
  have hbinxyz : b ∈ ({x,y,z} : Set ℕ) := by
    rw[habcxyz] at hbinabc; exact hbinabc
  clear hbinabc
  simp only [mem_insert_iff, mem_singleton_iff] at hbinxyz
  have hcinabc : c ∈ ({a,b,c} : Set ℕ) := (triv_lem_2 a b c).2.2
  have hcinxyz : c ∈ ({x,y,z} : Set ℕ) := by
    rw[habcxyz] at hcinabc; exact hcinabc
  clear hcinabc
  simp only [mem_insert_iff, mem_singleton_iff] at hcinxyz
  have hxinxyz : x ∈ ({x,y,z} : Set ℕ) := (triv_lem_2 x y z).1
  have hxinabc : x ∈ ({a,b,c} : Set ℕ) := by
    rw[← habcxyz] at hxinxyz; exact hxinxyz
  clear hxinxyz
  simp only [mem_insert_iff, mem_singleton_iff] at hxinabc
  have hyinxyz : y ∈ ({x,y,z} : Set ℕ) := (triv_lem_2 x y z).2.1
  have hyinabc : y ∈ ({a,b,c} : Set ℕ) := by
    rw[← habcxyz] at hyinxyz; exact hyinxyz
  clear hyinxyz
  simp only [mem_insert_iff, mem_singleton_iff] at hyinabc
  have hzinxyz : z ∈ ({x,y,z} : Set ℕ) := (triv_lem_2 x y z).2.2
  have hzinabc : z ∈ ({a,b,c} : Set ℕ) := by
    rw[← habcxyz] at hzinxyz; exact hzinxyz
  clear hzinxyz
  simp only [mem_insert_iff, mem_singleton_iff] at hzinabc
  rcases hainxyz with (hax | hayz)
  exact triv_lem_sets_3_0 a b c x y z habcxyz hxney hxnez hynez hax
  rcases hayz with (hay | haz)
  have habcyxz : ({a,b,c} : Set ℕ) = ({y,x,z} : Set ℕ) := by
    rw[habcxyz]
    exact insert_comm x y {z}
  have hynex : y ≠ x := by exact id (Ne.symm hxney)
  have hnear := triv_lem_sets_3_0 a b c y x z habcyxz hynex hynez hxnez hay
  rcases hnear with (h1 | h2 | h3)
  left; rw[Set.pair_comm y x] at h1; exact h1
  right; right; exact h2
  right; left; exact h3
  have habcyxz : ({a,b,c} : Set ℕ) = ({z,x,y} : Set ℕ) := by
    rw[habcxyz]
    ext t; apply Iff.intro; intro h; rcases h with (hx | hyz | hz)
    right; left; exact hx; right; right; exact hyz; left; exact hz
    intro h; rcases h with (hz | hx | hy); right; right; exact hz
    left; exact hx; right; left; exact hy
  have hznex : z ≠ x := by exact id (Ne.symm hxnez)
  have hzney : z ≠ y := by exact id (Ne.symm hynez)
  have hnear := triv_lem_sets_3_0 a b c z x y habcyxz hznex hzney hxney haz
  rcases hnear with (h1 | h2 | h3)
  right; left; rw[Set.pair_comm z x] at h1; exact h1
  right; right; rw[Set.pair_comm z y] at h2; exact h2
  left; exact h3

lemma triv_lem_sets_4_0 (a b c x y z : ℕ) (h: ( (({a,b} : Set ℕ),{a,c},{b,c}) : Set ℕ × Set ℕ × Set ℕ ) = (({x,y} : Set ℕ),{x,z},{y,z})) :
  ({a,b,c} : Set ℕ) ⊆ ({x,y,z} : Set ℕ) := by
  have habxy : ({a,b} : Set ℕ) = ({x,y} : Set ℕ) := by injections
  have hacxz : ({a,c} : Set ℕ) = ({x,z} : Set ℕ) := by injections
  have hacyz : ({b,c} : Set ℕ) = ({y,z} : Set ℕ) := by injections
  have hainab: a ∈ ({a,b} : Set ℕ) := (triv_lem_1 a b).1
  have hbinab: b ∈ ({a,b} : Set ℕ) := (triv_lem_1 a b).2
  have hcinac: c ∈ ({a,c} : Set ℕ) := (triv_lem_1 a c).2
  intro t h; rcases h with (ta | tb | tc)
  have htxy : t ∈ ({x,y} : Set ℕ) := by
    rw[ta]; rw[habxy] at hainab; exact hainab
  rcases htxy with (htx | hty)
  left; exact htx; right; left; exact hty
  have htxy : t ∈ ({x,y} : Set ℕ) := by
    rw[tb]; rw[habxy] at hbinab; exact hbinab
  rcases htxy with (htx | hty)
  left; exact htx; right; left; exact hty
  simp only [mem_singleton_iff] at tc
  have htxz : t ∈ ({x,z} : Set ℕ) := by
    rw[tc]; rw[hacxz] at hcinac; exact hcinac
  rcases htxz with (htx | htz)
  left; exact htx; right; right; exact htz

lemma triv_lem_sets_4 (a b c x y z : ℕ) (h: ( (({a,b} : Set ℕ),{a,c},{b,c}) : Set ℕ × Set ℕ × Set ℕ ) = (({x,y} : Set ℕ),{x,z},{y,z})) :
  ({a,b,c} : Set ℕ) = ({x,y,z} : Set ℕ) := by
  apply Set.Subset.antisymm
  exact triv_lem_sets_4_0 _ _ _ _ _ _ h
  have hflipped := Eq.symm h
  exact triv_lem_sets_4_0 _ _ _ _ _ _ hflipped

lemma triv_lem_sets_5 (G : Set ℕ × Set (Set ℕ)) (v : ℕ):
{y | {v,y} ∈ G.2} = {u | {u,v} ∈ G.2} := by
  apply Set.Subset.antisymm; intro t ht; simp at ht; simp; rw[Set.pair_comm] at ht; exact ht
  intro t ht; simp at ht; simp; rw[Set.pair_comm] at ht; exact ht

lemma triv_lem_about_disj (F G : Set (Set ℕ)): F ∩ G = ∅ → G ∩ F = ∅ := by
  intro h
  contrapose! h
  rcases h with ⟨x,hx⟩
  use x; apply And.intro; exact hx.2; exact hx.1

lemma lem_about_disj (F G : Set (Set ℕ)): (∀ T ∈ F, T ∉ G) → F ∩ G = ∅ := by
  intro h
  by_contra h1
  push_neg at h1
  rcases h1 with ⟨x,hx⟩
  have h1 := h x hx.1
  exact h1 hx.2

lemma sUdiff.{u1} {X : Type u1} (F : Set (Set X)) (C : Set X) (hCinF : C ∈ F): ⋃₀ F = ⋃₀ (F\{C}) ∪ C := by
  ext x; apply Iff.intro; swap

  intro hx; rcases hx with (hxF | hxC)
  simp at hxF; rcases hxF with ⟨t,ht⟩; use t; tauto
  use C

  intro hx; rcases hx with ⟨t,ht⟩
  by_cases htC : t = C
  right; rw[← htC]; exact ht.right
  left; use t; apply And.intro; swap; use ht.right
  tauto

lemma ncard_of_disjoint_sUnion_induction_form.{u1} {X : Type u1} (n : ℕ):
∀ (F : Set (Set X)), (h: F.Finite ∧ F.ncard = n ∧ (∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) ∧ (∀ A ∈ F, A.Finite)) →
(⋃₀ F).ncard = ∑ A ∈ (Finite.toFinset h.1), A.ncard := by

  induction' n with n hn

  --base case: n = 0
  intro F ⟨hF1,hF2,hF3⟩
  have hFempty: F = ∅ := by
    exact (ncard_eq_zero hF1).mp hF2
  subst hFempty
  simp only [sUnion_empty, ncard_empty, toFinite_toFinset, toFinset_empty, sum_empty]

  --induction step
  intro F ⟨hFfin,hFncard,hFdisj,hFfins⟩

  have hFnonempty : ∃ C : Set X, C ∈ F := by
    have hFnonemp : F.Nonempty := by
      apply Set.nonempty_of_ncard_ne_zero; rw[hFncard]; exact Ne.symm (Nat.zero_ne_add_one n)
    exact hFnonemp
  rcases hFnonempty with ⟨C,hCinF⟩
  let G : Set (Set X) := F\{C}
  have hGsubF : G ⊆ F := by
    exact diff_subset
  have hGfin: G.Finite := by
    exact Finite.diff hFfin {C}
  have hGncard : G.ncard = n := by
    dsimp[G]
    have hAsubF : {C} ⊆ F := by
      exact Set.singleton_subset_iff.mpr hCinF
    have hnear := Set.ncard_diff hAsubF hFfin
    rw[hnear]; rw[hFncard]
    simp only [ncard_singleton, add_tsub_cancel_right]
  have hGdisj : ∀ A ∈ G, ∀ B ∈ G, A ≠ B → Disjoint A B := by
    intro A hAinG B hBinG hAneB
    have hAinF := hGsubF hAinG
    have hBinF := hGsubF hBinG
    exact hFdisj A hAinF B hBinF hAneB
  have hGfins: ∀ A ∈ G, A.Finite := by
    intro A hA; exact hFfins A (hGsubF hA)
  have hnear := hn G ⟨hGfin,hGncard,hGdisj,hGfins⟩

  have hsUF_decomp : ⋃₀F = ⋃₀G ∪ C := by
    dsimp[G]
    exact sUdiff F C hCinF
  rw[hsUF_decomp]
  have hC_disj_sUG : Disjoint (⋃₀ G) C := by
    simp only [disjoint_sUnion_left]; intro A hAinG
    have hAinF := hGsubF hAinG
    apply hFdisj A hAinF C hCinF ?_
    contrapose! hAinG; rw[hAinG]; dsimp[G]; exact not_mem_diff_of_mem rfl
  have hsUG_fin : (⋃₀ G).Finite := by
    exact Finite.sUnion hGfin hGfins
  have hnear2 := Set.ncard_union_eq hC_disj_sUG (hsUG_fin) (hFfins C hCinF)
  rw[hnear2]; rw[hnear]

  set F1 := Finite.toFinset hFfin
  set G1 := Finite.toFinset hGfin
  suffices: G1 = F1\{C}
  . rw[this]
    symm
    refine Finset.sum_eq_sum_diff_singleton_add ?_ _
    dsimp[F1]; simp only [Finite.mem_toFinset]; exact hCinF
  dsimp[G1,F1]; ext A; apply Iff.intro; intro hA; rw[Finite.mem_toFinset] at hA
  rw[mem_sdiff]; apply And.intro; rw[Finite.mem_toFinset]; exact hGsubF hA; dsimp[G] at hA
  rw [Finset.mem_singleton]; contrapose! hA; exact not_mem_diff_of_mem hA
  intro hA; simp only [mem_sdiff, Finite.mem_toFinset, Finset.mem_singleton] at hA
  rw [Finite.mem_toFinset]; dsimp[G]; exact hA

theorem ncard_of_disjoint_sUnion.{u1} {X : Type u1} (F : Set (Set X)) (hFfin: F.Finite)
(hdisj: ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) (hFfins: ∀ A ∈ F, A.Finite):
(⋃₀ F).ncard = ∑ A ∈ (Finite.toFinset hFfin), A.ncard := by
  exact ncard_of_disjoint_sUnion_induction_form  F.ncard F ⟨hFfin, rfl, hdisj, hFfins⟩

def proj1.{u1} {X : Type u1} (A : Set (X × X × X × X)): Set X := {w : X | ∃(x y z : X), (w,x,y,z) ∈ A}

def marginal1.{u1} {X : Type u1} (A : Set (X × X × X × X)) (w : X): Set (X × X × X × X) :=
{a : X × X × X × X | a ∈ A ∧ ∃(x y z : X), a = (w,x,y,z)}

lemma Afin_imp_proj1Afin.{u1} {X : Type u1} {x0 : X}
(A : Set (X × X × X × X)) (hAfin: A.Finite): (proj1 A).Finite := by

  --set A1 := proj1 A with hA1def

  let f : X → X × X × X × X := fun x ↦
    if h: x ∈ proj1 A then (x,h.choose,(h.choose_spec).choose, ((h.choose_spec).choose_spec).choose)
    else (x0,x0,x0,x0)

  refine @Set.Finite.of_finite_image _ _ _ f ?_ ?_

  --show image f(proj1 A) is finite
  have hsubA : f '' proj1 A ⊆ A := by
    intro ⟨w,x,y,z⟩ hwxyz
    rw [Set.mem_image] at hwxyz; rcases hwxyz with ⟨w1,hw11,hw12⟩

    have h := ((hw11.choose_spec).choose_spec).choose_spec
    set x1 := hw11.choose; set y1 := (hw11.choose_spec).choose
    set z1 := ((hw11.choose_spec).choose_spec).choose
    have hf : f w1 = (w1,x1,y1,z1) := by exact dif_pos hw11
    rw[hw12] at hf; rw[hf]; exact h
  exact Finite.subset hAfin hsubA

  --show injective
  intro w1 hw1 w2 hw2 hf12
  have h1 := ((hw1.choose_spec).choose_spec).choose_spec
  set x1 := hw1.choose; set y1 := (hw1.choose_spec).choose
  set z1 := ((hw1.choose_spec).choose_spec).choose
  have h2 := ((hw2.choose_spec).choose_spec).choose_spec
  set x2 := hw2.choose; set y2 := (hw2.choose_spec).choose
  set z2 := ((hw2.choose_spec).choose_spec).choose
  have hfw1: f w1 = (w1,x1,y1,z1) := by exact dif_pos hw1
  have hfw2: f w2 = (w2,x2,y2,z2) := by exact dif_pos hw2
  rw[hfw1,hfw2] at hf12; injection hf12

lemma Afin_imp_marg1Afin.{u1} {X : Type u1} {x0 : X}
(A : Set (X × X × X × X)) (hAfin: A.Finite) (w : X): (marginal1 A w).Finite := by
  suffices: marginal1 A w ⊆ A
  . exact Finite.subset hAfin this
  intro a ha; dsimp[marginal1] at ha; exact ha.1

lemma union_of_marginal1s.{u1} {X : Type u1} (A : Set (X × X × X × X)):
A = ⋃₀{B | ∃ w ∈ proj1 A, B = marginal1 A w} := by
  apply Set.Subset.antisymm

  intro ⟨w,x,y,z⟩ ha
  simp only [mem_sUnion, mem_setOf_eq, exists_exists_and_eq_and]
  use marginal1 A w; apply And.intro
  swap; dsimp[marginal1]; apply And.intro; exact ha; use x; use y; use z
  use w; apply And.intro; swap; rfl; dsimp[proj1]; use x; use y; use z

  intro ⟨w,x,y,z⟩ ha; simp only [mem_sUnion, mem_setOf_eq, exists_exists_and_eq_and] at ha
  rcases ha with ⟨B,hB1,hB2⟩; rcases hB1 with ⟨w1,hw11,hw12⟩
  suffices: B ⊆ A
  . exact this hB2
  rw[hw12]; intro a ha; dsimp[marginal1] at ha; exact ha.1

lemma change_summation_index.{u1} {X : Type u1} {x0 : X} (A : Set (X × X × X × X)) (hAfin: A.Finite)
(F : Set (Set (X × X × X × X))) (hFeq : F = {B | ∃ w ∈ proj1 A, B = marginal1 A w}) (hFfin: F.Finite):
∑ B ∈ (Finite.toFinset hFfin), B.ncard =
∑ w ∈ Finite.toFinset (@Afin_imp_proj1Afin X x0 A hAfin) , (marginal1 A w).ncard := by

  have hproj1Afin := @Afin_imp_proj1Afin X x0 A hAfin

  set F1 := Finite.toFinset hFfin with hF1def
  set X1 := Finite.toFinset hproj1Afin with hG1def

  set f : Set (X × X × X × X) → ℕ := fun B ↦ B.ncard
  set g : X → ℕ := fun w ↦ (marginal1 A w).ncard

  let i2 (B : Set (X × X × X × X)) (hBinF1: B ∈ F1): X := by
    dsimp[F1] at hBinF1; simp only [Finite.mem_toFinset] at hBinF1
    rw[hFeq] at hBinF1; simp only [mem_setOf_eq] at hBinF1
    exact hBinF1.choose

  set i : (B : Set (X × X × X × X)) → B ∈ F1 → f B ≠ 0 → X := fun B ↦ fun hBinF1 ↦ fun hfBne0 ↦ i2 B hBinF1

  apply Finset.sum_bij_ne_zero i ?_ ?_ ?_ ?_

  --show i a ha in G1 for any a in F1
  intro A hAinF1 hAnezero
  dsimp[i]; dsimp[i2]
  dsimp[F1] at hAinF1; simp only [Finite.mem_toFinset] at hAinF1
  rw[hFeq] at hAinF1; simp only [mem_setOf_eq] at hAinF1
  have hxprop := hAinF1.choose_spec
  set x := hAinF1.choose
  dsimp[X1]; refine (Finite.mem_toFinset hproj1Afin).mpr ?_; exact hxprop.1

  --show i is injective
  intro A1 hA1inF1 hfA1nezero A2 hA2inF1 hfA2nezero hf12

  dsimp[i] at hf12; dsimp[i2] at hf12
  dsimp[F1] at hA1inF1; simp only [Finite.mem_toFinset] at hA1inF1
  rw[hFeq] at hA1inF1; simp only [mem_setOf_eq] at hA1inF1
  dsimp[F1] at hA2inF1; simp only [Finite.mem_toFinset] at hA2inF1
  rw[hFeq] at hA2inF1; simp only [mem_setOf_eq] at hA2inF1
  have hx1prop := hA1inF1.choose_spec
  set x1 := hA1inF1.choose
  have hx2prop := hA2inF1.choose_spec
  set x2 := hA2inF1.choose
  rw[hx1prop.2, hx2prop.2]; rw[hf12]

  --show i is surjective
  intro x hxinG1 hnezero
  set B := marginal1 A x with hAdef
  have hBinF1 : marginal1 A x ∈ F1 := by
    dsimp[F1]; simp only [Finite.mem_toFinset]; rw[hFeq]
    simp only [mem_setOf_eq]; use x; apply And.intro; swap; rfl
    dsimp[X1] at hxinG1; simp only [Finite.mem_toFinset] at hxinG1
    exact hxinG1
  use B; use hBinF1; use hnezero
  dsimp[i]; dsimp[i2]
  dsimp[F1] at hBinF1; simp only [Finite.mem_toFinset] at hBinF1
  rw[hFeq] at hBinF1; simp only [mem_setOf_eq] at hBinF1
  have hxprop := hBinF1.choose_spec
  set x1 := hBinF1.choose
  have hnear := hxprop.2
  rw[hAdef] at hnezero
  have hnonemp : ∃ a : X × X × X × X, a ∈ marginal1 A x := by
    exact Set.nonempty_of_ncard_ne_zero hnezero
  rcases hnonemp with ⟨⟨x2,u,v,w⟩,hinx⟩
  have hinx1 : (x2,u,v,w) ∈ marginal1 A x1 := by
    rw[hnear] at hinx; exact hinx
  have hxx2 : x = x2 := by
    dsimp[marginal1] at hinx; have hinx1 := hinx.1; have hinx2 := hinx.2; clear hinx
    rcases hinx2 with ⟨u1,v1,w1,h12⟩
    symm; injection h12
  have hx1x2 : x1 = x2 := by
    dsimp[marginal1] at hinx1; have hinx11 := hinx1.1; have hinx12 := hinx1.2; clear hinx
    rcases hinx12 with ⟨u1,v1,w1,h12⟩
    injection h12 with h; symm; exact h
  rw[hxx2,hx1x2]

  --show f = g ∘ i
  intro A hAinF1 hfnezero
  dsimp[i]; dsimp[i2]
  dsimp[F1] at hAinF1; simp only [Finite.mem_toFinset] at hAinF1
  rw[hFeq] at hAinF1; simp only [mem_setOf_eq] at hAinF1
  have hxprop := hAinF1.choose_spec
  set x := hAinF1.choose
  rw[hxprop.2]

lemma ncard_projections.{u1} {X : Type u1} {x0 : X} (A : Set (X × X × X × X)) (hAfin: A.Finite):
A.ncard = ∑ w ∈ Finite.toFinset (@Afin_imp_proj1Afin X x0 A hAfin), (marginal1 A w).ncard := by
  have hdecomp := union_of_marginal1s A
  nth_rewrite 1 [hdecomp]

  have hproj1Afin := @Afin_imp_proj1Afin X x0 A hAfin

  set F := {B | ∃ w ∈ proj1 A, B = marginal1 A w} with hFdef
  have hFfin: F.Finite := by
    apply Finite.of_surjOn (fun w ↦ marginal1 A w) ?_ hproj1Afin
    dsimp[SurjOn]; intro B hB; simp only [Set.mem_image]
    dsimp[F] at hB; rcases hB with ⟨w,hw1,hw2⟩; use w; exact ⟨hw1,Eq.symm hw2⟩
  have hnear2 := ncard_of_disjoint_sUnion F hFfin ?_ ?_
  rw[hnear2]

  set F1 := Finite.toFinset hFfin with hF1def
  set X1 := Finite.toFinset hproj1Afin with hX1def
  exact @change_summation_index X x0 A hAfin F hFdef hFfin

  --show ∀A ∈ F, ∀B ∈ F, A ≠ B → Disjoint A B
  intro B hB C hC hBneC; dsimp[F] at hB; dsimp[F] at hC
  rcases hB with ⟨xB,hxB1,hxB2⟩; rcases hC with ⟨xC,hxC1,hxC2⟩
  rw[hxB2, hxC2]
  have hnear: ∀ a ∈ marginal1 A xB, a ∉ marginal1 A xC := by
    intro ⟨x1,u1,v1,w1⟩ h1
    dsimp[marginal1] at h1
    rcases h1 with ⟨u,v,w,h1,h2⟩
    have hx1xB : x1 = xB := by injections
    contrapose! hx1xB
    dsimp[marginal1] at hx1xB; rcases hx1xB with ⟨u3,v3,w3,h31,h32⟩
    have hx1xC : x1 = xC := by
      injection h32
    rw[hx1xC]; contrapose! hBneC
    rw[hxB2, hxC2]; rw[hBneC]
  exact Set.disjoint_left.mpr hnear

  --show: ∀ A ∈ F, A.Finite
  intro B hB; dsimp[F] at hB; rcases hB with ⟨w,hw1,hw2⟩; rw[hw2]
  exact @Afin_imp_marg1Afin X x0 A hAfin w

lemma ncard_projections_2.{u1} {X : Type u1} {x0 : X} (A : Set (X × X × X × X)) (hAfin: A.Finite)
(Y : Set X) (hYfin: Y.Finite) (hYsubproj1A : proj1 A ⊆ Y):
A.ncard = ∑ w ∈ Finite.toFinset hYfin, (marginal1 A w).ncard := by
  have hnear := @ncard_projections X x0 A hAfin
  rw[hnear]
  set X1 := Finite.toFinset (@Afin_imp_proj1Afin X x0 A hAfin) with hX1def
  set Y1 := Finite.toFinset hYfin with hY1def
  have hYsubproj1A_finsets : X1 ⊆ Y1 := by
    exact Finite.toFinset_subset_toFinset.mpr hYsubproj1A
  refine Finset.sum_subset_zero_on_sdiff hYsubproj1A_finsets ?_ ?_

  swap; intro x hx; rfl

  intro x hx; simp only [mem_sdiff] at hx; have hx1 := hx.1; have hx2 := hx.2; clear hx
  contrapose! hx2; apply Set.nonempty_of_ncard_ne_zero at hx2; rcases hx2 with ⟨a,ha⟩
  dsimp[marginal1] at ha; have ha1 := ha.1; have ha2 := ha.2; clear ha
  rcases ha2 with ⟨x1,y,z,hx1yz⟩; dsimp[X1]; simp only [Finite.mem_toFinset]; dsimp[proj1]
  use x1; use y; use z; rw[← hx1yz]; exact ha1

lemma ncard_projections_trivial.{u1} {X : Type u1} {x0 : X} (A : Set (X × X × X × X)) (hAfin: A.Finite)
(w : X): (marginal1 A w).ncard = ({(x,y,z) : X × X × X | (w,x,y,z) ∈ A}).ncard := by

  let f : X × X × X × X → X × X × X := fun a ↦
    if h: a ∈ A ∧ ∃(x y z : X), a = (w,x,y,z) then
      (h.2.choose, (h.2.choose_spec).choose, ((h.2.choose_spec).choose_spec).choose)
    else
      (x0,x0,x0)

  have hinj: InjOn f (marginal1 A w) := by
    intro a1 ha1 a2 ha2 hf12
    dsimp[marginal1] at ha1; dsimp[marginal1] at ha2
    have hprop1 := ha1.2.choose_spec.choose_spec.choose_spec
    set x1 := ha1.2.choose; set y1 := ha1.2.choose_spec.choose; set z1 := ha1.2.choose_spec.choose_spec.choose
    have hprop2 := ha2.2.choose_spec.choose_spec.choose_spec
    set x2 := ha2.2.choose; set y2 := ha2.2.choose_spec.choose; set z2 := ha2.2.choose_spec.choose_spec.choose
    rw[hprop1,hprop2];
    have hf1eq : f a1 = (x1,y1,z1) := dif_pos ha1
    have hf2eq : f a2 = (x2,y2,z2) := dif_pos ha2
    rw[hf1eq,hf2eq] at hf12; exact congrArg (Prod.mk w) hf12
  have hnear := Set.ncard_image_of_injOn hinj

  --show image is RHS
  rw[← hnear]; congr; ext ⟨x,y,z⟩; apply Iff.intro

  intro hxyz; simp only [Prod.mk.eta,mem_setOf_eq]
  simp only [Set.mem_image, Prod.exists] at hxyz; rcases hxyz with ⟨w1,x1,y1,z1,h11,h12⟩
  dsimp[marginal1] at h11
  have hprop := h11.2.choose_spec.choose_spec.choose_spec
  set x2 := h11.2.choose; set y2 := h11.2.choose_spec.choose; set z2 := h11.2.choose_spec.choose_spec.choose
  have hfeq : f (w1,x1,y1,z1) = (x2,y2,z2) := by
    exact dif_pos h11
  rw[h12] at hfeq
  have hnear2 : (w,x,y,z) = (w1,x1,y1,z1) := by
    refine Prod.mk.inj_iff.mpr ?_; apply And.intro
    injection hprop with h101 h102; symm; exact h101
    rw[hfeq]; symm; injection hprop
  rw[hnear2]; exact h11.1

  intro hxyz; simp only [Prod.mk.eta, mem_setOf_eq] at hxyz; simp only [Set.mem_image, Prod.exists]
  use w; use x; use y; use z; apply And.intro; dsimp[marginal1]; use hxyz; use x; use y; use z
  have hexists : ∃ x_1 y_1 z_1, (w, x, y, z) = (w, x_1, y_1, z_1) := by
    use x; use y; use z
  have hprop := hexists.choose_spec.choose_spec.choose_spec
  set x1 := hexists.choose; set y1 := hexists.choose_spec.choose; set z1 := hexists.choose_spec.choose_spec.choose
  have hfeq : f (w,x,y,z) = (x1,y1,z1) := by
    exact dif_pos ⟨hxyz,hexists⟩
  rw[hfeq]; symm; injection hprop

lemma ncard_m_to_1_induction_form.{u1,u2} {X : Type u1} {Y : Type u2} (m n : ℕ):
∀(A : Set X), ∀(B : Set Y), (B.ncard = n ∧ A.Finite ∧ B.Finite) →
∀ f : X → Y, (∀a ∈ A, f a ∈ B) ∧ (∀b ∈ B, ({a ∈ A | f a = b}).ncard = m) →
A.ncard = m*B.ncard := by
  induction' n with n hind

  --base case: B.ncard = 0
  intro A B ⟨hBncard,hAfin,hBfin⟩ f ⟨hfAtoB, hfmto1⟩
  rw[hBncard, mul_zero]
  suffices: A = ∅
  . rw[this]; exact ncard_empty X
  apply (Set.ncard_eq_zero hBfin).mp at hBncard
  contrapose! hBncard; rcases hBncard with ⟨a,ha⟩; use f a; exact hfAtoB a ha

  --induction step
  intro A B ⟨hBncard,hAfin,hBfin⟩ f ⟨hfAtoB, hfmto1⟩
  have hBnonemp: B.Nonempty := by
    have hBncardpos : B.ncard > 0 := by
      rw[hBncard]; exact Nat.zero_lt_succ n
    exact (ncard_pos hBfin).mp hBncardpos
  rcases hBnonemp with ⟨b0,hb0⟩
  let Bp := B\{b0}; let Ap := A\{a ∈ A | f a = b0}
  have hBpncard : Bp.ncard = n := by
    suffices: Bp.ncard+1 = n+1
    . exact Nat.add_left_inj.mp this
    rw[← hBncard]; dsimp[Bp]; exact ncard_diff_singleton_add_one hb0 hBfin
  have hApBpfins : Ap.Finite ∧ Bp.Finite := by
    apply And.intro
    exact Finite.subset hAfin diff_subset
    exact Finite.subset hBfin diff_subset
  have hfAptoBp: ∀ ap ∈ Ap, f ap ∈ Bp := by
    intro ap hap; have hapinB := hfAtoB ap (diff_subset hap)
    dsimp[Bp]; by_contra hcontra
    have hfap : f ap = b0 := by
      have hnear : f ap ∈ B \ (B\{b0}) := by
        exact mem_diff_of_mem hapinB hcontra
      simp only [sdiff_sdiff_right_self, Set.inf_eq_inter, mem_inter_iff, mem_singleton_iff] at hnear
      exact hnear.2
    dsimp[Ap] at hap; simp only [mem_diff, mem_setOf_eq, not_and] at hap
    have hnear2 : ¬ (f ap = b0) := by
      exact hap.2 hap.1
    exact hnear2 hfap
  have hfmto1p : ∀ bp ∈ Bp, {ap ∈ Ap | f ap = bp}.ncard = m := by
    intro bp hbp
    have hnear := hfmto1 bp (diff_subset hbp)
    suffices: {ap | ap ∈ Ap ∧ f ap = bp} = {a | a ∈ A ∧ f a = bp}
    . rw[this]; exact hnear
    ext a; apply Iff.intro; intro ha; rw[mem_setOf] at ha; rw[mem_setOf]; use diff_subset ha.1
    exact ha.2; intro ha; rw[mem_setOf] at ha; rw[mem_setOf]; apply And.intro; swap; exact ha.2
    dsimp[Ap]; simp only [mem_diff, mem_setOf_eq, not_and]; use ha.1; intro hainA;
    have ha2 := ha.2; clear ha; by_contra hcontra; rw[ha2] at hcontra; rw[hcontra] at hbp
    dsimp[Bp] at hbp; simp only [mem_diff, mem_singleton_iff, not_true_eq_false, and_false] at hbp
  have hindused := hind Ap Bp ⟨hBpncard, hApBpfins⟩ f ⟨hfAptoBp, hfmto1p⟩
  have hApncard : A.ncard = Ap.ncard+m := by
    have hnear1 : {a | a ∈ A ∧ f a = b0}.ncard = m := by
      exact hfmto1 b0 hb0
    rw[← hnear1]
    have hnear2 : A = Ap ∪ {a | a ∈ A ∧ f a = b0} := by
      apply Set.Subset.antisymm; swap; refine Set.union_subset ?_ ?h_
      dsimp[Ap]; exact diff_subset; exact sep_subset A fun x ↦ f x = b0
      intro a ha; by_cases hfa: f a = b0; right; rw[mem_setOf]; use ha
      left; dsimp[Ap]; simp only [mem_diff, mem_setOf_eq, not_and]; use ha
      intro hainA; exact hfa
    nth_rewrite 1 [hnear2]
    apply Set.ncard_union_eq ?_ ?_ ?_
    --show disjoint
    have hnear: ∀ ap ∈ Ap, ap ∉ {a | a ∈ A ∧ f a = b0} := by
      intro ap hap
      dsimp[Ap] at hap; simp only [mem_setOf_eq, not_and];
      intro hapinA; simp only [mem_diff, mem_setOf_eq, not_and] at hap
      exact hap.2 hap.1
    exact disjoint_sdiff_left
    --show Ap finite
    suffices: Ap ⊆ A
    . exact Finite.subset hAfin this
    rw[hnear2]; exact Set.subset_union_left
    --show {a in A : f a = b0} finite
    suffices: {a | a ∈ A ∧ f a = b0} ⊆ A
    . exact Finite.subset hAfin this
    intro a ha; rw[mem_setOf] at ha; exact ha.1
  rw[hApncard, hBncard, mul_add, mul_one]; congr
  rw[hindused, hBpncard]

lemma ncard_m_to_1.{u1,u2} {X : Type u1} {Y : Type u2} (A : Set X) (B : Set Y) (hAfin: A.Finite)
(hBfin: B.Finite) (m : ℕ) (f : X → Y) (hAtoB: ∀a ∈ A, f a ∈ B) (hfmto1: ∀b ∈ B, ({a ∈ A | f a = b}).ncard = m):
A.ncard = m*B.ncard := by
  exact ncard_m_to_1_induction_form m B.ncard A B ⟨rfl,hAfin,hBfin⟩ f ⟨hAtoB,hfmto1⟩


end triv_lem_sets
