import Mathlib

set_option linter.unusedVariables false

open Set
open scoped Classical
open Finset BigOperators

namespace graph_defs

def is_graph (G : (Set ℕ) × (Set (Set ℕ))) : Prop :=
∀e ∈ G.2, ∃(x y : ℕ), (x ∈ G.1 ∧ y ∈ G.1 ∧ x ≠ y ∧ e = ({x,y} : Set ℕ))

noncomputable def num_vertices (G : Set ℕ × Set (Set ℕ)) : ℕ :=
  (G.1).ncard

def max_deg_le (d : ℕ) (G : Set ℕ × Set (Set ℕ)) : Prop :=
  ∀(x : ℕ), ({y : ℕ | {x,y} ∈ G.2}).ncard ≤ d

def is_triangle (G : Set ℕ × Set (Set ℕ)) (T : Set ℕ) : Prop :=
  ∃ (x y z : ℕ), (x ≠ y ∧ x ≠ z ∧ y ≠ z) ∧ (T = {x,y,z}) ∧ ({x,y} ∈ G.2 ∧ {x,z} ∈ G.2 ∧ {y,z} ∈ G.2)

noncomputable def deg (G : Set ℕ × Set (Set ℕ)) : ℕ → ℕ := fun v ↦ {u : ℕ | {u,v} ∈ G.2}.ncard

def closed_nbhd (G : Set ℕ × Set (Set ℕ)): ℕ → Set ℕ := fun v ↦ {v}∪{u : ℕ | {u,v} ∈ G.2}

def Wgraph (G : Set ℕ × Set (Set ℕ)) : Set (ℕ × ℕ × ℕ × ℕ) :=
{(x,u,v,w) | {u,x} ∈ G.2 ∧ {v,x} ∈ G.2 ∧ {w,x} ∈ G.2 ∧ {u,v} ∉ G.2 ∧ {u,w} ∉ G.2 ∧ {v,w} ∉ G.2}

end graph_defs
