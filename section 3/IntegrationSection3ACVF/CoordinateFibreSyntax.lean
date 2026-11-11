import IntegrationSection3.CoordinateFibres
import IntegrationSection3.FiniteTupleGraphs
import IntegrationSection3ACVF.FullBaseDefinability

/-! The full graph of every scalar coordinate-fibre map is one uniform
original-base definable relation,obtained by reindexing the actual tuple
map's entire partial graph. No labels are named in this relation. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.CoordinateFibreSyntax

variable {M ι κ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def Params (i : ι) (j : κ) := CoordinateSlices.Other i ⊕ CoordinateSlices.Other j

instance params_finite [Finite ι] [Finite κ] (i : ι) (j : κ) : Finite (Params i j) := by
  unfold Params CoordinateSlices.Other
  infer_instance

noncomputable def index (i : ι) (j : κ) : ι ⊕ κ → Params i j ⊕ Fin 2 := by
  classical
  exact Sum.elim (fun k => if h : k = i then .inr 0 else .inl (.inl ⟨k,h⟩))
    (fun k => if h : k = j then .inr 1 else .inl (.inr ⟨k,h⟩))

theorem graph_definable [Finite ι] [Finite κ] (B : FullBaseAtomicity.Base (M := M))
    (A : Set (ι → M)) (f : (ι → M) → (κ → M))
    (hf : FullBaseAtomicity.OverBase B (FiniteTupleGraphs.graph A f)) (i : ι) (j : κ) :
    FullBaseAtomicity.OverBase B {z : Params i j ⊕ Fin 2 → M |
      z (.inr 0) ∈ CoordinateFibres.source A f i j
        (fun k => z (.inl (.inl k))) (fun k => z (.inl (.inr k))) ∧
      z (.inr 1) = CoordinateFibres.map f i j (fun k => z (.inl (.inl k))) (z (.inr 0))} := by
  classical
  have h := FullBaseAtomicity.OverBase.preimage_comp hf (index i j)
  apply FullBaseAtomicity.OverBase.congr h
  intro z
  let u : CoordinateSlices.Other i → M := fun k => z (.inl (.inl k))
  let v : CoordinateSlices.Other j → M := fun k => z (.inl (.inr k))
  have hLeft : (z ∘ index i j) ∘ Sum.inl = CoordinateSlices.insert i u (z (.inr 0)) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [index,CoordinateSlices.insert]
    · simp [index,CoordinateSlices.insert,hk,u]
  have hRight : (z ∘ index i j) ∘ Sum.inr = CoordinateSlices.insert j v (z (.inr 1)) := by
    funext k
    by_cases hk : k = j
    · subst k
      simp [index,CoordinateSlices.insert]
    · simp [index,CoordinateSlices.insert,hk,v]
  change (((z ∘ index i j) ∘ Sum.inl) ∈ A ∧
    (z ∘ index i j) ∘ Sum.inr = f ((z ∘ index i j) ∘ Sum.inl)) ↔ _
  rw [hLeft,hRight]
  exact (CoordinateFibres.graph_iff A f i j u v (z (.inr 0)) (z (.inr 1))).symm

end IntegrationInACVF.Section3ACVF.CoordinateFibreSyntax
