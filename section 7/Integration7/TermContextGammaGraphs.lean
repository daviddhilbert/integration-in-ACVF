import Integration7.TermClosureDefinability
import Integration7.RealFiniteVolumePresentations
import Section3.VFDefinableClosure
import IntegrationSection6.AlgebraicFibres

/-! Real definitions over a named term context descend to its actual
generators. This applies to full graph relations and algebraicity. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (Point GammaGraphDefinable)
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem algebraicAt_termClosure_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (σ : SortTag) (x : M) :
    AlgebraicAt (Substructure.closure LRV S : Set M) σ x ↔ AlgebraicAt S σ x :=
  ⟨fun h => h.eliminate_definable_params hc (fun _ hx => definable_singleton_mem_termClosure hx),
    fun h => h.mono Substructure.subset_closure⟩

theorem gammaGraph_of_termContext
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (B : Base (M := M))
    (hBase : (C.base : Set M) = (Substructure.closure LRV B.real : Set M))
    {a b : ℕ} {R : (Fin a → CanonicalRV.RVSort M) → (Fin b → CanonicalRV.RVSort M) → Prop}
    (hR : (rawRVSpace (M := M) a).RelationDefinable (rawRVSpace (M := M) b) (C.base : Set M) R) :
    GammaGraphDefinable B (fun (x : Point (M := M) 0 a) (y : Point (M := M) 0 b) => R x.2 y.2) := by
  have hraw := rawRVRelationFormula_definable hR
  rw [hBase] at hraw
  have hΓ := canonicalRawGammaFormula hc B (fun _ : Fin (a+b) => .rv)
    (definable_termClosure_iff.mp hraw) (fun w hw i => rawRVRelationFormula_proper R w hw i)
  exact GammaGraphDefinable.congr (IntegrationInACVF.Section6.gamma_rv_graph_from_tuple_formula hΓ)
    (fun x y => rawRVRelationFormula_append R x.2 y.2)

theorem coordinate_algebraic_termContext
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (S : Set M)
    (hBase : (C.base : Set M) = (Substructure.closure LRV S : Set M))
    {n : ℕ} (i : Fin n) (t : Fin n → CanonicalRV.RVSort M)
    (h : AlgebraicAt (Section6.coordinateBase (C.base : Set M) i t) .rv (t i).val) :
    AlgebraicAt (Section6.coordinateBase S i t) .rv (t i).val := by
  apply (algebraicAt_termClosure_iff hc _ .rv _).mp
  apply h.mono
  rintro x (hx | hx)
  · rw [hBase] at hx
    exact (Substructure.closure_mono (show S ⊆ Section6.coordinateBase S i t from Set.subset_union_left)) hx
  · exact Substructure.subset_closure (Or.inr hx)

end IntegrationInACVF.Section7
