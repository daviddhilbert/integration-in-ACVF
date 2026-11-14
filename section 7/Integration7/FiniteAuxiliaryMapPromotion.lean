import Integration7.RealFiniteVolumePresentations
import Integration7.TermClosureDefinability
import IntegrationSection6.GammaFiniteObjectPromotion

/-! Promote an actual finite RV map from a term-generated context after
naming its finite auxiliary parameter tuple. Only raw definability is
descended through term closure; no field-generation property is used. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a j : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem finite_auxiliary_map_promotion {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (C : BaseContext M) (z : Fin p → M) (y : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hy : ∀ i, sortEval (sq i) (y i))
    (hBase : (C.base : Set M) = (Substructure.closure LRV (B.real ∪ Set.range (Fin.append z y)) : Set M))
    (D : DefSet (rawRVSpace (M := M) a) (C.base : Set M))
    (g : Map D (DefSet.univ (rawRVSpace (M := M) j) (C.base : Set M))) (hg : g.FiniteFibres) :
    ∃ E : GammaFiniteRVSchema B (p+q) a j (Fin.append sp sq), E.valid (Fin.append z y) ∧
      ∀ w, w ∈ D.carrier ↔ Fin.append (Fin.append z y) (rvValues w) ∈ E.domain := by
  let T := B.real ∪ Set.range (Fin.append z y)
  have hD : T.Definable LRV ((rawRVSpace (M := M) a).preimage D.carrier) := by
    apply definable_termClosure_iff.mp
    rw [← hBase]
    exact D.definable
  have hG : T.Definable LRV (rawRVRelationFormula g.graph) := by
    apply definable_termClosure_iff.mp
    rw [← hBase]
    exact rawRVRelationFormula_definable g.graph_definable
  obtain ⟨P⟩ := realFiniteMap_gammaPresentation (B := ⟨T,B.gamma⟩) hc D g hg hD hG
  have hzy (i) : sortEval (Fin.append sp sq i) (Fin.append z y i) := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.append_left] using hz i
    · simpa only [Fin.append_right] using hy i
  obtain ⟨E,hE,hED,_⟩ := gamma_sorted_finite_object_promotion hκ hs hreal hgamma
    (Fin.append sp sq) (Fin.append z y) hzy P.toGamma
  refine ⟨E,hE,?_⟩
  intro w
  rw [hED]
  constructor
  · intro hw
    refine ⟨⟨w,?_⟩,rfl⟩
    exact (Set.ext_iff.mp P.domain_eq w).mpr hw
  · rintro ⟨u,hu⟩
    have he : u.val = w := funext (fun i => Subtype.ext (congrFun hu i))
    exact he ▸ (Set.ext_iff.mp P.domain_eq u.val).mp u.property

end IntegrationInACVF.Section7
