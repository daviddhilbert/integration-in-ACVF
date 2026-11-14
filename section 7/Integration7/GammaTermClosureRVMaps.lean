import Integration7.TermContextGammaGraphs
import Integration7.GammaRVScalarMapGraphs
import Integration7.VolumeDensityRescaling

/-! Term-definable RV constants and maps descend to the original base.
The containing real context may be larger than the term closure. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S T : Set M} {a b : ℕ}

theorem gamma_rv_map_graph_of_term_closure
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawRVSpace (M := M) a) (Substructure.closure LRV B.real : Set M)}
    {D : DefSet (rawRVSpace (M := M) b) (Substructure.closure LRV B.real : Set M)}
    (g : Map A D) : RVMapGamma g B := by
  have hraw := rawRVRelationFormula_definable g.graph_definable
  have hΓ := canonicalRawGammaFormula hc B (fun _ : Fin (a+b) => .rv)
    (definable_termClosure_iff.mp hraw)
    (fun w hw i => rawRVRelationFormula_proper _ w hw i)
  exact GammaGraphDefinable.congr (gamma_rv_graph_from_tuple_formula hΓ)
    (fun p q => rawRVRelationFormula_append _ p.2 q.2)

theorem gamma_rv_map_graph_from_global
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
    (f : Map A D)
    (g : Map (DefSet.univ (rawRVSpace (M := M) a) T)
      (DefSet.univ (rawRVSpace (M := M) b) T))
    (hg : RVMapGamma g B)
    (hA : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A.carrier})
    (hfg : ∀ u : A, (f u).val = (g ⟨u.val,Set.mem_univ _⟩).val) : RVMapGamma f B := by
  apply GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph hA hg)
  intro p q
  constructor
  · rintro ⟨hp,⟨u,hu,hq⟩⟩
    refine ⟨⟨p.2,hp⟩,rfl,?_⟩
    exact (hfg ⟨p.2,hp⟩).trans ((congrArg (fun v => (g v).val) (Subtype.ext hu)).symm.trans hq)
  · rintro ⟨u,hu,hq⟩
    have hp : p.2 ∈ A.carrier := hu ▸ u.property
    exact ⟨hp,⟨⟨u.val,Set.mem_univ _⟩,hu,(hfg u).symm.trans hq⟩⟩

theorem gamma_rv_scalar_constant
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) a) S)
    (hA : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A.carrier})
    (c : CanonicalRV.RVSort M) (hS : c.val ∈ S)
    (hB : c.val ∈ Substructure.closure LRV B.real) : RVMapGamma (rvScalarConstant A c hS) B := by
  let g := rvScalarConstant (DefSet.univ (rawRVSpace (M := M) a)
    (Substructure.closure LRV B.real : Set M)) c hB
  exact gamma_rv_map_graph_from_global _ g (gamma_rv_map_graph_of_term_closure hc g) hA (fun _ => rfl)

end IntegrationInACVF.Section7
