import Integration7.GammaRVScalarMapGraphs
import Integration7.NonzeroConeScaling
import Section4.RVProductAssociativity

/-! Packing the actual cone fibre map into RV labels retains its full
original-Gamma graph. Its source is the actual product domain, and its
cone parameter is multiplied by the checked unit correction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a b : ℕ}

def packedNonzeroConeFibreMap
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
    (F : Map A D) (c : Map A (DefSet.univ (rawRVSpace (M := M) 1) S))
    (hc : ∀ u, RVOperations.absoluteHom ((c u).val 0) = 1) :
    Map (rvProductDomain A (nonzeroBlowupConeSet S)) (rvProductDomain D (nonzeroBlowupConeSet S)) :=
  (rvPack D (nonzeroBlowupConeSet S)).toImage.comp
    ((nonzeroConeFibreMap F c hc).comp (rvUnpack A (nonzeroBlowupConeSet S)))

theorem gamma_packed_nonzero_cone_fibre_map
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
    (F : Map A D) (c : Map A (DefSet.univ (rawRVSpace (M := M) 1) S))
    (hcabs : ∀ u, RVOperations.absoluteHom ((c u).val 0) = 1)
    (hF : RVMapGamma F B) (hC : RVMapGamma c B)
    (hDom : GammaSetDefinable B {p : Point (M := M) 0 (a+1) |
      p.2 ∈ (rvProductDomain A (nonzeroBlowupConeSet S)).carrier}) :
    RVMapGamma (packedNonzeroConeFibreMap F c hcabs) B := by
  let Q := nonzeroBlowupConeSet S
  let X := rvProductDomain A Q
  let π : Map X A := (Map.prodFst A Q).comp (rvUnpack A Q)
  let σ : Map X (DefSet.univ (rawRVSpace (M := M) 1) S) :=
    ((Map.prodSnd A Q).toUniv).comp (rvUnpack A Q)
  have hπ : RVMapGamma π B := gamma_real_rv_map_graph hc B π
    (rvCoordinateSelectMap B.real (Fin.castAdd 1 : Fin a → Fin (a+1))) hDom (by
      intro p
      obtain ⟨u,v,rfl⟩ := exists_rvPackPair A Q p
      simp only [π,Map.comp_apply,rvUnpack_pair]
      exact (funext (Fin.append_left u.val v.val)).symm)
  have hσ : RVMapGamma σ B := gamma_real_rv_map_graph hc B σ
    (rvCoordinateSelectMap B.real (Fin.natAdd a : Fin 1 → Fin (a+1))) hDom (by
      intro p
      obtain ⟨u,v,rfl⟩ := exists_rvPackPair A Q p
      simp only [σ,Map.comp_apply,rvUnpack_pair]
      exact (funext (Fin.append_right u.val v.val)).symm)
  have hHead := (hπ.comp hF).congr (g := (F.comp π).toUniv) (fun _ => rfl)
  have hTail := (hπ.comp hC).scalarMul hc hσ
  apply (hHead.append hTail).congr
  intro p
  rfl

end IntegrationInACVF.Section7
