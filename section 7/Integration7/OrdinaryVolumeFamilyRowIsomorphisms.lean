module

public import Integration7.OrdinaryVFVolumeFamilies
public import Integration7.RVMapGammaPointIsomorphisms
public import IntegrationSection6.MixedVFParameterDomains
public import Integration7.AllDegreeVolumeClasses

@[expose] public section

/-! Equality of ordinary RV[0] row classes gives actual Gamma row
isomorphisms over the original base and the named VF tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaIso)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b : ℕ}

theorem ordinary_volume_family_row_gamma_iso
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C n a) (G : OrdinaryVFVolumeFamily C n b)
    (x : Fin n → VFType (M := M))
    (h : rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.rowInContext x)) :
    Nonempty (GammaIso (⟨(C.base : Set M) ∪ Set.range (fun j => (x j).val),∅⟩ : Base (M := M))
      (vfParameterFibre (p := n) (n := 0) F.domain.carrier x)
      (vfParameterFibre (p := n) (n := 0) G.domain.carrier x)) := by
  obtain ⟨e⟩ := (rvVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C x)).mp h
  have hΓ := gamma_rv_map_graph_of_term_closure hc (B :=
    (⟨(C.base : Set M) ∪ Set.range (fun j => (x j).val),∅⟩ : Base (M := M))) (finiteIsoMap e)
  let f := rvMapGammaPointIso (finiteIsoMap e) (finiteIsoMap_bijective e) hΓ
  have hF : {p : Point (M := M) 0 a | p.2 ∈ (F.rowInContext x).obj.domain.carrier} =
      vfParameterFibre (p := n) (n := 0) F.domain.carrier x := by
    ext p
    change (x,p.2) ∈ F.domain.carrier ↔ (Fin.append x p.1,p.2) ∈ F.domain.carrier
    have he : Fin.append x p.1=x := funext (fun i => Fin.append_left x p.1 i)
    rw [he]
  have hG : {p : Point (M := M) 0 b | p.2 ∈ (G.rowInContext x).obj.domain.carrier} =
      vfParameterFibre (p := n) (n := 0) G.domain.carrier x := by
    ext p
    change (x,p.2) ∈ G.domain.carrier ↔ (Fin.append x p.1,p.2) ∈ G.domain.carrier
    have he : Fin.append x p.1=x := funext (fun i => Fin.append_left x p.1 i)
    rw [he]
  exact ⟨f.congr hF hG⟩

end IntegrationInACVF.Section7
