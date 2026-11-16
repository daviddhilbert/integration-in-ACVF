import Integration7.HKAEZeroVolumeFunctions
import Integration7.HKDensityEqualityGraphs
import Integration7.RVMapGammaPointIsomorphisms
import IntegrationSection6.MixedVFParameterDomains
import IntegrationSection6.GammaSortedParameterPreservation

/-! Equality of weighted zero row classes supplies an actual row
isomorphism preserving the original RV form, over the named VF tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaIso)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b : ℕ}

theorem zero_volume_family_row_gamma_iso
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C n a) (G : ZeroVFVolumeFamily C n b)
    (x : Fin n → VFType (M := M))
    (h : rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.rowInContext x)) :
    ∃ e : GammaIso (⟨(C.base : Set M) ∪ Set.range (fun j => (x j).val),∅⟩ : Base (M := M))
      (vfParameterFibre (p := n) (n := 0) F.domain.carrier x)
      (vfParameterFibre (p := n) (n := 0) G.domain.carrier x),
      ∀ u : vfParameterFibre (p := n) (n := 0) F.domain.carrier x,
        densityEqualRelation F.form G.form (Fin.append x u.val.1,u.val.2)
        (Fin.append x (e.equiv u).val.1,(e.equiv u).val.2) := by
  obtain ⟨e⟩ := (rvVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C x)).mp h
  have hΓ := gamma_rv_map_graph_of_term_closure hc (B :=
    (⟨(C.base : Set M) ∪ Set.range (fun j => (x j).val),∅⟩ : Base (M := M))) (finiteIsoMap e.iso)
  let f := rvMapGammaPointIso (finiteIsoMap e.iso) (finiteIsoMap_bijective e.iso) hΓ
  have hF : {p : Point (M := M) 0 a | p.2 ∈ (F.rowInContext x).underlying.obj.domain.carrier} =
      vfParameterFibre (p := n) (n := 0) F.domain.carrier x := by
    ext p
    change (x,p.2) ∈ F.domain.carrier ↔ (Fin.append x p.1,p.2) ∈ F.domain.carrier
    have he : Fin.append x p.1=x := funext (fun i => Fin.append_left x p.1 i)
    rw [he]
  have hG : {p : Point (M := M) 0 b | p.2 ∈ (G.rowInContext x).underlying.obj.domain.carrier} =
      vfParameterFibre (p := n) (n := 0) G.domain.carrier x := by
    ext p
    change (x,p.2) ∈ G.domain.carrier ↔ (Fin.append x p.1,p.2) ∈ G.domain.carrier
    have he : Fin.append x p.1=x := funext (fun i => Fin.append_left x p.1 i)
    rw [he]
  refine ⟨f.congr hF hG,?_⟩
  intro u
  have hx : Fin.append x u.val.1 = x := funext (fun i => Fin.append_left x u.val.1 i)
  let r : (F.rowInContext x).underlying.obj.domain := ⟨u.val.2,by
    change (x,u.val.2) ∈ F.domain.carrier
    have hu := u.property
    change (Fin.append x u.val.1,u.val.2) ∈ F.domain.carrier at hu
    rw [hx] at hu
    exact hu⟩
  let s := finiteIsoMap e.iso r
  have hy : ((f.congr hF hG).equiv u).val.2 = s.val := by
    rw [gammaIsoCongr_value]
    rfl
  have hx' : Fin.append x ((f.congr hF hG).equiv u).val.1 = x :=
    funext (fun i => Fin.append_left x _ i)
  refine ⟨⟨(x,r.val),r.property⟩,⟨(x,s.val),s.property⟩,?_,?_,e.density r⟩
  · exact Prod.ext hx.symm rfl
  · exact Prod.ext hx'.symm hy.symm

end IntegrationInACVF.Section7.HK
