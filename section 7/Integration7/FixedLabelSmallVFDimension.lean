import Integration7.FixedLabelContractionLiftGeometry
import Integration7.FixedRVLabelDomainBijections
import Integration7.FixedLabelProductHeadGeometry
import Integration7.NativeVFPairImages
import Section4.CoordinateMaps

/-! A pure two-coordinate domain on which one VF coordinate determines
the other has VF dimension at most one after adjoining fixed labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV VF carrier vfAt)
open IntegrationInACVF.Section5
open IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {d : ℕ}

theorem fixed_label_vf_dimension_le_one_of_coordinate
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S 2 0) (i : Fin 2)
    (hDet : ∀ p q : A, vfAt p.val i = vfAt q.val i → p.val.1 = q.val.1)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S) :
    vfDim (rawRVSpace (M := M) 1) (rawSpecialSet hc (fixedRVLabelDomain A z hz)) ≤ 1 := by
  let H := rawSpecialSet hc (fixedRVLabelDomain A z hz)
  let f := vfSelect (fun _ : Fin 1 => i) H
  have hf : Function.Injective f := by
    intro p q he
    have hh := congrArg Subtype.val he
    have hv0 := congrArg Prod.fst hh
    have hv : p.val.1 i = q.val.1 i := congrFun hv0 0
    have hr := congrArg Prod.snd hh
    let p0 := fixedRVLabelProjectionMap A z hz ⟨p.val,p.property⟩
    let q0 := fixedRVLabelProjectionMap A z hz ⟨q.val,q.property⟩
    have hVF : p.val.1 = q.val.1 := hDet p0 q0 hv
    exact Subtype.ext (Prod.ext hVF hr)
  exact (vfDim_le_of_finite_map (rawRVSpace (M := M) 1) f
    (Map.finiteFibres_of_injective hf)).trans (vfDim_le_arity _ _)

theorem native_graph_coordinate_determines
    (A : SpecialTransformations.Section5.DefSet (M := M) S 2 0)
    (f : VF (M := M) → VF (M := M))
    (hGraph : ∀ p ∈ nativeVFPairDomain A, p.2 = f p.1) :
    ∀ p q : A, vfAt p.val 0 = vfAt q.val 0 → p.val.1 = q.val.1 := by
  intro p q he
  have hp := hGraph (twoVFPointPairEquiv p.val) ⟨p.val,p.property,rfl⟩
  have hq := hGraph (twoVFPointPairEquiv q.val) ⟨q.val,q.property,rfl⟩
  funext j
  fin_cases j
  · exact he
  · exact hp.trans ((congrArg f he).trans hq.symm)

theorem native_first_singleton_coordinate_determines
    (A : SpecialTransformations.Section5.DefSet (M := M) S 2 0)
    (a : VF (M := M)) (hFirst : first (nativeVFPairDomain A) = {a}) :
    ∀ p q : A, vfAt p.val 1 = vfAt q.val 1 → p.val.1 = q.val.1 := by
  intro p q he
  have hp : vfAt p.val 0 ∈ first (nativeVFPairDomain A) :=
    ⟨twoVFPointPairEquiv p.val,⟨p.val,p.property,rfl⟩,rfl⟩
  have hq : vfAt q.val 0 ∈ first (nativeVFPairDomain A) :=
    ⟨twoVFPointPairEquiv q.val,⟨q.val,q.property,rfl⟩,rfl⟩
  rw [hFirst] at hp hq
  funext j
  fin_cases j
  · exact hp.trans hq.symm
  · exact he

end IntegrationInACVF.Section7
