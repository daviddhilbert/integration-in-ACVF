module

public import Integration7.VolumeLiftDescent
public import Integration7.VFVolumeLifts
public import Integration7.MixedJacobianRestriction
public import Integration7.FiniteVolumeIsoMaps
public import Integration7.EssentialVolumeRestriction
public import Section7.LiftedIsomorphism

@[expose] public section

/-! A full lift compatible with a full RV isomorphism descends to the
volume category. Restriction to essential labels and its Jacobian are proved
from the full map, rather than supplied as additional hypotheses. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem finiteIsoMap_mem_essential_iff
    {U V : RVFiniteObject (M := M) S (k+1)} (e : U ≅ V) (u : U.obj.domain) :
    (finiteIsoMap e u).val ∈ (rvEssentialLabels V.obj).carrier ↔
      u.val ∈ (rvEssentialLabels U.obj).carrier := by
  change ((finiteIsoMap e u).val ∈ V.obj.domain.carrier ∧
      (finiteIsoMap e u).val ∉ (rvLowDomain V.obj).carrier) ↔
    (u.val ∈ U.obj.domain.carrier ∧ u.val ∉ (rvLowDomain U.obj).carrier)
  have hw : rvWeight (U.obj.value u) = rvWeight (V.obj.value (finiteIsoMap e u)) :=
    rvIso_weight ((finiteVolumeProperty S (k+1)).ι.mapIso e) u
  rw [mem_rvLowDomain, mem_rvLowDomain, hw]
  exact (and_iff_right (finiteIsoMap e u).property).trans
    (and_iff_right u.property).symm

def RVVolumeIso.of_preserving_full_lift
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (e : U.underlying ≅ V.underlying)
    (f : Map (rvLift U.underlying.obj) (rvLift V.underlying.obj))
    (hf : Function.Bijective f)
    (hlabel : ∀ p, liftLabelMap V.underlying.obj (f p) =
      finiteIsoMap e (liftLabelMap U.underlying.obj p))
    (hMeasure : PreservesVFVolume (rvVolumeLift U).form (rvVolumeLift V).form f) :
    RVVolumeIso U V := by
  have hU : (rvLift U.essential.obj).carrier ⊆ (rvLift U.underlying.obj).carrier :=
    fun _ hp => ((rvLift_restrict_mem_iff _ _ _ _).mp hp).1
  have hV : (rvLift V.essential.obj).carrier ⊆ (rvLift V.underlying.obj).carrier :=
    fun _ hp => ((rvLift_restrict_mem_iff _ _ _ _).mp hp).1
  have hEss (p : rvLift U.underlying.obj) :
      p.val ∈ (rvLift U.essential.obj).carrier ↔
        (f p).val ∈ (rvLift V.essential.obj).carrier := by
    change p.val ∈ (rvLift (U.underlying.obj.restrict (rvEssentialLabels U.underlying.obj)
      (rvEssentialLabels_subset U.underlying.obj))).carrier ↔
      (f p).val ∈ (rvLift (V.underlying.obj.restrict (rvEssentialLabels V.underlying.obj)
        (rvEssentialLabels_subset V.underlying.obj))).carrier
    rw [rvLift_restrict_mem_iff, rvLift_restrict_mem_iff]
    simp only [and_iff_right p.property, and_iff_right (f p).property]
    change (liftLabelMap U.underlying.obj p).val ∈ (rvEssentialLabels U.underlying.obj).carrier ↔
      (liftLabelMap V.underlying.obj (f p)).val ∈ (rvEssentialLabels V.underlying.obj).carrier
    rw [hlabel]
    exact (finiteIsoMap_mem_essential_iff e _).symm
  let g : Map (rvLift U.essential.obj) (rvLift V.essential.obj) :=
    (f.restrict hU).corestrict (fun p => (hEss ⟨p.val, hU p.property⟩).mp p.property)
  have hg : Function.Bijective g := by
    constructor
    · intro p q hpq
      have h : f ⟨p.val, hU p.property⟩ = f ⟨q.val, hU q.property⟩ :=
        Subtype.ext (congrArg (fun w : rvLift V.essential.obj => w.val) hpq)
      exact Subtype.ext (congrArg (fun z : rvLift U.underlying.obj => z.val) (hf.1 h))
    · intro q
      obtain ⟨p, hp⟩ := hf.2 ⟨q.val, hV q.property⟩
      have hpe : p.val ∈ (rvLift U.essential.obj).carrier :=
        (hEss p).mpr (by rw [hp]; exact q.property)
      exact ⟨⟨p.val, hpe⟩, Subtype.ext
        (congrArg (fun z : rvLift V.underlying.obj => z.val) hp)⟩
  have hgl : ∀ p : rvLift U.essential.obj,
      (finiteIsoMap (rvFiniteEssentialIso e)).graph p.val.2 (g p).val.2 := by
    intro p
    refine ⟨liftLabelMap U.essential.obj p, rfl, ?_⟩
    exact (congrArg (fun z : V.underlying.obj.domain => z.val)
      (hlabel ⟨p.val, hU p.property⟩)).symm
  have hm : PreservesVFVolume (rvVolumeLift U.essentialCore).form
      (rvVolumeLift V.essentialCore).form g :=
    preservesVFVolume_of_restriction hc C (Nat.zero_lt_succ k) hU f g
      (fun _ => rfl) (rvVolumeLift U).form (rvVolumeLift V).form
      (rvVolumeLift U.essentialCore).form (rvVolumeLift V.essentialCore).form
      (fun _ => rfl) (fun _ => rfl) hMeasure
  apply RVVolumeIso.of_preserving_lift hc C (rvFiniteEssentialIso e) g hg hgl
  obtain ⟨Z, _, hz, hZ⟩ := hm
  exact ⟨Z, hz, hZ⟩

end IntegrationInACVF.Section7
