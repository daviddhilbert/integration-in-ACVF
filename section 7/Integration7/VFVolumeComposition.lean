import Integration7.VFVolumeIsomorphisms
import Integration7.VFVolumeRestrictions

/-! Composition in the actual almost-everywhere volume category. The
middle domains are intersected; the discarded sets are pulled back or
mapped forward by the supplied genuine bijections. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def VFVolumeIso.trans
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V W : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (f : VFVolumeIso U V) (g : VFVolumeIso V W) : VFVolumeIso U W := by
  let I := f.target.inter g.source
  have hIf : I.carrier ⊆ f.target.carrier := Set.inter_subset_left
  have hIg : I.carrier ⊆ g.source.carrier := Set.inter_subset_right
  have hft : VFCofull V.domain f.target := ⟨f.target_subset, f.target_complement_small⟩
  have hgs : VFCofull V.domain g.source := ⟨g.source_subset, g.source_complement_small⟩
  have hIfFull : VFCofull f.target I := hgs.inter_right f.target_subset
  have hIgFull : VFCofull g.source I := hft.inter_left g.source_subset
  let P := definableMapPreimage f.bijection.map I
  let hP := definableMapPreimage_subset f.bijection.map I
  let Q := (g.bijection.map.restrict hIg).image
  have hQ : Q.carrier ⊆ g.target.carrier := by
    rintro x ⟨p, rfl⟩
    exact (g.bijection.map ⟨p.val, hIg p.property⟩).property
  have hPFull : VFCofull U.domain P :=
    (⟨f.source_subset, f.source_complement_small⟩ : VFCofull U.domain f.source).trans hc C
      (hIfFull.preimage f.bijection.map f.bijection.bijective.1)
  have hQFull : VFCofull W.domain Q :=
    (⟨g.target_subset, g.target_complement_small⟩ : VFCofull W.domain g.target).trans hc C
      (hIgFull.image g.bijection.map g.bijection.bijective)
  let F := f.bijection.restrictPreimage hc C I hIf
  let G := g.bijection.restrictImage hc C I hIg
  refine ⟨P, Q, hPFull.subset, hQFull.subset, hPFull.small, hQFull.small, ?_⟩
  exact F.trans hc C G

def positiveVFVolumeIsoSetoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :
    Setoid (PositiveVFVolumeObject (M := M) (C.base : Set M) k) where
  r U V := Nonempty (VFVolumeIso U V)
  iseqv := ⟨fun U => ⟨VFVolumeIso.refl hc C U⟩,
    fun ⟨f⟩ => ⟨f.symm hc C⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans hc C g⟩⟩

end IntegrationInACVF.Section7
