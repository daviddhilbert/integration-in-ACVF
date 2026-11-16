module

public import Integration7.HKUpstreamRVZero
public import Integration7.HKZeroVolumeIntegration
public import Section4.VFDimensionRank

@[expose] public section

/-! The predecessor uses its actual Gamma imaginary in the dimension bound;
the sequel uses an RV-coded auxiliary space. The checked rank criterion
identifies these bounds on every mixed presentation over the same base.
The adapters retain the presentation and its complete form, pointwise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section10

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem zero_dimension_auxiliary_iff
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) (C.base : Set M)) :
    vfDim (rawRVSpace (M := M) 1) A ≤ 0 ↔ vfDim (volumeGammaSpace hc) A ≤ 0 :=
  (vfDim_le_iff_point_trdeg hc C.saturated C.small _ (rawRVSpace_rvCoded 1) A 0).trans
    (vfDim_le_iff_point_trdeg hc C.saturated C.small _ (volumeGammaSpace_rvCoded hc) A 0).symm

def ZeroVFVolumeObject.toUpstream
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : ZeroVFVolumeObject (M := M) (C.base : Set M)) :
    MeasuredVFZero hc (C.base : Set M) rvVolumeScale where
  underlying := ⟨⟨A.underlying.obj.obj,
    (zero_dimension_auxiliary_iff hc C A.underlying.obj.obj.set).mp A.underlying.obj.property⟩,
    A.underlying.property⟩
  form := formToUpstream A.form

def ZeroVFVolumeObject.fromUpstream
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : MeasuredVFZero hc (C.base : Set M) rvVolumeScale) :
    ZeroVFVolumeObject (M := M) (C.base : Set M) where
  underlying := ⟨⟨A.underlying.obj.obj,
    (zero_dimension_auxiliary_iff hc C A.underlying.obj.obj.set).mpr A.underlying.obj.property⟩,
    A.underlying.property⟩
  form := formFromUpstream A.form

def upstreamVFZeroEquiv (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    ZeroVFVolumeObject (M := M) (C.base : Set M) ≃
      MeasuredVFZero hc (C.base : Set M) rvVolumeScale where
  toFun := ZeroVFVolumeObject.toUpstream hc C
  invFun := ZeroVFVolumeObject.fromUpstream hc C
  left_inv A := by cases A with | mk A ω => cases A; cases ω; rfl
  right_inv A := by cases A with | mk A ω => cases A; cases ω; rfl

@[simp] theorem ZeroVFVolumeObject.toUpstream_weight
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : ZeroVFVolumeObject (M := M) (C.base : Set M)) (a : A.underlying.obj.obj.set) :
    (A.toUpstream hc C).weight a = A.form.value a := rfl

def ZeroVFVolumeIso.toUpstream
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A B : ZeroVFVolumeObject (M := M) (C.base : Set M)} (e : ZeroVFVolumeIso A B) :
    A.toUpstream hc C ≅ B.toUpstream hc C := by
  let E := (vfDimensionProperty (rawRVSpace (M := M) 1) (C.base : Set M) 0).ι.mapIso
    ((vfBoundedFiniteProperty (rawRVSpace (M := M) 1) (C.base : Set M) 0).ι.mapIso e.iso)
  exact WeightedZero.isoOfExactMap ⟨finiteZeroVFMap e.iso, DefinableSetCat.bijective_of_iso E, e.density⟩

def ZeroVFVolumeIso.fromUpstream
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A B : ZeroVFVolumeObject (M := M) (C.base : Set M)}
    (e : A.toUpstream hc C ≅ B.toUpstream hc C) : ZeroVFVolumeIso A B := by
  let f : Map A.underlying.obj.obj.set B.underlying.obj.obj.set := e.hom.map
  let i : A.underlying ≅ B.underlying := by
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    exact DefinableSetCat.isoOfBijective f e.hom.bijective
  refine ⟨i, ?_⟩
  intro a
  change A.form.value a = B.form.value (f a)
  exact e.hom.preserves a

theorem upstream_zero_vf_iso_iff
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A B : ZeroVFVolumeObject (M := M) (C.base : Set M)) :
    Nonempty (A.toUpstream hc C ≅ B.toUpstream hc C) ↔ Nonempty (ZeroVFVolumeIso A B) :=
  ⟨fun ⟨e⟩ => ⟨ZeroVFVolumeIso.fromUpstream hc C e⟩,
    fun ⟨e⟩ => ⟨e.toUpstream hc C⟩⟩

theorem upstream_zero_lift (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    (zeroLift U).toUpstream hc C = U.toUpstream.lift hc := rfl

end IntegrationInACVF.Section7.HK
