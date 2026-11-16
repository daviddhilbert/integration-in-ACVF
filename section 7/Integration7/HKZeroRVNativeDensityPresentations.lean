module

public import Integration7.HKZeroRVDensityPresentations

@[expose] public section

/-! Native finite presentations of arbitrary weighted zero coefficients.
The exact density graph is used; no positive point is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))

def zeroRVNativeDensityDomain := ordinaryRVNativeDomain hc C Z.densityGraph.underlying

theorem zero_rv_native_density_nonzero (q : zeroRVNativeDensityDomain hc C Z) :
    (q.val.2 (Fin.last Z.underlying.obj.arity)).val ≠ iRVZero := by
  let u : Z.densityGraph.underlying.obj.domain := ⟨q.val.2,q.property.2⟩
  exact (rv_nonzero_iff_raw _).mp (fun hz => Z.densityGraph.form.nonzero u
    ((Z.densityGraph_density_last u).trans hz))

def zeroRVNativeDensityObject := nativeZeroDensityObject hc C (zeroRVNativeDensityDomain hc C Z)
  (Fin.last Z.underlying.obj.arity) (ordinary_rv_native_labels_finite hc C Z.densityGraph.underlying)
  (zero_rv_native_density_nonzero hc C Z)

def zeroRVNativeDensityIso : ZeroRVVolumeIso Z (zeroRVNativeDensityObject hc C Z) := by
  let D := Z.densityGraph
  let V := zeroRVNativeDensityObject hc C Z
  have hDV : D.underlying.obj.domain.carrier = V.underlying.obj.domain.carrier :=
    (ordinary_rv_native_labels_carrier hc C D.underlying).symm
  let f : Map D.underlying.obj.domain V.underlying.obj.domain := Map.inclusion hDV.le
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      have hv : (f u).val = (f v).val := congrArg Subtype.val h
      exact Subtype.ext hv
    · intro u
      exact ⟨⟨u.val,hDV.ge u.property⟩,rfl⟩
  exact (zeroRVDensityGraphIso Z).trans (ZeroRVVolumeIso.ofBijection f hf
    (fun u => Z.densityGraph_density_last u))

end IntegrationInACVF.Section7.HK
