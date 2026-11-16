module

public import Integration7.NativeOrdinaryRVVolumeFactors
public import Integration7.HKZeroRVVolumeIsomorphisms

@[expose] public section

/-! A finite pure RV set with a nonzero retained label is a measured
degree-zero object. Its density is not replaced by a unit form. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {d : ℕ}

def nativeZeroDensityObject (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
    (ε : Fin d) (hR : (rawVolumeContractionLabels hc R).carrier.Finite)
    (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero) : ZeroRVVolumeObject (M := M) (C.base : Set M) where
  underlying := nativeOrdinaryRVObject hc C R hR
  form := {
    map := (rvCoordinateSelectMap (C.base : Set M) (fun _ : Fin 1 => ε)).restrict (Set.subset_univ _)
    nonzero := fun u => (rv_nonzero_iff_raw _).mpr
      (hε ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc R u.val).mp u.property⟩) }

theorem native_zero_density_value (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
    (ε : Fin d) (hR : (rawVolumeContractionLabels hc R).carrier.Finite)
    (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero)
    (u : (nativeZeroDensityObject hc C R ε hR hε).underlying.obj.domain) :
    (nativeZeroDensityObject hc C R ε hR hε).form.value u = u.val ε := rfl

end IntegrationInACVF.Section7.HK
