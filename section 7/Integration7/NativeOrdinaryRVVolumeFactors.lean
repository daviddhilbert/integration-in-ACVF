module

public import Integration7.NativeCoordinateDensityVolumeObjects
public import Integration7.VolumeFormProducts

@[expose] public section

/-! A finite pure-RV label set is an actual ordinary RV[0] object.
Its empty volume tuple carries no artificial density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {d : ℕ}

def nativeOrdinaryRVObject (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
    (hR : (rawVolumeContractionLabels hc R).carrier.Finite) : RVFiniteObject (M := M) (C.base : Set M) 0 where
  obj := ⟨d,rawVolumeContractionLabels hc R,
    (rvCoordinateSelectMap (C.base : Set M) (Fin.elim0 : Fin 0 → Fin d)).restrict (Set.subset_univ _)⟩
  property t := hR.of_injOn (f := fun u : rawVolumeContractionLabels hc R => u.val)
    (fun u _ => u.property) (fun _ _ _ _ he => Subtype.ext he)

def ordinaryRVNativeDomain (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 Z.obj.arity :=
  nativeMixedVolumeDomain hc ((DefSet.univ (rawVFSpace (M := M) 0) (C.base : Set M)).prod Z.obj.domain)

theorem ordinary_rv_native_labels_carrier (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    (rawVolumeContractionLabels hc (ordinaryRVNativeDomain hc C Z)).carrier=Z.obj.domain.carrier := by
  ext r
  rw [mem_rawVolumeContractionLabels]
  change ((Fin.elim0,r).1 ∈ Set.univ ∧ r ∈ Z.obj.domain.carrier) ↔ _
  exact and_iff_right (Set.mem_univ _)

theorem ordinary_rv_native_labels_finite (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    (rawVolumeContractionLabels hc (ordinaryRVNativeDomain hc C Z)).carrier.Finite := by
  rw [ordinary_rv_native_labels_carrier]
  let t : DefSet.univ (rawRVSpace (M := M) 0) (C.base : Set M) := ⟨Fin.elim0,Set.mem_univ _⟩
  apply ((Z.property t).image Subtype.val).subset
  intro r hr
  exact ⟨⟨r,hr⟩,Subtype.ext (funext (fun i => Fin.elim0 i)),rfl⟩
end IntegrationInACVF.Section7
