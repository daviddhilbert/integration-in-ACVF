import Integration7.NativeVolumeDomains
import Integration7.RVCoordinateSelection
import Integration7.GammaTermContextVolumeGeometry

/-! An actual finite selected tuple and a retained nonzero density on a
pure RV native domain give the corresponding literal volume object. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a k : ℕ}

def nativeCoordinateDensityVolumeObject (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 a)
    (ι : Fin (k+1) → Fin a) (δ : Fin a)
    (hfin : ∀ t : Fin (k+1) → RV (M := M),
      {r : Fin a → RV (M := M) | (Fin.elim0,r) ∈ carrier U ∧ r ∘ ι = t}.Finite)
    (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) k where
  underlying := {
    obj := ⟨a,rawVolumeContractionLabels hc U,
      (rvCoordinateSelectMap (C.base : Set M) ι).restrict (Set.subset_univ _)⟩
    property := by
      intro y
      apply (hfin y.val).of_injOn (f := fun u : rawVolumeContractionLabels hc U => u.val)
      · intro u hu
        exact ⟨(mem_rawVolumeContractionLabels hc U u.val).mp u.property,congrArg Subtype.val hu⟩
      · intro u hu v hv he
        exact Subtype.ext he }
  form := {
    map := (rvCoordinateSelectMap (C.base : Set M) (fun _ : Fin 1 => δ)).restrict (Set.subset_univ _)
    nonzero := fun u => (rv_nonzero_iff_raw _).mpr
      (hδ ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc U u.val).mp u.property⟩) }

theorem native_coordinate_density_volume_object_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 a)
    (ι : Fin (k+1) → Fin a) (δ : Fin a)
    (hfin : ∀ t : Fin (k+1) → RV (M := M),
      {r : Fin a → RV (M := M) | (Fin.elim0,r) ∈ carrier U ∧ r ∘ ι = t}.Finite)
    (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) :
    VolumeObjectGamma (nativeCoordinateDensityVolumeObject hc C U ι δ hfin hδ)
      (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) := by
  apply VolumeObjectGamma.of_term_context hc C
  change (C.base : Set M) = (Substructure.closure LRV (C.base : Set M) : Set M)
  rw [Substructure.closure_eq]

end IntegrationInACVF.Section7
