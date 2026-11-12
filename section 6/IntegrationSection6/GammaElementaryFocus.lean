import IntegrationSection6.GammaVolumeImage
import IntegrationSection6.NormalizedCanonicalLifts
import IntegrationSection6.AdmissibleFocusExistence

/-! Focus existence for every actual original-Gamma admissible object.
Preparatory canonical labeling supplies the required tag; only B.real,
not the real presentation code set, is bounded by saturation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

theorem gamma_typedLift_definable (U : GammaRVObject B n) :
    GammaSetDefinable B (carrier (typedLift U.object)) := by
  have he : carrier (typedLift U.object) = U.lift := by
    ext p
    exact typedLift_mem U.object p
  rw [he]
  exact U.lift_definable

theorem gamma_canonicalTypedLift_definable (U : GammaRVObject B n) :
    GammaSetDefinable B (carrier (canonicalTypedLift U.object)) :=
  GammaPrimitiveDefinable.target (gammaLogicInput B) (.canonical (typedLift U.object))
    (gamma_typedLift_definable U)

theorem canonicalTypedLift_pullback
    (U : @RVObject M (@CanonicalStructure.normalize M sM) B.real n) :
    IsRVPullback (carrier (canonicalTypedLift U)) :=
  Primitive.preserves_pullback (.canonical (typedLift U)) (typedLift_pullback U)

theorem typedLift_keys_mem_volumeImage (U : GammaRVObject B n)
    (p : Point (M := M) n (rvObjectArity U.object))
    (hp : p ∈ carrier (typedLift U.object)) :
    (fun i => (rv (p.1 i)).val) ∈ gammaVolumeImage U := by
  obtain ⟨u,_,hv⟩ := (typedLift_mem U.object p).mp hp
  refine ⟨u,?_⟩
  have hh := hv.trans (@normalized_tupleRV M sM hM n p.1)
  exact congrArg (fun t : Fin n → RV (M := M) => fun i => (t i).val) hh

theorem canonicalTypedLift_keys_mem_volumeImage (U : GammaRVObject B n)
    (p : Point (M := M) n (n+rvObjectArity U.object))
    (hp : p ∈ carrier (canonicalTypedLift U.object)) :
    (fun i => (rv (p.1 i)).val) ∈ gammaVolumeImage U := by
  obtain ⟨a,ha,rfl⟩ := (Set.ext_iff.mp (canonicalImage_carrier (typedLift U.object)) p).mp hp
  exact typedLift_keys_mem_volumeImage U a ha

/-- The original-Gamma whole-fibre root construction now applies to the
actual lift of every elementary-blowup input, with its canonical tag. -/
theorem GammaAdmissible.exists_canonical_fullFocus {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    {U : GammaRVObject B n} {i : Fin n} (hAd : GammaAdmissible U i) :
    ∃ D : Focus (canonicalTypedLift U.object) i (Fin.castAdd (rvObjectArity U.object) i),
      D.locus = carrier (canonicalTypedLift U.object) ∧ GammaFocusDefinable B D := by
  have hp : IsRVPullback (carrier (canonicalTypedLift U.object)) :=
    Primitive.preserves_pullback (.canonical (typedLift U.object)) (typedLift_pullback U.object)
  exact exists_fullFocus_on_admissible_image hκ hs h00 B hsmall hB U.real_contains
    (canonicalTypedLift U.object) hp (gamma_canonicalTypedLift_definable U)
    i (Fin.castAdd (rvObjectArity U.object) i) (canonicalTypedLift_tagged U.object i)
    (gammaVolumeImage U) (gammaVolumeImage_definable U)
    (fun p hp => canonicalTypedLift_keys_mem_volumeImage U p hp)
    (fun _ ht => hAd.image_nonzero ht) (fun t ht => hAd.image_algebraic t ht)

end IntegrationInACVF.Section6
