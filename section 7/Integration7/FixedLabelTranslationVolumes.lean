module

public import Integration7.FixedRVLabelDomainBijections
public import Integration7.NativeRelativeTranslationVolumes
public import Integration7.FixedLabelProductHeadGeometry
public import Integration7.TwoOrderProductCoordinateDensities

@[expose] public section

/-! Actual translations of pure VF domains carry fixed old RV labels
and still have Jacobian one almost everywhere on the resulting mixed domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n d : ℕ}

theorem fixed_pure_rv_label_fibres_finite (A : DefSet (M := M) S n 0)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S) :
    ∀ x : Fin n → VF (M := M),
      {u : Fin (0+d) → RV (M := M) | (x,u) ∈ carrier (fixedRVLabelDomain A z hz)}.Finite := by
  intro x
  apply (Set.finite_singleton (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) z)).subset
  intro u hu
  exact Set.mem_singleton_iff.mpr ((fixed_pure_vf_label_domain_carrier A z hz (x,u)).mp hu).2

set_option maxHeartbeats 1200000 in
theorem fixed_rv_label_translation_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    (A : DefSet (M := M) (C.base : Set M) n 0) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) (C.base : Set M)))
    (hC : ∀ p q : A, erase i p.val = erase i q.val → (c p).val 0 = (c q).val 0)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M)) :
    VFAlmostEverywhere (rawSpecialSet hc (fixedRVLabelDomain A z hz))
      (fun p => HasMixedVFJacobianAt
        (rawSpecialMap hc (fixedRVLabelMap (relativeTranslationToImage A i c) z hz)) p 1) := by
  let f := fixedRVLabelMap (relativeTranslationToImage A i c) z hz
  have hi : UnaryRelative f i := fixed_rv_label_map_relative (relativeTranslationToImage A i c) (relative_translation_unary_relative A i c) z hz
  apply relative_fibre_translation_jacobian_one hc C hn f i hi
    (fun u _ => relativeTranslationFibreCentre A i c u Fin.elim0)
  intro u q
  let p : fixedRVLabelDomain A z hz := ⟨coordinateInsert i u q.val,q.property⟩
  let p0 := fixedRVLabelProjectionMap A z hz p
  have hErase : erase i p0.val = erase i (u,Fin.elim0) :=
    Prod.ext (Function.update_idem _ _ _) (Subsingleton.elim _ _)
  have hCentre := relative_translation_fibre_centre_value A i c hC p0 u Fin.elim0 hErase
  rw [coordinateFibreMap_apply]
  change (fixedRVLabelMap (relativeTranslationToImage A i c) z hz p).val.1 i = _
  rw [fixed_rv_label_map_vf,hCentre]
  change (relativeTranslationMap A i c p0).val.1 i = _
  rw [relative_translation_map_value]
  simp only [replace,Function.update_self]
  have hVF : (show VFType (M := M) from p0.val.1 i) = q.val.1 0 := by
    exact Function.update_self i (q.val.1 0) u
  exact congrArg (fun x : VFType (M := M) => x - (show VFType (M := M) from (c p0).val 0)) hVF

theorem fixed_rv_label_translation_preserves_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    (A : DefSet (M := M) (C.base : Set M) n 0) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) (C.base : Set M)))
    (hC : ∀ p q : A, erase i p.val = erase i q.val → (c p).val 0 = (c q).val 0)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (ω : VolumeForm (rawSpecialSet hc (fixedRVLabelDomain A z hz)))
    (π : VolumeForm (rawSpecialSet hc (fixedRVLabelDomain (relativeTranslationImage A i c) z hz)))
    (hDensity : ∀ p, ω.value p = π.value
      (rawSpecialMap hc (fixedRVLabelMap (relativeTranslationToImage A i c) z hz) p)) :
    PreservesVFVolume ω π (rawSpecialMap hc (fixedRVLabelMap (relativeTranslationToImage A i c) z hz)) :=
  (fixed_rv_label_translation_jacobian_one hc C hn A i c hC z hz).mono
    (fun p hJ => ⟨1,hJ,by rw [RVOperations.rv_one,mul_one];exact hDensity p⟩)

end IntegrationInACVF.Section7
