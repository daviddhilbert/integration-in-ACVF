module

public import IntegrationSection6.CanonicalFiniteContractionIsomorphisms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Exact key, coordinate and old-label identities for the checked
canonical contraction isomorphism of an RV pullback. These strengthen
its weight identity to the full tuple needed by volume objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a : ℕ} {κ : Cardinal}
variable (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk G.real < κ)
variable (hGS : G.real ⊆ S) {U : DefSet (M := M) S n a}
variable (hU : GammaSetDefinable G (carrier U))
variable (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
variable (hUF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
  (@CanonicalStructure.normalize M sM) _ _ S _ _
  (rvObjectVolume (pullbackObject U)))
variable {σ : Equiv.Perm (Fin n)} (T : StandardContraction U σ) (hT : GammaProgramDefinable G T.program)
variable (hVF : ∀ u : U, (T.naturalMap u).val.1 = u.val.1) (hcon : Contractible T.toMap)

set_option maxHeartbeats 1600000 in
theorem canonical_contraction_key_square (p : U) :
    ((FiniteRV.gammaCanonicalContractionIso hκ hs hreal hGS hU hfin hUF T hT hVF hcon).equiv
      (Map.toImage (rawKeyMap U) p)).val = (T.normalizedContractionMap p).val := by
  let f := typedContractionNaturalMap T
  let hc := typedContractionNaturalMap_contractible T hVF hcon
  change (@RVHom.map M (@CanonicalStructure.normalize M sM) S n _ _
    (pullbackPresentationIso (normalizedTypedLift_presents T.normalizedObject)).hom
      (rvContractionMap f hc (Map.toImage (rawKeyMap U) p))).val = _
  rw [pullbackPresentationIso_labels,rvContractionMap_spec]
  funext i
  erw [rawKeyMap_apply]
  simp only [Fin.append_right]
  change (typedContractionNaturalMap T p).val.2 i = (T.normalizedContractionMap p).val i
  exact congrFun (T.normalizedNaturalLiftMap_square p) i

theorem canonical_contraction_coordinates
    (u : rvObjectDomain (pullbackObject U)) :
    gammaVolumeValue (FiniteRV.gammaFiniteContraction hκ hs hreal hGS hU hfin T hT).toGammaRVObject
      ((FiniteRV.gammaCanonicalContractionIso hκ hs hreal hGS hU hfin hUF T hT hVF hcon).equiv u) =
      gammaVolumeValue (FiniteRV.gammaPullbackAt hGS U hU hUF).toGamma.toGammaRVObject u := by
  obtain ⟨p,rfl⟩ := rawKeyImage_surjective U u
  have he := canonical_contraction_key_square hκ hs hreal hGS hU hfin hUF T hT hVF hcon p
  have hPoint : (FiniteRV.gammaCanonicalContractionIso hκ hs hreal hGS hU hfin hUF T hT hVF hcon).equiv
      (Map.toImage (rawKeyMap U) p) = T.normalizedContractionMap p := Subtype.ext he
  rw [hPoint]
  funext i
  change (rvObjectVolume T.normalizedObject (T.normalizedContractionMap p)).val i =
    (rvObjectVolume (pullbackObject U) (Map.toImage (rawKeyMap U) p)).val i
  rw [pullbackObject_value_key]
  rw [T.normalizedObject_first]
  have h := congrFun (T.normalizedNaturalRawMap_labels p) (Fin.castAdd T.arity i)
  change (canonical (T.naturalMap p).val).2 (Fin.castAdd T.arity i) =
    (T.normalizedContractionMap p).val (Fin.castAdd T.arity i) at h
  rw [canonical_new] at h
  exact h.symm.trans (congrArg rv (congrFun (hVF p) i))

theorem canonical_contraction_retained_labels
    (u : rvObjectDomain (pullbackObject U)) (i : Fin a) :
    ((FiniteRV.gammaCanonicalContractionIso hκ hs hreal hGS hU hfin hUF T hT hVF hcon).equiv u).val
      (FiniteRV.contractionOldLabelIndex T i) = u.val (Fin.natAdd n i) := by
  obtain ⟨p,rfl⟩ := rawKeyImage_surjective U u
  rw [canonical_contraction_key_square hκ hs hreal hGS hU hfin hUF T hT hVF hcon p]
  erw [rawKeyMap_apply]
  simp only [Fin.append_right]
  exact FiniteRV.contraction_oldLabels T p i

end IntegrationInACVF.Section7
