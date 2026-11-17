module

public import Integration7.BalancedPreparedVolumeProducts
public import Integration7.CanonicalFiniteRVObjects

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The original balanced Gamma product descends to the actual definable
RV-key isomorphism of the chosen unary preparations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l u v : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

set_option maxHeartbeats 1600000 in
theorem prepared_unary_rv_value_products {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (P : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk P.real < κ)
    (hcM : CanonicalStructure.IsCanonical (M := M))
    {R : Set (VF (M := M) × VF (M := M))} {ε : VF (M := M) → VF (M := M)}
    {r t : RV (M := M)} (h : IsBalanced R ε r t) (hr : r ≠ rv (0 : VF (M := M)))
    {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
    {A' : DefSet (M := M) S 1 u} {B' : DefSet (M := M) S 1 v}
    (f : Map A B) (hf : Function.Bijective f)
    (hDomain : ∀ p : A, vfAt p.val 0 ∈ first R)
    (hValue : ∀ p : A, vfAt (f p).val 0 = ε (vfAt p.val 0))
    (TA : SpecialBijection A A') (TB : SpecialBijection B B')
    (hA' : IsRVPullback (carrier A')) (hB' : IsRVPullback (carrier B'))
    (hc : Contractible (unaryConjugate TA TB f))
    (hback : Contractible (Map.inverse (unaryConjugate TA TB f) (unaryConjugate_bijective TA TB f hf)))
    (hgΓ : GammaGraphDefinable P (pointMapGraph (unaryConjugate TA TB f)))
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S _ _
      (rvObjectVolume (pullbackObject A')))
    (hBF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S _ _
      (rvObjectVolume (pullbackObject B'))) :
    let U := canonicalFiniteRVObject hcM ⟨pullbackObject A',hAF⟩
    let V := canonicalFiniteRVObject hcM ⟨pullbackObject B',hBF⟩
    let e : U ≅ V := rvFiniteIsoOfAmbient (canonicalRVIso hcM
      (unaryRVIso hκ hs hsmall (unaryConjugate TA TB f) (unaryConjugate_bijective TA TB f hf)
        hc hback hA' hB' hgΓ))
    ∀ z : U.obj.domain, (U.obj.value z 0).val ≠ iRVZero →
      Values.vrv r*Values.vrv (V.obj.value (finiteIsoMap e z) 0) =
        Values.vrv (U.obj.value z 0)*Values.vrv t := by
  intro U V e z hz
  obtain ⟨a,ha⟩ := z.property
  have he : z = (⟨(rawKeyMap A' a).val,⟨a,rfl⟩⟩ : U.obj.domain) := Subtype.ext ha.symm
  subst z
  have ha0 : vfAt a.val 0 ≠ 0 := by
    intro ha0
    apply hz
    change (rv (vfAt a.val 0)).val = iRVZero
    exact (CanonicalRV.encodedRv_zero_iff _).mpr ha0
  have hSpec := unaryRVIso_spec hκ hs hsmall (unaryConjugate TA TB f)
    (unaryConjugate_bijective TA TB f hf) hc hback hA' hB' hgΓ a
  have hV : V.obj.value (finiteIsoMap e ⟨(rawKeyMap A' a).val,⟨a,rfl⟩⟩) 0 =
      rv (vfAt (unaryConjugate TA TB f a).val 0) := by
    apply Subtype.ext
    exact congrArg (fun q : rvObjectDomain (pullbackObject B') =>
      (q.val (Fin.castAdd v (0 : Fin 1))).val) hSpec
  have hU : U.obj.value ⟨(rawKeyMap A' a).val,⟨a,rfl⟩⟩ 0 = rv (vfAt a.val 0) := rfl
  rw [hV,hU]
  exact balanced_prepared_volume_products h hr f hf hDomain hValue TA TB hA' hB' hc hback a ha0

end IntegrationInACVF.Section7
