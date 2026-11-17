module

public import IntegrationSection5.FiniteNormalization
public import IntegrationSection6.FiniteStandardContractions
public import IntegrationSection6.FiniteGammaIsomorphisms
public import IntegrationSection6.FiniteGammaWeightedIsos

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Convert the completed Section 5 category isomorphisms to the actual
original-Gamma finite-object interface consumed by Section 6. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def gammaStandardComparisonOfNormalizedIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    {A : DefSet (M := M) S n a} (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    {σ υ : Equiv.Perm (Fin n)} (C : StandardContraction A σ) (D : StandardContraction A υ)
    (hC : GammaProgramDefinable B C.program) (hD : GammaProgramDefinable B D.program)
    (e : IntegrationInACVF.Section5.GammaRVIso B C.normalizedObject D.normalizedObject) :
    SpecialTransformations.Section7.GammaRVIso
      (gammaFiniteContraction hκ hs hsmall hBS hA hfin C hC).toGammaRVObject
      (gammaFiniteContraction hκ hs hsmall hBS hA hfin D hD).toGammaRVObject := by
  let U := gammaFiniteContraction hκ hs hsmall hBS hA hfin C hC
  let V := gammaFiniteContraction hκ hs hsmall hBS hA hfin D hD
  let f := rvIsoHomMap e.iso
  let g := rvIsoInvMap e.iso
  have hLeft (u : rvObjectDomain C.normalizedObject) : g (f u) = u :=
    congrArg (fun h : @RVHom M N S n C.normalizedObject C.normalizedObject =>
      @RVHom.map M N S n C.normalizedObject C.normalizedObject h u) e.iso.hom_inv_id
  have hRight (v : rvObjectDomain D.normalizedObject) : f (g v) = v :=
    congrArg (fun h : @RVHom M N S n D.normalizedObject D.normalizedObject =>
      @RVHom.map M N S n D.normalizedObject D.normalizedObject h v) e.iso.inv_hom_id
  let E : rvObjectDomain U.object ≃ rvObjectDomain V.object := ⟨f,g,hLeft,hRight⟩
  apply gammaIsoOfFiniteEquiv U V E e.hom_graph
  intro u
  have hw : @rvWeight M N n (@RVObject.value M N S n C.normalizedObject u) =
      @rvWeight M N n (@RVObject.value M N S n D.normalizedObject (f u)) := by
    apply le_antisymm (@RVHom.volumetric M N S n C.normalizedObject D.normalizedObject e.iso.hom u)
    have h := @RVHom.volumetric M N S n D.normalizedObject C.normalizedObject e.iso.inv (f u)
    change @rvWeight M N n (@RVObject.value M N S n D.normalizedObject (f u)) ≤
      @rvWeight M N n (@RVObject.value M N S n C.normalizedObject (g (f u))) at h
    rwa [hLeft] at h
  exact (rawWeight_eq_normalized_weight (gammaVolumeValue U.toGammaRVObject u)).trans
    (hw.trans (rawWeight_eq_normalized_weight (gammaVolumeValue V.toGammaRVObject (E u))).symm)

def gammaStandardComparisonOfNativeIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    {A : DefSet (M := M) S n a} (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    {σ υ : Equiv.Perm (Fin n)} (C : StandardContraction A σ) (D : StandardContraction A υ)
    (hC : GammaProgramDefinable B C.program) (hD : GammaProgramDefinable B D.program)
    (e : IntegrationInACVF.Section5.GammaRVIso B C.contractionObject D.contractionObject) :
    SpecialTransformations.Section7.GammaRVIso
      (gammaFiniteContraction hκ hs hsmall hBS hA hfin C hC).toGammaRVObject
      (gammaFiniteContraction hκ hs hsmall hBS hA hfin D hD).toGammaRVObject := by
  let eC := gamma_firstVolumeIso (Map.image (rawLabelMap C.target)) C.volumeIndex
    (C.gamma_rv_domain (gamma_program_final_set C.program hC))
  let eD := gamma_firstVolumeIso (Map.image (rawLabelMap D.target)) D.volumeIndex
    (D.gamma_rv_domain (gamma_program_final_set D.program hD))
  exact gammaStandardComparisonOfNormalizedIso hκ hs hsmall hBS hA hfin C D hC hD
    (eC.symm.trans (e.trans eD))

end IntegrationInACVF.Section6.FiniteRV
