module

public import Integration7.LiteralVolumeLiftMaps
public import Integration7.MixedJacobianOneOperations
public import Integration7.SpecialVolumeJacobians
public import IntegrationSection6.CanonicalFocusDiagram
public import IntegrationSection5.RelativeLabelPreservation

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual special-focus lift of an elementary blowup has Jacobian
one and preserves every original RV label. Its density equation therefore
holds for any source RV density pulled back along the elementary projection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
variable {U : @RVObject M (@CanonicalStructure.normalize M sM) S n}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n (@RVObject.arity M (@CanonicalStructure.normalize M sM) _ n U)}
variable (h : @Section6.PresentsLift M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) S n U (normalizedPointSet A))
variable {i : Fin n} {j : Fin (n+(@RVObject.arity M (@CanonicalStructure.normalize M sM) _ n U))} (D : Focus (canonicalImage A) i j)
variable (hFull : carrier (canonicalImage A) ⊆ D.locus) (hAd : @Section6.Admissible M (@CanonicalStructure.normalize M sM) S n U i)

def canonicalFocusLiftMap : SpecialTransformations.Section5.Map A (typedLift (@Section6.elementary M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) S n U i)) :=
  SpecialTransformations.Section5.Map.comp (canonicalFocusRelabelMap h D hFull hAd)
    (canonicalFocusSpecial A D).toMap

theorem canonical_focus_lift_map_bijective (hA : IsRVPullback (carrier A)) :
    Function.Bijective (canonicalFocusLiftMap h D hFull hAd) :=
  (canonicalFocusRelabelMap_bijective h D hFull hAd hA).comp (canonicalFocusSpecial A D).bijective

theorem canonical_focus_lift_original_labels (a : A) :
    (canonicalFocusLiftMap h D hFull hAd a).val.2 ∘ Fin.castAdd 1 = a.val.2 := by
  let T := canonicalFocusSpecial A D
  have hf := canonicalFocusRelabelMap_formula h D hFull hAd (T.toMap a)
  have hlabels := congrArg Prod.snd hf
  funext k
  have hk := congrFun hlabels (Fin.castAdd 1 k)
  simp only [mapRVLabels_value,focusRelabelProgram_value] at hk
  change (canonicalFocusLiftMap h D hFull hAd a).val.2 (Fin.castAdd 1 k) = _ at hk
  have hOld := special_oldLabels T a k
  have hIndex : suffixIndex (special_chain_rvArity_le T.chain) k =
      Fin.natAdd n (Fin.natAdd n k) := by
    apply Fin.ext
    change (n+(n+(@RVObject.arity M (@CanonicalStructure.normalize M sM) _ n U)))-(@RVObject.arity M (@CanonicalStructure.normalize M sM) _ n U)+k.val = n+(n+k.val)
    omega
  rw [hIndex] at hOld
  exact hk.trans ((Fin.append_left _ _ k).trans hOld)

theorem canonical_focus_lift_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {U : @RVObject M (@CanonicalStructure.normalize M sM) (C.base : Set M) n}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n (@RVObject.arity M (@CanonicalStructure.normalize M sM) _ n U)}
    (h : @Section6.PresentsLift M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) n U (normalizedPointSet A))
    {i : Fin n} {j : Fin (n+(@RVObject.arity M (@CanonicalStructure.normalize M sM) _ n U))} (D : Focus (canonicalImage A) i j)
    (hFull : carrier (canonicalImage A) ⊆ D.locus)
    (hAd : @Section6.Admissible M (@CanonicalStructure.normalize M sM) (C.base : Set M) n U i) :
    VFAlmostEverywhere (rawSpecialSet hc A)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc (canonicalFocusLiftMap h D hFull hAd)) p 1) := by
  let T := canonicalFocusSpecial A D
  let f := rawSpecialMap hc T.toMap
  let g := rawSpecialMap hc (canonicalFocusRelabelMap h D hFull hAd)
  have hf := (special_vf_jacobian_one hc C hn T).1
  have hg := vfJacobianOne_of_preservesVF hc C hn g (fun _ => rfl)
  exact vfJacobianOne_comp hc C hn f g T.bijective.1 hf hg

theorem canonical_focus_lift_preserves_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {U : @RVObject M (@CanonicalStructure.normalize M sM) (C.base : Set M) n}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n (@RVObject.arity M (@CanonicalStructure.normalize M sM) _ n U)}
    (h : @Section6.PresentsLift M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) n U (normalizedPointSet A))
    {i : Fin n} {j : Fin (n+(@RVObject.arity M (@CanonicalStructure.normalize M sM) _ n U))} (D : Focus (canonicalImage A) i j)
    (hFull : carrier (canonicalImage A) ⊆ D.locus)
    (hAd : @Section6.Admissible M (@CanonicalStructure.normalize M sM) (C.base : Set M) n U i)
    (ω : VolumeForm (rawSpecialSet hc A))
    (π : VolumeForm (rawSpecialSet hc (typedLift (@Section6.elementary M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) n U i))))
    (hDensity : ∀ (a : A) (b : typedLift (@Section6.elementary M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) n U i)),
      b.val.2 ∘ Fin.castAdd 1 = a.val.2 → ω.value a = π.value b) :
    PreservesVFVolume ω π (rawSpecialMap hc (canonicalFocusLiftMap h D hFull hAd)) :=
  (canonical_focus_lift_jacobian_one hc C hn h D hFull hAd).mono (fun p hJ =>
    ⟨1,hJ,by
      rw [RVOperations.rv_one,mul_one]
      exact hDensity p _ (canonical_focus_lift_original_labels h D hFull hAd p)⟩)

end IntegrationInACVF.Section7
