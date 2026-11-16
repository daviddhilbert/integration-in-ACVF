module

public import Integration7.RectangleFamilyPullbackPreparations
public import Integration7.RelativeHeadSpecialJacobians
public import Integration7.PermutedPullbackGeometry
public import Integration7.PermutationJacobianOneTransport
public import Integration7.MixedJacobianOneOperations

@[expose] public section

/-! Restoring the original VF order after the two rectangle-family
preparations gives an actual Jacobian-one bijection to a full RV
pullback. Both coordinate permutations are retained in the proof. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}

namespace RectangleFamilyPullbackPreparation
variable {H : DefSet (M := M) S 2 m}

def volumeTarget (F : RectangleFamilyPullbackPreparation G H) : DefSet (M := M) S 2 F.tail.arity :=
  vfPermutationImage F.tail.target (Equiv.swap 0 1)

def volumeMap (F : RectangleFamilyPullbackPreparation G H) : Map H F.volumeTarget :=
  Map.comp (vfPermutationBijection F.tail.target (Equiv.swap 0 1)) F.toMap

theorem volume_map_bijective (F : RectangleFamilyPullbackPreparation G H) :
    Function.Bijective F.volumeMap :=
  (vfPermutationBijection_bijective _ _).comp F.bijective

theorem volume_target_pullback (F : RectangleFamilyPullbackPreparation G H) :
    IsRVPullback (carrier F.volumeTarget) := vf_permutation_image_pullback _ F.pullback _

theorem volume_target_gamma (F : RectangleFamilyPullbackPreparation G H) :
    GammaSetDefinable G (carrier F.volumeTarget) := gamma_vfPermutationImage _ F.tail_target _

theorem volume_graph_gamma (F : RectangleFamilyPullbackPreparation G H) :
    GammaGraphDefinable G (pointMapGraph F.volumeMap) :=
  gamma_composition_graph _ _ F.graph_gamma (gamma_vfPermutation_graph _ F.tail_target _)

def volumeLabelIndex (F : RectangleFamilyPullbackPreparation G H) : Fin m → Fin F.tail.arity :=
  suffixIndex (specialRelative_rvArity_le F.tail.special) ∘
    suffixIndex (specialRelative_rvArity_le F.head.special)

theorem volume_old_labels (F : RectangleFamilyPullbackPreparation G H) (p : H) (i : Fin m) :
    (F.volumeMap p).val.2 (F.volumeLabelIndex i) = p.val.2 i :=
  (specialRelative_oldLabels F.tail.special
    (vfPermutationBijection F.head.target (Equiv.swap 0 1) (F.head.map p)) _).trans
      (specialRelative_oldLabels F.head.special p i)

set_option maxHeartbeats 2000000 in
theorem volume_jacobian_one (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {H : DefSet (M := M) (C.base : Set M) 2 m} (F : RectangleFamilyPullbackPreparation G H) :
    VFAlmostEverywhere (rawSpecialSet hc H)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc F.volumeMap) p 1) := by
  let σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  let r := doubleVFPermutationMap F.head.target σ
  let q := (rawSpecialMap hc r).comp (rawSpecialMap hc F.head.map)
  have hr := vfJacobianOne_of_preservesVF hc C (by decide : 0 < 2) (rawSpecialMap hc r)
    (fun p => congrArg Prod.fst (double_vf_permutation_value F.head.target σ p))
  have hq := vfJacobianOne_comp hc C (by decide : 0 < 2)
    (rawSpecialMap hc F.head.map) (rawSpecialMap hc r) F.head.bijective.1
    (relative_head_special_vf_jacobian_one hc C F.head.map F.head.special) hr
  have hTail := vf_jacobian_one_conjugate_permutation hc F.tail.map σ
    (relative_head_special_vf_jacobian_one hc C F.tail.map F.tail.special)
  have hcomp := vfJacobianOne_comp hc C (by decide : 0 < 2) q
    (rawSpecialMap hc (vfPermutedMap F.tail.map σ))
    ((double_vf_permutation_bijective F.head.target σ).1.comp F.head.bijective.1) hq hTail
  apply vfJacobianOne_of_same_vf hc C (by decide : 0 < 2)
    ((rawSpecialMap hc (vfPermutedMap F.tail.map σ)).comp q) (rawSpecialMap hc F.volumeMap) _ hcomp
  intro p
  change (vfPermutationBijection F.tail.target σ
    (F.tail.map (Map.inverse (vfPermutationBijection _ σ) (vfPermutationBijection_bijective _ σ)
      (vfPermutationBijection _ σ (vfPermutationBijection F.head.target σ (F.head.map p)))))).val.1 = _
  rw [Map.inverse_apply]
  rfl

theorem volume_inverse_jacobian_one (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {H : DefSet (M := M) (C.base : Set M) 2 m} (F : RectangleFamilyPullbackPreparation G H) :
    VFAlmostEverywhere (rawSpecialSet hc F.volumeTarget)
      (fun p => HasMixedVFJacobianAt
        (rawSpecialMap hc (Map.inverse F.volumeMap F.volume_map_bijective)) p 1) :=
  vfJacobianOne_inverse hc C (by decide : 0 < 2) (rawSpecialMap hc F.volumeMap)
    F.volume_map_bijective (F.volume_jacobian_one hc C)

theorem volume_preserves (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {H : DefSet (M := M) (C.base : Set M) 2 m} (F : RectangleFamilyPullbackPreparation G H)
    (ω : VolumeForm (rawSpecialSet hc H)) (π : VolumeForm (rawSpecialSet hc F.volumeTarget))
    (hDensity : ∀ p, ω.value p = π.value (rawSpecialMap hc F.volumeMap p)) :
    PreservesVFVolume ω π (rawSpecialMap hc F.volumeMap) :=
  (F.volume_jacobian_one hc C).mono
    (fun p hJ => ⟨1,hJ,by rw [RVOperations.rv_one,mul_one]; exact hDensity p⟩)

end RectangleFamilyPullbackPreparation
end IntegrationInACVF.Section7
