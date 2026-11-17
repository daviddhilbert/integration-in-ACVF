module

public import Integration7.BalancedUnaryVolumePreparationWithoutField
public import Integration7.TwoOrderProductPreparations
public import Integration7.BalancedUnaryVolumePreparation

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The two translated products of a balanced cell have constructed
opposite-order standard contractions whose actual raw RV volume objects
are original-Gamma volume-isomorphic. The compatible unary preparations
and all comparisons are constructed from checked Lemma5.2. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem balanced_product_standard_volume_comparison_without_field {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (hPS : P.real ⊆ S) (hc : CanonicalStructure.IsCanonical (M := M))
    {R : Set (VF (M := M) × VF (M := M))} {ε : VF (M := M) → VF (M := M)}
    {r t : RV (M := M)} (h : IsBalanced R ε r t) (hr : r ≠ rv (0 : VF (M := M)))
    (hrS : r.val ∈ S) (htS : t.val ∈ S) (hr0 : r.val ≠ iRVZero) (ht0 : t.val ≠ iRVZero)
    (D E : DefSet (M := M) S 1 0) (f : Map D E) (hf : Function.Bijective f)
    (hDΓ : GammaSetDefinable P (carrier D)) (hEΓ : GammaSetDefinable P (carrier E))
    (hfΓ : GammaGraphDefinable P (pointMapGraph f))
    (hDomain : ∀ p : D, vfAt p.val 0 ∈ first R)
    (hValue : ∀ p : D, vfAt (f p).val 0 = ε (vfAt p.val 0))
    (X Y : DefSet (M := M) S 2 0)
    (hXΓ : GammaSetDefinable P (carrier X)) (hYΓ : GammaSetDefinable P (carrier Y))
    (hX : ∀ p : Point (M := M) 2 0, p ∈ carrier X ↔
      rv (vfAt p 0) = r ∧ ((fun _ : Fin 1 => vfAt p 1),Fin.elim0) ∈ carrier E)
    (hY : ∀ p : Point (M := M) 2 0, p ∈ carrier (vfPermutationImage Y (Equiv.swap 0 1)) ↔
      rv (vfAt p 0) = t ∧ ((fun _ : Fin 1 => vfAt p 1),Fin.elim0) ∈ carrier D)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S)
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    ∃ F : TwoOrderProductPreparations X Y D E r t z hz P,
    ∃ i : RVVolumeIso (F.headVolumeObject hκ.le hs hsmall hc hrS η hη hη0)
      (F.tailVolumeObject hκ.le hs hsmall hc htS η hη hη0), i.GammaDefinable P := by
  obtain ⟨S',hSS',u,v,D',E',TA,TB,hTA,hTB,hD',hE',iBal,hiBal⟩ :=
    balanced_unary_volume_preparation_without_field hκ hs hsmall h00 γ hγ hγ1 hPS hc h hr
      hrS htS hr0 ht0 η hη hη0 D E f hf hDΓ hEΓ hfΓ hDomain hValue
  have hX' : ∀ p : Point (M := M) 2 0, p ∈ carrier (extendBase X hSS') ↔
      rv (vfAt p 0) = r ∧ ((fun _ : Fin 1 => vfAt p 1),Fin.elim0) ∈ carrier (extendBase E hSS') := hX
  have hY' : ∀ p : Point (M := M) 2 0,
      p ∈ carrier (vfPermutationImage (extendBase Y hSS') (Equiv.swap 0 1)) ↔
      rv (vfAt p 0) = t ∧ ((fun _ : Fin 1 => vfAt p 1),Fin.elim0) ∈ carrier (extendBase D hSS') := hY
  obtain ⟨LX⟩ := gamma_rv_class_product_tail_preparation_exists (extendBase X hSS') (extendBase E hSS') E'
    TB hTB hE' hXΓ r hX' z (fun j => hSS' (hz j)) hzΓ
  obtain ⟨LY⟩ := gamma_rv_class_product_tail_preparation_exists
    (vfPermutationImage (extendBase Y hSS') (Equiv.swap 0 1)) (extendBase D hSS') D'
    TA hTA hD' (gamma_vfPermutationImage (extendBase Y hSS') hYΓ (Equiv.swap 0 1))
    t hY' z (fun j => hSS' (hz j)) hzΓ
  let F : TwoOrderProductPreparations X Y D E r t z hz P := {
    codes := S', contains := hSS', dArity := u, eArity := v, dTarget := D', eTarget := E'
    dSpecial := TA, eSpecial := TB, dGamma := hTA, eGamma := hTB, dPullback := hD', ePullback := hE'
    headSaturated := head_saturated_rv_class_product _ _ r hX'
    tailSaturated := head_saturated_rv_class_product _ _ t hY'
    headPreparation := LX, tailPreparation := LY }
  obtain ⟨eX,heX⟩ := rv_class_product_original_unary_volume_comparison hκ.le hs hsmall hc (hPS.trans hSS')
    (extendBase X hSS') (extendBase E hSS') E' TB hTB hE' F.headSaturated r (hSS' hrS) hr0
    z (fun j => hSS' (hz j)) LX η (hSS' hη) hη0
  obtain ⟨eY,heY⟩ := swapped_rv_class_product_original_unary_volume_comparison hκ.le hs hsmall hc (hPS.trans hSS')
    (extendBase Y hSS') (extendBase D hSS') D' TA hTA hD' F.tailSaturated t (hSS' htS) ht0
    z (fun j => hSS' (hz j)) LY η (hSS' hη) hη0
  let hDF := gamma_special_pullback_finite_volume hκ.le hs hsmall TA hTA hD' (fun _ => Set.toFinite _)
  let hEF := gamma_special_pullback_finite_volume hκ.le hs hsmall TB hTB hE' (fun _ => Set.toFinite _)
  let U := rvFiniteEssential (canonicalFiniteRVObject hc ⟨pullbackObject D',hDF⟩)
  let V := rvFiniteEssential (canonicalFiniteRVObject hc ⟨pullbackObject E',hEF⟩)
  let VH := (prependFixedRVVolume V r (hSS' hrS) (VolumeForm.one _)).rescale η (hSS' hη) hη0
  let UT := (appendFixedRVVolume U t (hSS' htS) (VolumeForm.one _)).rescale η (hSS' hη) hη0
  have hdV : rvDim VH.essential.obj.domain < 2 :=
    lt_of_le_of_lt (constant_head_volume_dimension_le_one VH.essential r (fun _ => rfl)) (by decide)
  have hdU : rvDim UT.essential.obj.domain < 2 :=
    lt_of_le_of_lt (constant_tail_volume_dimension_le_one UT.essential t (fun _ => rfl)) (by decide)
  have hdX : rvDim (F.headVolumeObject hκ.le hs hsmall hc hrS η hη hη0).essential.obj.domain < 2 :=
    (rvDim_eq_of_bijective (finiteIsoMap eX.iso) (finiteIsoMap_bijective eX.iso)).trans_lt hdV
  exact ⟨F,(eX.transOfSmallDimension iBal hdX).transOfSmallDimension (eY.symmOfSmallDimension hdU) hdX,
    (heX.transOfSmallDimension hiBal hdX).transOfSmallDimension (heY.symmOfSmallDimension hdU) hdX⟩

end IntegrationInACVF.Section7
