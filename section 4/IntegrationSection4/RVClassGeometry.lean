import IntegrationSection4.TranslatedRVGeometry
import IntegrationSection3.FiniteClosedHull

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.RVClassGeometry

open BalancedFibres Cells GammaRadiusAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem centres_close (t : RV (M := M)) (ht : t ≠ rv (0 : VF (M := M)))
    (c d : VF (M := M))
    (hd : d.val ∈ gammaBall c ⟨Values.vrv t,TranslatedRVGeometry.value_ne_infinity t ht⟩ true) :
    translatedRV t d = translatedRV t c := by
  let γ : Values.Gamma (M := M) := ⟨Values.vrv t,TranslatedRVGeometry.value_ne_infinity t ht⟩
  have forward (a b : VF (M := M)) (hb : b.val ∈ gammaBall a γ true) :
      translatedRV t b ⊆ translatedRV t a := by
    intro y hy
    have hy' : rv (y-b) = t := hy
    have hy0 : y-b ≠ 0 := fun h => ht (hy'.symm.trans (congrArg rv h))
    have hgt := GammaDifferenceRealization.difference_gt_radius a γ a b
      (BallEnlargementGeometry.gammaBall_centre_mem a γ true) hb
    have hValue : Values.vfValueHom (y-b) = Values.vrv t := congrArg Values.vrv hy'
    have hEq : iRv (y-a).val = iRv (y-b).val := by
      apply (CanonicalRV.encoded_eq_iff_close (y-a).property (y-b).property
        (fun h => hy0 (Subtype.ext h))).mpr
      intro h
      change VFValued.predV (y-b) ((y-a)-(y-b)) at h
      have hh := (Values.vf_pred_iff_gamma_le (y-b) ((y-a)-(y-b))).mp h
      have he : (y-a)-(y-b) = b-a := by ring
      rw [he,hValue] at hh
      exact not_le_of_gt hgt hh
    have hRV : rv (y-a) = rv (y-b) := Subtype.ext (by simpa only [rv] using hEq)
    exact hRV.trans hy'
  have hc : c.val ∈ gammaBall d γ true :=
    (RadiusPreparationGeometry.recentre c d γ hd).symm ▸
      BallEnlargementGeometry.gammaBall_centre_mem c γ true
  exact Set.Subset.antisymm (forward c d hd) (forward d c hc)

/-- The closed hull of a nonzero translated RV class has the positioning
value as a centre and the paradigm value as its radius. Minimality is the
intrinsic checked valuation-hull predicate, not a selected ball code. -/
theorem closed_hull {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (t : RV (M := M)) (ht : t ≠ rv (0 : VF (M := M)))
    (c x : VF (M := M)) (hx : x ∈ translatedRV t c) :
    Values.vfValueHom (x-c) = Values.vrv t ∧
      FiniteClosedHull.IsHull v (translatedRV t c) c (x-c) := by
  have hValue : Values.vfValueHom (x-c) = Values.vrv t := congrArg Values.vrv hx
  have hr0 : x-c ≠ 0 := fun h => ht (hx.symm.trans (congrArg rv h))
  let γ : Values.Gamma (M := M) := ⟨Values.vrv t,TranslatedRVGeometry.value_ne_infinity t ht⟩
  have hOrd := TranslatedRVGeometry.ordinary_ball t ht c x hx
  have hOpen : translatedRV t c = {y : VF (M := M) | v (y-x) < v (x-c)} := by
    ext y
    constructor
    · intro hy
      have hm : y.val ∈ rawSet (translatedRV t c) := ⟨y,hy,rfl⟩
      rw [hOrd] at hm
      exact (GammaCosetGeometry.gammaBall_mem_valuation v hv x (x-c) γ hValue y).mp hm
    · intro hy
      have hm := (GammaCosetGeometry.gammaBall_mem_valuation v hv x (x-c) γ hValue y).mpr hy
      rw [← hOrd] at hm
      obtain ⟨z,hz,he⟩ := hm
      exact (Subtype.ext he : z=y) ▸ hz
  refine ⟨hValue,?_,?_⟩
  · intro y hy
    have he : Values.vfValueHom (y-c) = Values.vfValueHom (x-c) :=
      (congrArg Values.vrv hy).trans hValue.symm
    exact ((Values.vf_value_eq_iff v hv (y-c) (x-c)).mp he).le
  · intro b s hSub
    rw [hOpen] at hSub
    have hHull := FiniteClosedHull.open_hull_subset v (BallRadiusGeometry.valuation_dense v hv δ hδ)
      x (x-c) b s hr0 hSub
    exact ValuationRadius.closed_radius_le_of_subset v x b (x-c) s hHull



/-- Reversing all differences changes the RV parameter but preserves its
value. This identifies the first balanced fibre with a translated RV class. -/
theorem reverse_class (t : RV (M := M)) (a x : VF (M := M)) (hx : rv (a-x) = t) :
    {y : VF (M := M) | rv (a-y) = t} = translatedRV (rv (x-a)) a := by
  ext y
  constructor
  · intro hy
    have he := congrArg Subtype.val (hy.trans hx.symm)
    have he' := InverseDifferenceGeometry.reverse_difference (0 : VF (M := M)) (a-y) (a-x)
      (by simpa only [sub_zero,rv] using he)
    exact Subtype.ext (by simpa only [zero_sub,neg_sub,rv] using he')
  · intro hy
    have he := InverseDifferenceGeometry.reverse_difference a y x (congrArg Subtype.val hy)
    exact (Subtype.ext he).trans hx

theorem reverse_closed_hull {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (t : RV (M := M)) (ht : t ≠ rv (0 : VF (M := M)))
    (a x : VF (M := M)) (hx : rv (a-x) = t) :
    Values.vfValueHom (x-a) = Values.vrv t ∧
      FiniteClosedHull.IsHull v {y : VF (M := M) | rv (a-y) = t} a (x-a) := by
  have ht' : rv (x-a) ≠ rv (0 : VF (M := M)) := by
    intro he
    have hx' := sub_eq_zero.mp ((rv_eq_zero_iff (x-a)).mp he)
    apply ht
    rw [hx',sub_self] at hx
    exact hx.symm
  have hh := closed_hull v hv δ hδ (rv (x-a)) ht' a x rfl
  refine ⟨?_,?_⟩
  · rw [BalancedSlope.value_sub_swap x a]
    exact congrArg Values.vrv hx
  · rw [reverse_class t a x hx]
    exact hh.2



/-- Translating an entire paradigm-radius ball by the RV class gives the
same translated RV fibre as translating its centre. -/
theorem translate_ball (t : RV (M := M)) (ht : t ≠ rv (0 : VF (M := M))) (c : VF (M := M)) :
    {y : VF (M := M) | ∃ b : VF (M := M),
      b.val ∈ gammaBall c ⟨Values.vrv t,TranslatedRVGeometry.value_ne_infinity t ht⟩ true ∧
      y ∈ translatedRV t b} = translatedRV t c := by
  ext y
  constructor
  · rintro ⟨b,hb,hy⟩
    exact centres_close t ht c b hb ▸ hy
  · intro hy
    exact ⟨c,BallEnlargementGeometry.gammaBall_centre_mem c _ true,hy⟩

end IntegrationInACVF.Section4.RVClassGeometry
