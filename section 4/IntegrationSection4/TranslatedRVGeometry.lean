import IntegrationSection4.BalancedSlope
import IntegrationSection4.LinearBallRadius
import IntegrationSection3ACVF.RVInputFibre

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Milestone0.sortEval

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.TranslatedRVGeometry

open BalancedFibres Cells GammaRadiusAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem value_ne_infinity (t : RV (M := M)) (ht : t ≠ rv (0 : VF (M := M))) :
    Values.vrv t ≠ Values.infinity := by
  intro he
  have hz := (Values.vrv_eq_infinity_iff t).mp he
  apply ht
  exact Subtype.ext (hz.trans ((CanonicalRV.encodedRv_zero_iff (0 : VFType (M := M))).mpr rfl).symm)

/-- Every translated nonzero RV fibre is an ordinary open ball with the
paradigm's value as radius, centred at any one of its points. -/
theorem ordinary_ball (t : RV (M := M)) (ht : t ≠ rv (0 : VF (M := M)))
    (c x : VF (M := M)) (hx : x ∈ translatedRV t c) :
    rawSet (translatedRV t c) = gammaBall x ⟨Values.vrv t,value_ne_infinity t ht⟩ true := by
  have hxc : x-c ≠ 0 := by
    intro h
    apply ht
    change rv (x-c) = t at hx
    exact hx.symm.trans (congrArg rv h)
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  have hval : Values.vfValueHom (x-c) = Values.vrv t := congrArg Values.vrv hx
  ext z
  constructor
  · rintro ⟨y,hy,rfl⟩
    let Y : VF (M := M) := ⟨y.val,y.property⟩
    have hy' : rv (Y-c) = t := hy
    have he : iRv (Y-c).val = iRv (x-c).val := congrArg Subtype.val (hy'.trans hx.symm)
    have hc := (CanonicalRV.encoded_eq_iff_close (Y-c).property (x-c).property
      (fun h => hxc (Subtype.ext h))).mp he
    apply (GammaCosetGeometry.gammaBall_mem_valuation v hv x (x-c) _ hval Y).mpr
    have hh : ¬ v (x-c) ≤ v ((Y-c)-(x-c)) := fun h => hc ((hv _ _).mpr h)
    simpa only [sub_sub_sub_cancel_right,not_le] using hh
  · intro hz
    let Z : VF (M := M) := ⟨z,hz.1⟩
    have hclose := (GammaCosetGeometry.gammaBall_mem_valuation v hv x (x-c) _ hval Z).mp hz
    have he : iRv (Z-c).val = iRv (x-c).val := by
      apply (CanonicalRV.encoded_eq_iff_close (Z-c).property (x-c).property
        (fun h => hxc (Subtype.ext h))).mpr
      intro h
      change VFValued.predV (x-c) ((Z-c)-(x-c)) at h
      have hh := (hv _ _).mp h
      have hs : (Z-c)-(x-c) = Z-x := by ring
      rw [hs] at hh
      exact not_le_of_gt hclose hh
    exact ⟨Z,(Subtype.ext he).trans hx,rfl⟩

theorem subset_open {A : Set M} (ho : PaperBalls.IsOpenBall A)
    (t : RV (M := M)) (c x : VF (M := M)) (hc : c.val ∈ A) (hx : x.val ∈ A)
    (ht : x ∈ translatedRV t c) : rawSet (translatedRV t c) ⊆ A := by
  rintro _ ⟨y,hy,rfl⟩
  let Y : VF (M := M) := ⟨y.val,y.property⟩
  have hy' : rv (Y-c) = t := hy
  have he : Values.vfValueHom (Y-c) = Values.vfValueHom (x-c) :=
    congrArg Values.vrv (hy'.trans ht.symm)
  have hh := RVInputFibre.translate_mem_of_value ho c x (Y-c) hc hx he
  have hs : c+(Y-c) = Y := by ring
  rwa [hs] at hh

theorem mem_of_value_gt (c x : VF (M := M)) (β : Values.Gamma (M := M))
    (h : β.val < Values.vfValueHom (x-c)) : x.val ∈ gammaBall c β true := by
  change ∃ hx : iVF x.val, β.val ≤ Values.vfValueHom (x-c) ∧
    (true = true → ¬ Values.vfValueHom (x-c) ≤ β.val)
  exact ⟨x.property,h.le,fun _ => not_le_of_gt h⟩

/-- If the positioning image has radius below the paradigm value, its
translated RV fibres stay inside it and cover it. -/
theorem cover_ordinary (c : VF (M := M)) (β : Values.Gamma (M := M)) (t : RV (M := M))
    (hβt : β.val < Values.vrv t) :
    (∀ a : VF (M := M), a.val ∈ gammaBall c β true →
      rawSet (translatedRV t a) ⊆ gammaBall c β true) ∧
    (∀ z : VF (M := M), z.val ∈ gammaBall c β true →
      ∃ a : VF (M := M), a.val ∈ gammaBall c β true ∧ z ∈ translatedRV t a) := by
  constructor
  · intro a ha
    rintro _ ⟨z,hz,rfl⟩
    let Z : VF (M := M) := ⟨z.val,z.property⟩
    have he : Values.vfValueHom (Z-a) = Values.vrv t := congrArg Values.vrv (show rv (Z-a) = t from hz)
    have hm := mem_of_value_gt a Z β (he.symm ▸ hβt)
    exact RadiusPreparationGeometry.recentre c a β ha ▸ hm
  · intro z hz
    obtain ⟨u,hu⟩ := CanonicalRV.encodedRv_surjective t
    let a := z-u
    have hValue : Values.vfValueHom (a-z) = Values.vrv t := by
      have hs : a-z = -u := by dsimp [a]; ring
      rw [hs]
      have he := BalancedSlope.value_sub_swap (0 : VF (M := M)) u
      simp only [zero_sub,sub_zero] at he
      exact he.trans (congrArg Values.vrv hu)
    have ha := mem_of_value_gt z a β (hValue.symm ▸ hβt)
    refine ⟨a,RadiusPreparationGeometry.recentre c z β hz ▸ ha,?_⟩
    change rv (z-a) = t
    have he : z-a = u := by dsimp [a]; ring
    rw [he]
    exact Subtype.ext (congrArg Subtype.val hu)

end IntegrationInACVF.Section4.TranslatedRVGeometry
