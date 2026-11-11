import IntegrationSection3ACVF.RVDifferencePairs
import IntegrationSection3ACVF.RVInverse
import IntegrationSection3ACVF.RVFibreSubballs
import IntegrationSection4.RadiusPreparationGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.InverseDifferenceGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem reverse_difference (a x y : VFType (M := M))
    (h : iRv (x-a).val = iRv (y-a).val) : iRv (a-x).val = iRv (a-y).val := by
  have he := congrArg (fun t => iRVMul (iRv (-1 : VFType (M := M)).val) t) h
  rw [← rv_mul_hom_of_model hM (-1 : VFType (M := M)).property (x-a).property,
    ← rv_mul_hom_of_model hM (-1 : VFType (M := M)).property (y-a).property] at he
  change iRv ((-1)*(x-a) : VFType (M := M)).val = iRv ((-1)*(y-a) : VFType (M := M)).val at he
  simpa only [neg_one_mul,neg_sub] using he

/-- The inverse image of a translated nonzero RV class is an open ball
missing the distinguished point. Hence the inverse differences agree in RV. -/
theorem inverse_differences (A B : Set M) (hAVF : A ⊆ {x | iVF x})
    (hBVF : B ⊆ {x | iVF x}) (hB : PaperBalls.IsOpenBall B)
    (f : M → M) (hbij : Set.BijOn f A B) (hoo : MaximalOpenClasses.OpenToOpen A f)
    (a b c : VFType (M := M)) (ha : a.val ∈ A) (hb : b.val ∈ B) (hc : c.val ∈ B)
    (he : RVDifferencePairs.difference b.val (f a.val) =
      RVDifferencePairs.difference c.val (f a.val)) :
    RVDifferencePairs.difference a.val (RVInverse.inverse A f b.val) =
      RVDifferencePairs.difference a.val (RVInverse.inverse A f c.val) := by
  have himage : f '' A = B := hbij.image_eq
  have hbI : b.val ∈ f '' A := himage.symm ▸ hb
  have hcI : c.val ∈ f '' A := himage.symm ▸ hc
  have hbInv := RVInverse.inverse_right hbI
  have hcInv := RVInverse.inverse_right hcI
  let x : VFType (M := M) := ⟨RVInverse.inverse A f b.val,hAVF hbInv.1⟩
  let y : VFType (M := M) := ⟨RVInverse.inverse A f c.val,hAVF hcInv.1⟩
  let fa : VFType (M := M) := ⟨f a.val,hBVF (hbij.1 ha)⟩
  rw [RVDifferencePairs.difference_vf b fa,RVDifferencePairs.difference_vf c fa] at he
  by_cases hbf : b = fa
  · have hcf : c = fa := by
      have hz : iRv (c-fa).val = iRVZero := he.symm.trans ((CanonicalRV.encodedRv_zero_iff (b-fa)).mpr (sub_eq_zero.mpr hbf))
      exact sub_eq_zero.mp ((CanonicalRV.encodedRv_zero_iff (c-fa)).mp hz)
    have hbc : b = c := hbf.trans hcf.symm
    rw [hbc]
  · have hBall : IsBall B := by
      rcases hB with h | ⟨d,γ,h⟩
      · exact Or.inl h
      · exact h.symm ▸ BallEnlargementGeometry.gammaBall_isBall d γ true
    obtain ⟨i,hio,hiB,hbi,hci,hfai⟩ := RVFibreSubballs.exists_subball hBall fa b c (hbij.1 ha) hb hbf he.symm
    let Q := BallImaginaries.underlying i
    let P := {z | z ∈ A ∧ f z ∈ Q}
    have hPA : P ⊆ A := fun _ hz => hz.1
    have hPQ : f '' P = Q := by
      ext z
      constructor
      · rintro ⟨u,hu,rfl⟩
        exact hu.2
      · intro hz
        obtain ⟨u,hu,rfl⟩ := hbij.2.2 (hiB hz)
        exact ⟨u,⟨hu,hz⟩,rfl⟩
    have hPo : PaperBalls.IsOpenBall P := (hoo P hPA).mpr (hPQ.symm ▸ hio)
    have haP : a.val ∉ P := fun h => hfai h.2
    have hxP : x.val ∈ P := ⟨hbInv.1,hbInv.2.symm ▸ hbi⟩
    have hyP : y.val ∈ P := ⟨hcInv.1,hcInv.2.symm ▸ hci⟩
    have hh := reverse_difference a x y (OpenBallRVGeometry.rv_sub_constant hPo a x y haP hxP hyP)
    rw [RVDifferencePairs.difference_vf a x,RVDifferencePairs.difference_vf a y]
    exact hh

end IntegrationInACVF.Section4.InverseDifferenceGeometry
