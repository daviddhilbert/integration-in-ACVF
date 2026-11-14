import Integration7.GammaLinearOpenBallRadii
import IntegrationSection5.UnaryBijectionPreparation
import IntegrationSection5.ChainAlgebra
import IntegrationSection5.UnaryPaperBallBridge

/-! Mutually contractible prepared unary bijections match the actual
inverse-special fibres. Those fibres are the balls whose radii are the
values of the prepared VF coordinates, with their original RV labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5 IntegrationInACVF.Section5
open IntegrationInACVF.Section3ACVF IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l r s : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {A' : DefSet (M := M) S 1 r} {B' : DefSet (M := M) S 1 s}

theorem unary_conjugate_inverse_fibre_image
    (TA : SpecialBijection A A') (TB : SpecialBijection B B')
    (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible (unaryConjugate TA TB f))
    (hback : Contractible (Map.inverse (unaryConjugate TA TB f) (unaryConjugate_bijective TA TB f hf)))
    (a : A') :
    unaryImage f (TA.inverseFibre a) = TB.inverseFibre (unaryConjugate TA TB f a) := by
  let g := unaryConjugate TA TB f
  have hg (x : A) : g (TA.toMap x) = TB.toMap (f x) := by
    change TB.toMap (f (TA.inverseMap (TA.toMap x))) = _
    rw [TA.inverse_apply]
  ext q
  constructor
  · rintro ⟨x,⟨y,hy,hya⟩,rfl⟩
    have hyx : y = x := Subtype.ext hy
    subst y
    refine ⟨f x,rfl,?_⟩
    rw [← hg x]
    exact hc (TA.toMap x) a hya
  · rintro ⟨y,rfl,hya⟩
    let x := Map.inverse f hf y
    have hfx : f x = y := Map.apply_inverse f hf y
    have hgx : g (TA.toMap x) = TB.toMap y := (hg x).trans (congrArg TB.toMap hfx)
    have ha := hback (g (TA.toMap x)) (g a) (by rw [hgx];exact hya)
    rw [Map.inverse_apply,Map.inverse_apply] at ha
    exact ⟨x,⟨x,rfl,ha⟩,congrArg Subtype.val hfx⟩

theorem unary_inverse_fibre_insert_iff
    (T : SpecialBijection A A') (hA' : IsRVPullback (carrier A'))
    (a : A') (ha : vfAt a.val 0 ≠ 0) (α : Values.Gamma (M := M))
    (hα : Values.vfValueHom (vfAt a.val 0) = α.val) (x : VFType (M := M)) :
    unaryInsert (T.inverseMap a).val.2 x ∈ T.inverseFibre a ↔
      x.val ∈ gammaBall (vfAt (T.inverseMap a).val 0) α true := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have he := (T.unary_inverse_fibre v hv hA' a ha).1
  rw [he]
  change (v (x-vfAt (T.inverseMap a).val 0) < v (vfAt a.val 0) ∧ _) ↔ _
  have hBall := GammaCosetGeometry.gammaBall_mem_valuation v hv
    (vfAt (T.inverseMap a).val 0) (vfAt a.val 0) α hα x
  exact ⟨fun h => hBall.mpr h.1,fun h => ⟨hBall.mp h,rfl⟩⟩

theorem unary_inverse_fibre_labels
    (T : SpecialBijection A A') (a : A') (p : Point (M := M) 1 m)
    (hp : p ∈ T.inverseFibre a) : p.2 = (T.inverseMap a).val.2 := by
  obtain ⟨x,rfl,hx⟩ := hp
  apply T.chain.labels_eq_of x (T.inverseMap a)
  change (T.toMap x).val.2 = (T.toMap (T.inverseMap a)).val.2
  rw [T.apply_inverse]
  exact ((sameRV_iff _ _).mp hx).2

end IntegrationInACVF.Section7
