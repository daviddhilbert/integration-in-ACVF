module

public import Integration7.PreparedUnaryBallFibres
public import IntegrationSection5.UnaryRVCategory

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual RV map induced by mutually contractible unary
preparations scales values by the original Gamma-linearity coefficient.
The conclusion concerns prepared coordinates, rather than differences. -/
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

private theorem unary_insert_reconstruct (p : Point (M := M) 1 m) :
    unaryInsert p.2 (vfAt p 0) = p := by
  refine Prod.ext ?_ rfl
  funext i
  exact congrArg p.1 (Subsingleton.elim _ _)

private theorem inverse_fibre_source (T : SpecialBijection A A') (a : A')
    {p : Point (M := M) 1 m} (hp : p ∈ T.inverseFibre a) : p ∈ carrier A := by
  obtain ⟨x,rfl,_⟩ := hp
  exact x.property

set_option maxHeartbeats 1600000 in
theorem prepared_unary_gamma_value_ratio
    (TA : SpecialBijection A A') (TB : SpecialBijection B B')
    (f : Map A B) (hf : Function.Bijective f)
    (hA' : IsRVPullback (carrier A')) (hB' : IsRVPullback (carrier B'))
    (hc : Contractible (unaryConjugate TA TB f))
    (hback : Contractible (Map.inverse (unaryConjugate TA TB f) (unaryConjugate_bijective TA TB f hf)))
    (c : Values.Gamma (M := M))
    (hLin : ∀ x y : A, Values.vfValueHom (vfAt (f y).val 0-vfAt (f x).val 0) =
      c.val*Values.vfValueHom (vfAt y.val 0-vfAt x.val 0))
    (a : A') (ha : vfAt a.val 0 ≠ 0) :
    Values.vfValueHom (vfAt (unaryConjugate TA TB f a).val 0) = c.val*Values.vfValueHom (vfAt a.val 0) := by
  let g := unaryConjugate TA TB f
  have hg : Function.Bijective g := unaryConjugate_bijective TA TB f hf
  have hb : vfAt (g a).val 0 ≠ 0 := fun h => ha
    ((unary_bijection_zero_iff g hg hc hback hA' hB' a).mp h)
  have haΓ : Values.vfValueHom (vfAt a.val 0) ≠ Values.infinity := by
    intro h
    exact ha ((CanonicalRV.encodedRv_zero_iff _).mp ((Values.vrv_eq_infinity_iff _).mp h))
  have hbΓ : Values.vfValueHom (vfAt (g a).val 0) ≠ Values.infinity := by
    intro h
    exact hb ((CanonicalRV.encodedRv_zero_iff _).mp ((Values.vrv_eq_infinity_iff _).mp h))
  let α : Values.Gamma (M := M) := ⟨Values.vfValueHom (vfAt a.val 0),haΓ⟩
  let β : Values.Gamma (M := M) := ⟨Values.vfValueHom (vfAt (g a).val 0),hbΓ⟩
  let ca := vfAt (TA.inverseMap a).val 0
  let cb := vfAt (TB.inverseMap (g a)).val 0
  let X := {x : VFType (M := M) | x.val ∈ gammaBall ca α true}
  let Y := {y : VFType (M := M) | y.val ∈ gammaBall cb β true}
  have hImage := unary_conjugate_inverse_fibre_image TA TB f hf hc hback a
  let lift (x : X) : A :=
    ⟨unaryInsert (TA.inverseMap a).val.2 x.val,
      inverse_fibre_source TA a ((unary_inverse_fibre_insert_iff TA hA' a ha α rfl x.val).mpr x.property)⟩
  have hLift (x : X) : (lift x).val ∈ TA.inverseFibre a :=
    (unary_inverse_fibre_insert_iff TA hA' a ha α rfl x.val).mpr x.property
  have hOut (x : X) : (f (lift x)).val ∈ TB.inverseFibre (g a) := by
    rw [← hImage]
    exact ⟨lift x,hLift x,rfl⟩
  let F : X → Y := fun x => ⟨vfAt (f (lift x)).val 0,by
    apply (unary_inverse_fibre_insert_iff TB hB' (g a) hb β rfl _).mp
    have hl := unary_inverse_fibre_labels TB (g a) _ (hOut x)
    rw [← hl,unary_insert_reconstruct]
    exact hOut x⟩
  have hF : Function.Surjective F := by
    intro y
    have hy : unaryInsert (TB.inverseMap (g a)).val.2 y.val ∈ TB.inverseFibre (g a) :=
      (unary_inverse_fibre_insert_iff TB hB' (g a) hb β rfl y.val).mpr y.property
    rw [← hImage] at hy
    obtain ⟨u,hu,he⟩ := hy
    have hl := unary_inverse_fibre_labels TA a u.val hu
    have hx : (vfAt u.val 0).val ∈ gammaBall ca α true := by
      apply (unary_inverse_fibre_insert_iff TA hA' a ha α rfl _).mp
      rw [← hl,unary_insert_reconstruct]
      exact hu
    let x : X := ⟨vfAt u.val 0,hx⟩
    have hxu : lift x = u := by
      apply Subtype.ext
      change unaryInsert (TA.inverseMap a).val.2 (vfAt u.val 0) = u.val
      rw [← hl,unary_insert_reconstruct]
    refine ⟨x,Subtype.ext ?_⟩
    change vfAt (f (lift x)).val 0 = y.val
    rw [hxu,he]
    rfl
  have hR := gamma_linear_open_ball_radii ca cb α β c F hF (by
    intro x y
    exact hLin (lift x) (lift y))
  exact congrArg Subtype.val hR

end IntegrationInACVF.Section7
