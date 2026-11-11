import IntegrationSection4.GammaUnarySyntax
import IntegrationSection4.ConstantRowsLinearity
import IntegrationSection4.InverseBodies
import IntegrationSection4.FiniteRelationPreparation

/-! The geometric assembly in Lemma 4.2: a prepared radius/slope relation
gives Gamma-linearity on every actual inverse RV-polydisc, including points. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.PreparedLinearity

open GammaRadiusAtomicity GammaLinearRestrictions

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {l : ℕ}
variable {D : DefSet (M := M) S 1 0} {E : DefSet (M := M) S 1 l}

theorem code_row_iff (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (r s : M) (hr : NonzeroRV r) (hs : NonzeroRV s) (p : Point (M := M) 1 0) :
    GammaUnarySyntax.linearRow A f p (Fin.elim0,![⟨r,hr.1⟩,⟨s,hs.1⟩]) ↔
      SlopeAt A f hfVF (vfAt p 0) (codeValue r) (codeValue s) := by
  change (NonzeroRV r ∧ NonzeroRV s ∧
    GammaLinearBallRow.row A f ![r,s,(vfAt p 0).val]) ↔ _
  exact ⟨fun h => (GammaLinearBallRow.row_iff A f hfVF r s hr hs _).mp h.2.2,
    fun h => ⟨hr,hs,(GammaLinearBallRow.row_iff A f hfVF r s hr hs _).mpr h⟩⟩

theorem rows_on_body (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (T : SpecialBijection D E)
    (hUniform : FiniteRelationPreparation.Uniform (GammaUnarySyntax.linearRow A f) T)
    (b : E) (x y : VF (M := M)) (hx : x.val ∈ InverseBodies.body T b)
    (hy : y.val ∈ InverseBodies.body T b) (β s : Values.Gamma (M := M)) :
    SlopeAt A f hfVF x β s ↔ SlopeAt A f hfVF y β s := by
  obtain ⟨r,hr,hrβ⟩ := EndpointLogic.codeValue_surjective β
  obtain ⟨u,hu,hus⟩ := EndpointLogic.codeValue_surjective s
  obtain ⟨a,ha,haKey⟩ := hx
  obtain ⟨c,hc,hcKey⟩ := hy
  let q : Point (M := M) 0 2 := (Fin.elim0,![⟨r,hr.1⟩,⟨u,hu.1⟩])
  have hh := hUniform (T.toMap a) (T.toMap c) (haKey.trans hcKey.symm) q
  rw [T.inverse_apply,T.inverse_apply] at hh
  have hax : vfAt a.val 0 = x := Subtype.ext ha
  have hcy : vfAt c.val 0 = y := Subtype.ext hc
  have hA := code_row_iff A f hfVF r u hr hu a.val
  have hC := code_row_iff A f hfVF r u hr hu c.val
  rw [hax,hrβ,hus] at hA
  rw [hcy,hrβ,hus] at hC
  exact hA.symm.trans (hh.trans hC)

theorem linear_on_body {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (A : Set M) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hInj : Set.InjOn f A)
    (T : SpecialBijection D E) (hE : IsRVPullback (carrier E))
    (hUniform : FiniteRelationPreparation.Uniform (GammaUnarySyntax.linearRow A f) T)
    (b : E) (hBA : InverseBodies.body T b ⊆ A) :
    ∃ s : Values.Gamma (M := M), GammaLinearity.GammaLinear (InverseBodies.body T b) f
      (fun x hx => hfVF x (hBA hx)) s := by
  by_cases hb : vfAt b.val 0 = 0
  · refine ⟨1,?_⟩
    intro x y hx hy
    have hx' := hx
    have hy' := hy
    rw [InverseBodies.body_zero T b hb] at hx' hy'
    have he : y = x := Subtype.ext (hy'.trans hx'.symm)
    subst y
    simp only [sub_self,map_zero,mul_zero]
  · obtain ⟨γ,_,hBody⟩ := InverseBodies.body_ordinary T hE b hb
    have hBallA : gammaBall (vfAt (T.inverseMap b).val 0) γ true ⊆ A := hBody ▸ hBA
    obtain ⟨s,hLin⟩ := ConstantRowsLinearity.on_ordinary_ball hκ hs B hsmall h00 A f hf hfVF hInj
      (vfAt (T.inverseMap b).val 0) γ hBallA (by
        intro x y hx hy β s
        exact rows_on_body A f hfVF T hUniform b x y (hBody.symm ▸ hx) (hBody.symm ▸ hy) β s)
    refine ⟨s,?_⟩
    intro x y hx hy
    exact hLin x y (hBody ▸ hx) (hBody ▸ hy)

end IntegrationInACVF.Section4.PreparedLinearity
