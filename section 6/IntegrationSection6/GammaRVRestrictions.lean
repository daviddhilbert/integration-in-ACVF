import IntegrationSection6.GammaRVGlobalRestriction

/-! Full Gamma graphs survive genuine RV source restrictions and images. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a b : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gamma_rv_graph_restrict_source
    {P A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N a) S}
    {Q C : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N b) S}
    (F : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ S P Q)
    (G : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ S A C)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S P))
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 a |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A})
    (hF : GammaGraphDefinable B (fun (p : Point (M := M) 0 a) (q : Point (M := M) 0 b) =>
      ∃ x : P, x.val = p.2 ∧ (F x).val = q.2))
    (hG : ∀ x : A, (G x).val = (F ⟨x.val,hA x.property⟩).val) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 a) (q : Point (M := M) 0 b) =>
      ∃ x : A, x.val = p.2 ∧ (G x).val = q.2) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph hΓ hF)
  intro p q
  constructor
  · rintro ⟨hp,x,hx,hq⟩
    let y : A := ⟨p.2,hp⟩
    have he : (⟨y.val,hA y.property⟩ : P) = x := Subtype.ext hx.symm
    exact ⟨y,rfl,(hG y).trans ((congrArg (fun x => (F x).val) he).trans hq)⟩
  · rintro ⟨x,hx,hq⟩
    refine ⟨?_,⟨x.val,hA x.property⟩,hx,(hG x).symm.trans hq⟩
    exact (show (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) p.2 from hx ▸ x.property)

theorem gamma_rv_map_image
    {P : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N a) S}
    {Q : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N b) S}
    (F : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ S P Q)
    (hF : GammaGraphDefinable B (fun (p : Point (M := M) 0 a) (q : Point (M := M) 0 b) =>
      ∃ x : P, x.val = p.2 ∧ (F x).val = q.2)) :
    GammaSetDefinable B {q : Point (M := M) 0 b |
      q.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S
        (@SpecialTransformations.DefinableGeometry.Map.image LRV M N _ _ S P Q F)} := by
  have h := (gammaLogicInput B).image_graph hF
  convert h using 1
  ext q
  constructor
  · rintro ⟨x,hq⟩
    exact ⟨(Fin.elim0,x.val),x,rfl,hq⟩
  · rintro ⟨p,x,hx,hq⟩
    exact ⟨x,hq⟩

end IntegrationInACVF.Section6
