import IntegrationSection6.GammaGraphCoproducts

/-! Native coproduct volume values at either tagged label, independent of
internal code unions and the choice of graph presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b k : ℕ}
variable {D : Set (Fin a → RV (M := M))} {E : Set (Fin b → RV (M := M))}
variable {R : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}
variable {T : (Fin b → RV (M := M)) → (Fin k → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaFiniteGraphPresentation.coprod_value_at_left (P : GammaFiniteGraphPresentation B a k D R)
    (Q : GammaFiniteGraphPresentation B b k E T) (x : P.domain) (y : (P.coprod Q).domain)
    (hy : y.val = @rvLeftTag M N hN a b x.val) :
    ((P.coprod Q).volume y).val = (P.volume x).val := by
  have hx := (P.graph_iff x.val (P.volume x).val).mp ⟨x,rfl,rfl⟩
  obtain ⟨y',hy',hv⟩ := ((P.coprod Q).graph_iff (@rvLeftTag M N hN a b x.val) (P.volume x).val).mpr
    ⟨Or.inl ⟨x.val,hx.1,rfl⟩,Or.inl ⟨x.val,hx.1,rfl,hx.2⟩⟩
  have he : y' = y := Subtype.ext (hy'.trans hy.symm)
  exact he ▸ hv

theorem GammaFiniteGraphPresentation.coprod_value_at_right (P : GammaFiniteGraphPresentation B a k D R)
    (Q : GammaFiniteGraphPresentation B b k E T) (x : Q.domain) (y : (P.coprod Q).domain)
    (hy : y.val = @rvRightTag M N hN b a x.val) :
    ((P.coprod Q).volume y).val = (Q.volume x).val := by
  have hx := (Q.graph_iff x.val (Q.volume x).val).mp ⟨x,rfl,rfl⟩
  obtain ⟨y',hy',hv⟩ := ((P.coprod Q).graph_iff (@rvRightTag M N hN b a x.val) (Q.volume x).val).mpr
    ⟨Or.inr ⟨x.val,hx.1,rfl⟩,Or.inr ⟨x.val,hx.1,rfl,hx.2⟩⟩
  have he : y' = y := Subtype.ext (hy'.trans hy.symm)
  exact he ▸ hv

end IntegrationInACVF.Section6
