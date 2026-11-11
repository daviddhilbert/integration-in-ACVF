import IntegrationSection3ACVF.FiniteFibresFromExchange
import IntegrationSection3ACVF.OpenImages

/-! A real-parameter definable VF function, restricted to an atomic open
ball, is constant or has finite fibres. The atomic base may contain actual
ball and Gamma names. Genuine saturation is used for fibre finiteness. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.AtomicFunctionFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem no_algebraic_point (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (x : VFType (M := M)) (hx : x.val ∈ A) : ¬ AlgebraicAt B.real .vf x.val := by
  rintro ⟨W,hW,hFin,hxW⟩
  have hDef : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ W} :=
    FullBaseAtomicity.OverBase.of_real (((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp hW).1)
  rcases hA.2 W hDef with hsub | hdis
  · exact (SeparationFunctions.open_infinite h00 δ hδ1 ho) (hFin.subset hsub)
  · exact Set.disjoint_left.mp hdis hx hxW

theorem constant_or_finite_fibres {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : FullBaseAtomicity.Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A D : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (hsub : A ⊆ D) (f : M → M)
    (hf : @Set.Definable M B.real LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      (ImaginaryBaseImages.graphOn D f))
    (hfVF : ∀ x ∈ A, iVF (f x)) :
    (∃ c : M, ∀ x ∈ A, f x = c) ∨ ∀ y : M, {x : M | x ∈ A ∧ f x = y}.Finite := by
  have hReal : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn D f) :=
    FullBaseAtomicity.OverBase.of_real hf
  have hm := FullBaseAtomicity.OverBase.preimage_comp hA.1 (fun _ : Fin 1 => (0 : Fin 2))
  have hGraph : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f) := by
    apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hm hReal)
    intro z
    change (z 0 ∈ A ∧ z 0 ∈ D ∧ z 1 = f (z 0)) ↔ (z 0 ∈ A ∧ z 1 = f (z 0))
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hsub h.1,h.2⟩⟩
  rcases OpenImages.lemma_3_13 B h00 δ hδ hδ1 ho hA f hGraph hfVF with hc | hIm
  · obtain ⟨c,hc⟩ := hc
    exact Or.inl ⟨c.val,hc⟩
  · apply Or.inr
    apply FiniteFibresFromExchange.finite_fibres hκ hs B hsmall
      (fun x hx => by
        rcases ho with he | ⟨a,α,he⟩
        · exact he ▸ hx
        · rw [he] at hx
          exact hx.1) f hGraph
    intro x hx
    have hna := no_algebraic_point B h00 δ hδ1 hIm.2 hIm.1
      (⟨f x.val,hfVF x.val hx⟩ : VFType (M := M)) ⟨x.val,hx,rfl⟩
    exact FiniteFibresFromExchange.inverse_algebraic B.real f hf x (hsub hx) (hfVF x.val hx) hna

end IntegrationInACVF.Section3ACVF.AtomicFunctionFibres
