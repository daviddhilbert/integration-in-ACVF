import IntegrationSection3ACVF.RVErrorSyntax
import IntegrationSection3ACVF.RVUnaryConstancy

/-! Actual RV of the affine error is constant on an atomic open ball. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RVErrorConstancy

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem constant (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x))
    (c e fe : VFType (M := M)) (hc : c.val ∈ B.real)
    (he : e.val ∈ B.real) (hfe : fe.val ∈ B.real) :
    ∀ (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A),
      let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
      let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
      CanonicalRV.encodedRv (fy-fe-c*(y-e)) = CanonicalRV.encodedRv (fx-fe-c*(x-e)) := by
  have hAVF : A ⊆ {x | iVF x} := by
    rcases ho with he | ⟨a,α,he⟩
    · exact he ▸ Set.Subset.rfl
    · rw [he]
      exact fun _ hx => hx.1
  let g : M → M := fun x => RVErrorSyntax.affineError c.val e.val fe.val x (f x)
  have hg := RVErrorSyntax.graph_definable B c.val e.val fe.val hc he hfe f hf
  have hgRV (x : M) (hx : x ∈ A) : iRV (g x) := by
    let x' : VFType (M := M) := ⟨x,hAVF hx⟩
    let fx : VFType (M := M) := ⟨f x,hfVF x hx⟩
    have hE := RVErrorSyntax.error_vf c e fe x' fx
    change iRV (RVErrorSyntax.affineError c.val e.val fe.val x (f x))
    rw [hE]
    exact rv_mem hM (fx-fe-c*(x'-e)).property
  have hConst := RVUnaryConstancy.constant B h00 δ hδ hδ1 ho hA g hg hgRV
  intro x y hx hy
  let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
  let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
  have hraw := hConst y.val hy x.val hx
  change RVErrorSyntax.affineError c.val e.val fe.val y.val (f y.val) =
    RVErrorSyntax.affineError c.val e.val fe.val x.val (f x.val) at hraw
  rw [RVErrorSyntax.error_vf c e fe y fy,RVErrorSyntax.error_vf c e fe x fx] at hraw
  exact Subtype.ext hraw

end IntegrationInACVF.Section3ACVF.RVErrorConstancy
