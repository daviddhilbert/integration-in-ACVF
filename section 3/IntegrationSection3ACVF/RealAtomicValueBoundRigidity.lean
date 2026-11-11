import IntegrationSection3ACVF.AtomicFunctionInjectivity
import IntegrationSection3ACVF.AtomicValueBoundRigidity

/-! The radius contradiction for a real-parameter map on a larger domain.
Injectivity of its atomic open-ball restriction is proved, not assumed. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.RealAtomicValueBoundRigidity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem impossible {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    {D : Set M} (hsub : gammaBall a α true ⊆ D) (g : M → M)
    (hg : @Set.Definable M B.real LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      (ImaginaryBaseImages.graphOn D g))
    (hgVF : ∀ x ∈ gammaBall a α true, iVF (g x))
    (s : Values.Gamma (M := M))
    (hBound : ∀ (x : VFType (M := M)) (hx : x.val ∈ gammaBall a α true),
      s.val * α.val < Values.vfValueHom (⟨g x.val,hgVF _ hx⟩ : VFType (M := M)))
    (x y : VFType (M := M)) (hx : x.val ∈ gammaBall a α true) (hy : y.val ∈ gammaBall a α true)
    (hne : y ≠ x)
    (hPair : let gx : VFType (M := M) := ⟨g x.val,hgVF _ hx⟩
      let gy : VFType (M := M) := ⟨g y.val,hgVF _ hy⟩
      Values.vfValueHom (gy-gx) = s.val * Values.vfValueHom (y-x)) : False := by
  have ho : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
  rcases AtomicFunctionInjectivity.constant_or_injective hκ hs B hsmall h00 δ hδ hδ1
      ho hA hsub g hg hgVF with ⟨c,hc⟩ | hinj
  · let gx : VFType (M := M) := ⟨g x.val,hgVF _ hx⟩
    let gy : VFType (M := M) := ⟨g y.val,hgVF _ hy⟩
    change Values.vfValueHom (gy-gx) = s.val*Values.vfValueHom (y-x) at hPair
    have he : gy = gx := Subtype.ext ((hc y.val hy).trans (hc x.val hx).symm)
    rw [he,sub_self,map_zero] at hPair
    have hsNZ : s.val ≠ 0 := by simpa only [← Values.infinity_eq_zero] using s.property
    have hNZ : Values.vfValueHom (y-x) ≠ 0 := by
      intro hz
      have hi : Values.vfValueHom (y-x) = Values.infinity := hz.trans Values.infinity_eq_zero.symm
      have hRV0 := (Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv (y-x))).mp hi
      exact sub_ne_zero.mpr hne ((CanonicalRV.encodedRv_zero_iff (y-x)).mp hRV0)
    exact mul_ne_zero hsNZ hNZ hPair.symm
  · have hReal : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn D g) :=
      FullBaseAtomicity.OverBase.of_real hg
    have hm := FullBaseAtomicity.OverBase.preimage_comp hA.1 (fun _ : Fin 1 => (0 : Fin 2))
    have hGraph : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) g) := by
      apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hm hReal)
      intro z
      change (z 0 ∈ gammaBall a α true ∧ z 0 ∈ D ∧ z 1 = g (z 0)) ↔
        (z 0 ∈ gammaBall a α true ∧ z 1 = g (z 0))
      exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hsub h.1,h.2⟩⟩
    exact AtomicValueBoundRigidity.impossible hκ hs B hsmall h00 δ hδ hδ1 a α hA g hGraph
      hgVF hinj s hBound x y hx hy hne hPair

end IntegrationInACVF.Section3ACVF.RealAtomicValueBoundRigidity
