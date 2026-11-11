import IntegrationSection3ACVF.RVUnaryConstancy
import IntegrationSection3ACVF.RVDifferencePairs
import Section3.Barycentre

/-! Finite fibres become singletons when the RV of their mean-centred
points is constant. The actual characteristic-zero barycentre theorem is
the proved pinned Section3/Barycentre.rv_nonconstant. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FiniteFibreInjectivity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem injOn_of_centred_RV_constant (h00 : M ⊨ Axioms.ACVF00)
    (A : Set M) (hAVF : A ⊆ {x | iVF x}) (f : M → M)
    (F : M → Finset (VFType (M := M)))
    (hF : ∀ y (x : VFType (M := M)), x ∈ F y ↔ x.val ∈ A ∧ f x.val = y)
    (hConst : ∀ (x y : VFType (M := M)), x.val ∈ A → y.val ∈ A →
      iRv (x-Barycentre.mean (F (f x.val))).val = iRv (y-Barycentre.mean (F (f y.val))).val) :
    Set.InjOn f A := by
  intro x hx y hy he
  let xx : VFType (M := M) := ⟨x,hAVF hx⟩
  let yy : VFType (M := M) := ⟨y,hAVF hy⟩
  have hOne : (F (f x)).card ≤ 1 := by
    by_contra h
    obtain ⟨u,hu,v,hv,hne⟩ := Barycentre.rv_nonconstant h00 (F (f x)) (by omega)
    have hu' := (hF (f x) u).mp hu
    have hv' := (hF (f x) v).mp hv
    have h := hConst u v hu'.1 hv'.1
    rw [hu'.2,hv'.2] at h
    exact hne h
  have hxx : xx ∈ F (f x) := (hF (f x) xx).mpr ⟨hx,rfl⟩
  have hyy : yy ∈ F (f x) := (hF (f x) yy).mpr ⟨hy,he.symm⟩
  exact congrArg Subtype.val ((Finset.card_le_one.mp hOne) xx hxx yy hyy)

theorem centred_graph_definable (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} (mu : M → VFType (M := M))
    (hmu : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A (fun x => (mu x).val))) :
    FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A
      (fun x => RVDifferencePairs.difference x (mu x).val)) := by
  have hd := RVDifferencePairs.difference_graph_definable B
  have hg := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.preimage_comp hmu (![.inl 0,.inr 0] : Fin 2 → Fin 2 ⊕ Fin 1))
    (FullBaseAtomicity.OverBase.preimage_comp hd (![.inl 0,.inr 0,.inl 1] : Fin 3 → Fin 2 ⊕ Fin 1)))
  apply FullBaseAtomicity.OverBase.congr hg
  intro z
  change (∃ y : Fin 1 → M, (z 0 ∈ A ∧ y 0 = (mu (z 0)).val) ∧
    z 1 = RVDifferencePairs.difference (z 0) (y 0)) ↔
    (z 0 ∈ A ∧ z 1 = RVDifferencePairs.difference (z 0) (mu (z 0)).val)
  exact ⟨fun ⟨y,⟨ha,hy⟩,he⟩ => ⟨ha,hy ▸ he⟩,
    fun ⟨ha,he⟩ => ⟨![(mu (z 0)).val],⟨ha,rfl⟩,he⟩⟩

theorem injOn_of_definable_fibre_mean (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (F : M → Finset (VFType (M := M)))
    (hF : ∀ y (x : VFType (M := M)), x ∈ F y ↔ x.val ∈ A ∧ f x.val = y)
    (hMean : FullBaseAtomicity.OverBase B
      (ImaginaryBaseImages.graphOn A (fun x => (Barycentre.mean (F (f x))).val))) :
    Set.InjOn f A := by
  have hAVF : A ⊆ {x | iVF x} := by
    rcases ho with he | ⟨a,α,he⟩
    · exact he ▸ Set.Subset.rfl
    · rw [he]
      exact fun _ hx => hx.1
  let mu : M → VFType (M := M) := fun x => Barycentre.mean (F (f x))
  let g : M → M := fun x => RVDifferencePairs.difference x (mu x).val
  have hg := centred_graph_definable B mu hMean
  have hgRV (x : M) (hx : x ∈ A) : iRV (g x) := by
    let xx : VFType (M := M) := ⟨x,hAVF hx⟩
    change iRV (RVDifferencePairs.difference xx.val (mu x).val)
    rw [RVDifferencePairs.difference_vf xx (mu x)]
    exact rv_mem hM (xx-mu x).property
  have hConst := RVUnaryConstancy.constant B h00 δ hδ hδ1 ho hA g hg hgRV
  apply injOn_of_centred_RV_constant h00 A hAVF f F hF
  intro x y hx hy
  have h := hConst x.val hx y.val hy
  change RVDifferencePairs.difference x.val (mu x.val).val =
    RVDifferencePairs.difference y.val (mu y.val).val at h
  simpa only [RVDifferencePairs.difference_vf] using h

end IntegrationInACVF.Section3ACVF.FiniteFibreInjectivity
