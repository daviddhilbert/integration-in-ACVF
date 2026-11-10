import IntegrationSection3ACVF.FullBaseDefinability
import Section3.RingSyntax

/-! The actual affine affineError, represented by a normalized first-order term. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RVErrorSyntax

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

noncomputable def expression : FreeCommRing (Fin 0 ⊕ Fin 5) :=
  FreeCommRing.of (.inr 1) - FreeCommRing.of (.inr 4) -
    FreeCommRing.of (.inr 3) * (FreeCommRing.of (.inr 0) - FreeCommRing.of (.inr 2))

noncomputable def polyTerm : LRV.Term (Fin 0 ⊕ Fin 5) :=
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing expression)

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def affineError (c e fe x y : M) : M :=
  @iRv M (CanonicalStructure.normalize (M := M))
    (@Term.realize LRV M (CanonicalStructure.normalize (M := M)) _
      (Sum.elim Fin.elim0 ![x,y,e,c,fe]) polyTerm)

theorem poly_value (x y e c fe : VFType (M := M)) :
    @Term.realize LRV M (CanonicalStructure.normalize (M := M)) _
      (Sum.elim Fin.elim0 ![x.val,y.val,e.val,c.val,fe.val]) polyTerm = (y-fe-c*(x-e)).val := by
  let w : Fin 5 → VFType (M := M) := ![x,y,e,c,fe]
  have hn := CanonicalStructure.term_normalize hM (fun _ : Fin 0 => .vf) (fun _ : Fin 5 => .vf)
    Fin.elim0 (fun i => (w i).val) (fun i => i.elim0) (fun i => (w i).property)
    polyTerm (RingSyntax.sorted _)
  have he : ![x.val,y.val,e.val,c.val,fe.val] = (fun i => (w i).val) := by
    funext i
    fin_cases i <;> rfl
  rw [he,hn]
  have hv : (fun i => ((Sum.elim (Fin.elim0 : Fin 0 → VFType (M := M)) w) i).val) =
      Sum.elim Fin.elim0 (fun i => (w i).val) := by
    funext i
    cases i with
    | inl i => exact i.elim0
    | inr i => rfl
  rw [← hv]
  unfold polyTerm
  rw [RingSyntax.realizes,FirstOrder.Ring.realize_termOfFreeCommRing]
  simp only [expression,map_sub,map_mul,FreeCommRing.lift_of]
  rfl

theorem error_vf (c e fe x y : VFType (M := M)) :
    affineError c.val e.val fe.val x.val y.val = iRv (y-fe-c*(x-e)).val := by
  change @iRv M (CanonicalStructure.normalize (M := M))
    (@Term.realize LRV M (CanonicalStructure.normalize (M := M)) _
      (Sum.elim Fin.elim0 ![x.val,y.val,e.val,c.val,fe.val]) polyTerm) = _
  rw [poly_value]
  exact CanonicalStructure.normalize_fun Fn.rvMap ![(y-fe-c*(x-e)).val]
    (fun i => by fin_cases i; exact (y-fe-c*(x-e)).property)

theorem error_definable (B : FullBaseAtomicity.Base (M := M))
    (c e fe : M) (hc : c ∈ B.real) (he : e ∈ B.real) (hfe : fe ∈ B.real) :
    @Set.DefinableFun M LRV (CanonicalStructure.normalize (M := M)) (Fin 2) B.real
      (fun z => affineError c e fe (z 0) (z 1)) := by
  let E := @affineError M sM
  let N := @CanonicalStructure.normalize M sM
  change @Set.DefinableFun M LRV N (Fin 2) B.real (fun z => E c e fe (z 0) (z 1))
  letI := N
  have ht : (∅ : Set M).DefinableFun LRV (fun z => Term.realize z polyTerm) :=
    polyTerm.definableFun_realize (M := M)
  have hp : B.real.DefinableFun LRV (fun z : Fin 2 → M =>
      Term.realize (Sum.elim Fin.elim0 ![z 0,z 1,e,c,fe]) polyTerm) := by
    apply Set.DefinableFun.comp (f := fun z => Term.realize z polyTerm)
      (g := fun z : Fin 2 → M => Sum.elim Fin.elim0 ![z 0,z 1,e,c,fe])
    · intro j
      cases j with
      | inl j => exact j.elim0
      | inr j =>
        fin_cases j
        · exact Set.DefinableFun.proj LRV
        · exact Set.DefinableFun.proj LRV
        · exact LRV.definableFun_const (Fin 2) he
        · exact LRV.definableFun_const (Fin 2) hc
        · exact LRV.definableFun_const (Fin 2) hfe
    · exact ht.of_empty
  have hr : B.real.DefinableFun LRV (Structure.funMap (L := LRV) Fn.rvMap) :=
    Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV N 1 Fn.rvMap)
  exact Set.DefinableFun.comp
    (g := fun z : Fin 2 → M => ![Term.realize (Sum.elim Fin.elim0 ![z 0,z 1,e,c,fe]) polyTerm])
    (fun j => by fin_cases j; exact hp) hr

theorem graph_definable (B : FullBaseAtomicity.Base (M := M))
    (c e fe : M) (hc : c ∈ B.real) (he : e ∈ B.real) (hfe : fe ∈ B.real)
    {A : Set M} (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B
      (ImaginaryBaseImages.graphOn A (fun x => affineError c e fe x (f x))) := by
  let E := @affineError M sM
  have hE := error_definable B c e fe hc he hfe
  have hRel : FullBaseAtomicity.OverBase B
      {z : Fin 3 → M | z 2 = affineError c e fe (z 0) (z 1)} := by
    apply FullBaseAtomicity.OverBase.of_real
    letI := CanonicalStructure.normalize (M := M)
    have hE3 : B.real.DefinableFun LRV (fun z : Fin 3 → M => E c e fe (z 0) (z 1)) :=
      Set.DefinableFun.comp (f := fun z => E c e fe (z 0) (z 1))
        (g := fun z => ![z 0,z 1]) (fun j => by fin_cases j <;> exact Set.DefinableFun.proj LRV) hE
    exact (Set.DefinableFun.proj LRV).ofPred_eq hE3
  have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.preimage_comp hf (![.inl 0,.inr 0] : Fin 2 → Fin 2 ⊕ Fin 1))
    (FullBaseAtomicity.OverBase.preimage_comp hRel (![.inl 0,.inr 0,.inl 1] : Fin 3 → Fin 2 ⊕ Fin 1)))
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  change (∃ y : Fin 1 → M, (z 0 ∈ A ∧ y 0 = f (z 0)) ∧
    z 1 = affineError c e fe (z 0) (y 0)) ↔ (z 0 ∈ A ∧ z 1 = affineError c e fe (z 0) (f (z 0)))
  exact ⟨fun ⟨y,⟨ha,hy⟩,hE⟩ => ⟨ha,hy ▸ hE⟩,
    fun ⟨ha,hE⟩ => ⟨![f (z 0)],⟨ha,rfl⟩,hE⟩⟩

end IntegrationInACVF.Section3ACVF.RVErrorSyntax
