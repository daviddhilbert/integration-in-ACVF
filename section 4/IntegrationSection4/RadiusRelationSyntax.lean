import IntegrationSection4.UnaryPreparation
import IntegrationSection3ACVF.FullBaseLogic
import IntegrationSection3ACVF.UniformGammaBallSyntax

/-! The entire source/image radius relation, with both radii free.
No radius function or choice of a least radius is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
open UniformGammaBallSyntax GammaRadiusAtomicity

namespace IntegrationInACVF.Section4.RadiusRelationSyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def image (A : Set M) (f : M → M) (a : Fin 4 → M) : Prop :=
  ∀ p : Fin 1 → M, ball (a 1) (p 0) (a 3) ↔
    ∃ q : Fin 1 → M, ball (a 0) (q 0) (a 2) ∧ q 0 ∈ A ∧ p 0 = f (q 0)

def row (A : Set M) (f : M → M) (a : Fin 3 → M) : Prop :=
  (∀ p : Fin 1 → M, ball (a 0) (p 0) (a 2) → p 0 ∈ A) ∧
    ∃ d : Fin 1 → M, iVF (d 0) ∧ image A f ![a 0,a 1,a 2,d 0]

theorem image_definable (B : FullBaseAtomicity.Base (M := M)) (A : Set M) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B {a : Fin 4 → M | image A f a} := by
  let ι := Fin 4 ⊕ Fin 1
  let υ := ι ⊕ Fin 1
  have hS := FullBaseAtomicity.OverBase.preimage_comp (ball_definable B)
    (![.inl (.inl 0),.inr 0,.inl (.inl 2)] : Fin 3 → υ)
  have hG := FullBaseAtomicity.OverBase.preimage_comp hf
    (![.inr 0,.inl (.inr 0)] : Fin 2 → υ)
  have hE := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hS hG)
  have hT := FullBaseAtomicity.OverBase.preimage_comp (ball_definable B)
    (![.inl 1,.inr 0,.inl 3] : Fin 3 → ι)
  exact FullBaseAtomicity.OverBase.forall_block (FullBaseLogic.equivalence B hT hE)

theorem row_definable (B : FullBaseAtomicity.Base (M := M)) (A : Set M) (f : M → M)
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B {a : Fin 3 → M | row A f a} := by
  let ι := Fin 3 ⊕ Fin 1
  have hS := FullBaseAtomicity.OverBase.preimage_comp (ball_definable B)
    (![.inl 0,.inr 0,.inl 2] : Fin 3 → ι)
  have hD := FullBaseAtomicity.OverBase.preimage_comp hA (Sum.inr : Fin 1 → ι)
  have hSub := FullBaseAtomicity.OverBase.forall_block (FullBaseLogic.implication B hS hD)
  have hVF := ((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
    (@definableAt_sort M sM B.real .vf)).1
  have hSort := FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.of_real (B := B) hVF)
    (Sum.inr : Fin 1 → ι)
  have hIm := FullBaseAtomicity.OverBase.preimage_comp (image_definable B A f hf)
    (![.inl 0,.inl 1,.inl 2,.inr 0] : Fin 4 → ι)
  exact FullBaseAtomicity.OverBase.inter hSub
    (FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hSort hIm))

theorem ball_iff_raw (r : M) (hr : NonzeroRV r) (c : VFType (M := M)) (x : M) :
    ball r x c.val ↔ x ∈ gammaBall c (codeValue r) true := by
  constructor
  · intro h
    exact (ball_iff r hr ⟨x,h.1⟩ c).mp h
  · intro h
    exact (ball_iff r hr ⟨x,h.1⟩ c).mpr h

theorem image_iff (A : Set M) (f : M → M) (r s : M) (hr : NonzeroRV r) (hs : NonzeroRV s)
    (c d : VFType (M := M)) :
    image A f ![r,s,c.val,d.val] ↔
      f '' (gammaBall c (codeValue r) true ∩ A) = gammaBall d (codeValue s) true := by
  constructor
  · intro h
    ext y
    have hh := h ![y]
    change ball s y d.val ↔ ∃ q : Fin 1 → M, ball r (q 0) c.val ∧ q 0 ∈ A ∧ y = f (q 0) at hh
    rw [ball_iff_raw s hs d y] at hh
    constructor
    · rintro ⟨x,⟨hx,hA⟩,he⟩
      exact hh.mpr ⟨![x],(ball_iff_raw r hr c x).mpr hx,hA,he.symm⟩
    · intro hy
      obtain ⟨q,hq,hA,he⟩ := hh.mp hy
      exact ⟨q 0,⟨(ball_iff_raw r hr c (q 0)).mp hq,hA⟩,he.symm⟩
  · intro h p
    change ball s (p 0) d.val ↔ ∃ q : Fin 1 → M, ball r (q 0) c.val ∧ q 0 ∈ A ∧ p 0 = f (q 0)
    rw [ball_iff_raw s hs d (p 0),← h]
    exact ⟨fun ⟨x,⟨hx,hA⟩,he⟩ => ⟨![x],(ball_iff_raw r hr c x).mpr hx,hA,he.symm⟩,
      fun ⟨q,hq,hA,he⟩ => ⟨q 0,⟨(ball_iff_raw r hr c (q 0)).mp hq,hA⟩,he.symm⟩⟩

theorem row_iff (A : Set M) (f : M → M) (r s : M) (hr : NonzeroRV r) (hs : NonzeroRV s)
    (c : VFType (M := M)) : row A f ![r,s,c.val] ↔
      gammaBall c (codeValue r) true ⊆ A ∧ ∃ d : VFType (M := M),
        f '' gammaBall c (codeValue r) true = gammaBall d (codeValue s) true := by
  constructor
  · rintro ⟨hSub,d,hd,hi⟩
    have hBA : gammaBall c (codeValue r) true ⊆ A := fun x hx =>
      hSub ![x] ((ball_iff_raw r hr c x).mpr hx)
    refine ⟨hBA,⟨d 0,hd⟩,?_⟩
    have hh := (image_iff A f r s hr hs c ⟨d 0,hd⟩).mp hi
    rwa [Set.inter_eq_left.mpr hBA] at hh
  · rintro ⟨hSub,d,hi⟩
    refine ⟨fun p hp => hSub ((ball_iff_raw r hr c (p 0)).mp hp),![d.val],d.property,?_⟩
    apply (image_iff A f r s hr hs c d).mpr
    rwa [Set.inter_eq_left.mpr hSub]

def relation (A : Set M) (f : M → M) (p : Point (M := M) 1 0)
    (q : Point (M := M) 0 2) : Prop :=
  NonzeroRV (q.2 0).val ∧ NonzeroRV (q.2 1).val ∧
    row A f ![(q.2 0).val,(q.2 1).val,(vfAt p 0).val]

theorem relation_definable (G : GammaParameters.Base (M := M)) (A : Set M) (f : M → M)
    (hA : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) {z : Fin 1 → M | z 0 ∈ A})
    (hf : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) (ImaginaryBaseImages.graphOn A f)) :
    GammaGraphDefinable G (relation A f) := by
  let B := GammaBaseBridge.fullBase G
  let D : Set (Fin 3 → M) := {z | iVF (z 0) ∧ NonzeroRV (z 1) ∧ NonzeroRV (z 2) ∧
    row A f ![z 1,z 2,z 0]}
  have hVF : FullBaseAtomicity.OverBase B {z : Fin 1 → M | iVF (z 0)} :=
    FullBaseAtomicity.OverBase.of_real (((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
      (@definableAt_sort M sM B.real .vf)).1)
  have hV := FullBaseAtomicity.OverBase.preimage_comp hVF (fun _ : Fin 1 => (0 : Fin 3))
  have hP := FullBaseAtomicity.OverBase.preimage_comp (FullGammaSyntax.proper_definable (ι := Fin 2) B)
    (![1,2] : Fin 2 → Fin 3)
  have hR := FullBaseAtomicity.OverBase.preimage_comp (row_definable B A f hA hf)
    (![1,2,0] : Fin 3 → Fin 3)
  have hD : FullBaseAtomicity.OverBase B D := by
    apply FullBaseAtomicity.OverBase.congr
      (FullBaseAtomicity.OverBase.inter hV (FullBaseAtomicity.OverBase.inter hP hR))
    intro z
    change (iVF (z 0) ∧ SpecialTransformations.Section4.GammaSyntax.Proper (z ∘ (![1,2] : Fin 2 → Fin 3)) ∧
      row A f (z ∘ (![1,2,0] : Fin 3 → Fin 3))) ↔ _
    have he : z ∘ (![1,2,0] : Fin 3 → Fin 3) = ![z 1,z 2,z 0] := by
      funext i; fin_cases i <;> rfl
    rw [he]
    exact ⟨fun h => ⟨h.1,h.2.1 0,h.2.1 1,h.2.2⟩,
      fun h => ⟨h.1,(by intro i; fin_cases i; exact h.2.1; exact h.2.2.1),h.2.2.2⟩⟩
  have hEq : {z | ∃ (p : Point (M := M) 1 0) (q : Point (M := M) 0 2),
      relation A f p q ∧ Fin.append (gammaPointCode p) (gammaPointCode q) = z} = D := by
    ext z
    constructor
    · rintro ⟨p,q,⟨hr,hs,hrow⟩,rfl⟩
      exact ⟨(vfAt p 0).property,hr,hs,hrow⟩
    · rintro ⟨hx,hr,hs,hrow⟩
      let p : Point (M := M) 1 0 := unaryPoint ⟨z 0,hx⟩ Fin.elim0
      let q : Point (M := M) 0 2 := (Fin.elim0,![⟨z 1,hr.1⟩,⟨z 2,hs.1⟩])
      refine ⟨p,q,⟨hr,hs,hrow⟩,?_⟩
      funext i
      fin_cases i <;> rfl
  change GammaParameters.DefinableOverBase G
    (Fin.append (gammaPointSort 1 0) (gammaPointSort 0 2)) _
  rw [hEq]
  apply GammaBaseDescent.to_gamma G _ D hD
  intro z hz i
  fin_cases i
  · exact hz.1
  · exact hz.2.1.1
  · exact hz.2.2.1.1


end IntegrationInACVF.Section4.RadiusRelationSyntax
