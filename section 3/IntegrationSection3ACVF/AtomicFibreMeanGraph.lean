import IntegrationSection3ACVF.FullFibreMeans
import IntegrationSection3ACVF.FullBallCoset
import IntegrationSection3.AtomicFiniteFibres

/-! Actual finite fibres have a mean graph over the unchanged interpreted
base. Atomicity supplies the uniform finite bound; all enumerations remain
quantified variables of the defining formula. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.AtomicFibreMeanGraph

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_mean_graph (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {A : Set M} (hA : AdjoinBall.AtomicOver B A)
    (hAVF : A ⊆ {x | iVF x}) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hFinite : ∀ y : M, {x : M | x ∈ A ∧ f x = y}.Finite) :
    ∃ F : M → Finset (VFType (M := M)),
      (∀ y (x : VFType (M := M)), x ∈ F y ↔ x.val ∈ A ∧ f x.val = y) ∧
      FullBaseAtomicity.OverBase B
        (ImaginaryBaseImages.graphOn A (fun x => (Barycentre.mean (F (f x))).val)) := by
  have hpre (y : M) : {x : VFType (M := M) | x.val ∈ A ∧ f x.val = y}.Finite :=
    (hFinite y).preimage Subtype.val_injective.injOn
  let F (y : M) : Finset (VFType (M := M)) := (hpre y).toFinset
  have hMem (y : M) (x : VFType (M := M)) : x ∈ F y ↔ x.val ∈ A ∧ f x.val = y :=
    (hpre y).mem_toFinset
  have hImage (y : M) : Subtype.val '' (F y : Set (VFType (M := M))) =
      {x : M | x ∈ A ∧ f x = y} := by
    ext x
    constructor
    · rintro ⟨u,hu,he⟩
      exact he ▸ (hMem y u).mp hu
    · intro hx
      exact ⟨⟨x,hAVF hx.1⟩,(hMem y _).mpr hx,rfl⟩
  have hCard (y : M) : (F y).card = {x : M | x ∈ A ∧ f x = y}.ncard := by
    rw [← hImage y,Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_coe_finset]
  let R : Set (M × M) := {p | p.2 ∈ A ∧ f p.2 = p.1}
  have hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R} := by
    apply FullBaseAtomicity.OverBase.congr
      (FullBaseAtomicity.OverBase.preimage_comp hf (![1,0] : Fin 2 → Fin 2))
    intro z
    change (z 1 ∈ A ∧ z 0 = f (z 1)) ↔ (z 1 ∈ A ∧ f (z 1) = z 0)
    exact and_congr_right (fun _ => eq_comm)
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hY : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ f '' A} := by
    letI := @CanonicalStructure.normalize M sM
    exact ImaginaryBaseImages.image_definable hf
  have hYcomplete : FullBallCoset.CompleteType B (f '' A) := by
    letI := @CanonicalStructure.normalize M sM
    exact ImaginaryBaseImages.completeType_image hp hA.2 hf
  have hN : ∃ N : ℕ, ∀ y ∈ f '' A, {x : M | (y,x) ∈ R}.ncard ≤ N := by
    letI := @CanonicalStructure.normalize M sM
    exact AtomicFiniteFibres.uniform_bound hp hYcomplete hR (fun y _ => hFinite y)
  obtain ⟨N,hN⟩ := hN
  let F' (t : Fin 1 → M) := F (t 0)
  have hRel : FullBaseAtomicity.OverBase B {z : Fin 1 ⊕ Fin 1 → M |
      (z ∘ Sum.inl,z (.inr 0)) ∈ Barycentre.finiteFibreRelation F'} := by
    apply FullBaseAtomicity.OverBase.congr
      (FullBaseAtomicity.OverBase.preimage_comp hR (![.inl 0,.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1))
    intro z
    change (z (.inr 0) ∈ A ∧ f (z (.inr 0)) = z (.inl 0)) ↔
      ∃ x ∈ F (z (.inl 0)), x.val = z (.inr 0)
    constructor
    · intro hx
      exact ⟨⟨z (.inr 0),hAVF hx.1⟩,(hMem _ _).mpr hx,rfl⟩
    · rintro ⟨x,hx,he⟩
      exact he ▸ (hMem _ x).mp hx
  let T : Set (Fin 1 → M) := {t | t 0 ∈ f '' A}
  have hne (t : Fin 1 → M) (ht : t ∈ T) : (F' t).Nonempty := by
    obtain ⟨x,hx,he⟩ := ht
    exact ⟨⟨x,hAVF hx⟩,(hMem _ _).mpr ⟨hx,he⟩⟩
  have hBound (t : Fin 1 → M) (ht : t ∈ T) : (F' t).card ≤ N := by
    rw [hCard]
    exact hN (t 0) ht
  have hG := FullFibreMeans.bounded_graph_definable B h00 F' hRel T hY hne N hBound
  have hMeanY : FullBaseAtomicity.OverBase B
      (ImaginaryBaseImages.graphOn (f '' A) (fun y => (Barycentre.mean (F y)).val)) :=
    FullBaseAtomicity.OverBase.preimage_comp hG
      (Sum.elim (fun _ : Fin 1 => (0 : Fin 2)) (fun _ : Fin 1 => (1 : Fin 2)))
  refine ⟨F,hMem,?_⟩
  have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.preimage_comp hf (![.inl 0,.inr 0] : Fin 2 → Fin 2 ⊕ Fin 1))
    (FullBaseAtomicity.OverBase.preimage_comp hMeanY (![.inr 0,.inl 1] : Fin 2 → Fin 2 ⊕ Fin 1)))
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  change (∃ y : Fin 1 → M, (z 0 ∈ A ∧ y 0 = f (z 0)) ∧
    y 0 ∈ f '' A ∧ z 1 = (Barycentre.mean (F (y 0))).val) ↔
    (z 0 ∈ A ∧ z 1 = (Barycentre.mean (F (f (z 0)))).val)
  exact ⟨fun ⟨y,⟨ha,hy⟩,_,he⟩ => ⟨ha,hy ▸ he⟩,
    fun ⟨ha,he⟩ => ⟨![f (z 0)],⟨ha,rfl⟩,⟨z 0,ha,rfl⟩,he⟩⟩

end IntegrationInACVF.Section3ACVF.AtomicFibreMeanGraph
