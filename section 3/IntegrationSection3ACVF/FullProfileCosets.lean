import IntegrationSection3ACVF.FullCosetExceptions
import IntegrationSection3.ProfileAtomicity

/-! Atomicity removes finite exceptional cosets when the atomic set meets
infinitely many classes. The default VF point is definable zero; it is used
only to totalize real-variable maps and adds no parameter. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullProfileCosets

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def vfDefault (x : M) : VFType (M := M) :=
  if hx : iVF x then ⟨x,hx⟩ else 0

theorem vfDefault_val (x : VFType (M := M)) : vfDefault x.val = x := by
  simp only [vfDefault,dif_pos x.property]

theorem vfDefault_definable (Q : Set M) :
    @Set.DefinableFun M LRV (CanonicalStructure.normalize (M := M))
      (Fin 1) Q (fun z => (vfDefault (z 0)).val) := by
  have hs := ((@definableAt_iff_normalized_raw M sM hM Q .vf _).mp
    (@definableAt_sort M sM Q .vf)).1
  let D : (Fin 1 → M) → M := fun z => (vfDefault (z 0)).val
  have hz : @iVFZero M (CanonicalStructure.normalize (M := M)) = @iVFZero M sM :=
    @CanonicalStructure.sortZero_normalize M sM .vf
  let N := CanonicalStructure.normalize (M := M)
  have hc : @Set.DefinableFun M LRV N (Fin 1) Q (fun _ => @iVFZero M sM) := by
    rw [← hz]
    letI := N
    exact SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol
        (L := LRV) Fn.vfZero Fin.elim0 (fun j => j.elim0))
  letI := N
  have hd := Set.DefinableFun.ite hs (Set.DefinableFun.proj LRV) hc
  change Q.DefinableFun LRV D
  convert hd using 1
  funext z
  dsimp [D]
  by_cases hx : @iVF M sM (z 0) <;> simp only [vfDefault,hx,↓reduceDIte,↓reduceIte]

theorem total_graph_definable (B : FullBaseAtomicity.Base (M := M)) {m : ℕ}
    (f : VFType (M := M) → Set (Fin m → M))
    (hf : FullBaseAtomicity.OverBase B (BallFibreConstancy.graph f)) :
    FullBaseAtomicity.OverBase B (ProfileAtomicity.graph (fun x => f (vfDefault x))) := by
  have hd := vfDefault_definable (M := M) B.real
  let D := vfDefault (M := M)
  let F : (Fin 1 ⊕ Fin m → M) → (Fin (m+1) → M) :=
    fun z => Fin.cons (D (z (.inl 0))).val (z ∘ Sum.inr)
  have hm : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin 1 ⊕ Fin m) (Fin (m+1)) B.real F := by
    letI := CanonicalStructure.normalize (M := M)
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact hd.comp (fun _ => Set.DefinableFun.proj LRV)
    · exact Set.DefinableFun.proj LRV
  have h := FullBaseAtomicity.OverBase.preimage_map hf hm
  convert h using 1
  ext z
  exact (BallFibreConstancy.mem_graph f (D (z (.inl 0))) (z ∘ Sum.inr)).symm

theorem total_class_relation_definable (B : FullBaseAtomicity.Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (hH : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))}) :
    FullBaseAtomicity.OverBase B {z : Fin 2 → M |
      QuotientAddGroup.mk' H (vfDefault (z 0)) = QuotientAddGroup.mk' H (vfDefault (z 1))} := by
  have hr := FullBallCoset.cosetRelation_definable B H hH
  have hd := vfDefault_definable (M := M) B.real
  let D := vfDefault (M := M)
  let F : (Fin 2 → M) → (Fin 2 → M) := fun z => ![(D (z 0)).val,(D (z 1)).val]
  have hm : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M))
      (Fin 2) (Fin 2) B.real F := by
    letI := CanonicalStructure.normalize (M := M)
    intro j
    fin_cases j
    · exact hd.comp (fun _ => Set.DefinableFun.proj LRV)
    · exact hd.comp (fun _ => Set.DefinableFun.proj LRV)
  convert FullBaseAtomicity.OverBase.preimage_map hr hm using 1
  ext z
  change (QuotientAddGroup.mk' H (D (z 0)) = QuotientAddGroup.mk' H (D (z 1))) ↔
    ![(D (z 1)).val,(D (z 0)).val] ∈
      DefinableCosets.relation (Subtype.val '' (H : Set (VFType (M := M))))
  exact eq_comm.trans (DefinableCosets.mem_relation H (D (z 1)) (D (z 0))).symm

/-- The atomicity step toward Lemma 3.9. Finiteness is obtained from the
pinned coset theorem. Infinitely many classes is the remaining ball-geometry
input, stated independently of the desired constancy. -/
theorem constant_on_cosets (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (hH : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))})
    {A : Set M} (hA : AdjoinBall.AtomicOver B A)
    {m : ℕ} (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hgraph : FullBaseAtomicity.OverBase B (BallFibreConstancy.graph f))
    (hinf : (QuotientAddGroup.mk' H '' {x : VFType (M := M) | x.val ∈ A}).Infinite) :
    ∀ x : VFType (M := M), x.val ∈ A → ∀ y : VFType (M := M), y.val ∈ A →
      QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y → f x = f y := by
  let D := vfDefault (M := M)
  let q : M → VFType (M := M) ⧸ H := fun x => QuotientAddGroup.mk' H (D x)
  let g : M → Set (Fin m → M) := fun x => f (D x)
  have hbad := FullCosetExceptions.finite_bad_cosets h00 B H hH f hf hgraph
  have hb : {c | ∃ x y : M, q x = c ∧ q y = c ∧ g x ≠ g y}.Finite :=
    hbad.subset (by rintro c ⟨x,y,hx,hy,hne⟩; exact ⟨D x,D y,hx,hy,hne⟩)
  have hi : (q '' A).Infinite := hinf.mono (by
    rintro c ⟨x,hx,rfl⟩
    refine ⟨x.val,hx,?_⟩
    change QuotientAddGroup.mk' H (vfDefault x.val) = QuotientAddGroup.mk' H x
    rw [vfDefault_val])
  have hg := total_graph_definable B f hgraph
  have hq := total_class_relation_definable B H hH
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hc : ∀ x ∈ A, ∀ y ∈ A, q x = q y → g x = g y := by
    letI := CanonicalStructure.normalize (M := M)
    exact ProfileAtomicity.constant_on_classes hp q hA hg hq hb hi
  intro x hx y hy he
  have hqx : q x.val = QuotientAddGroup.mk' H x := by dsimp [q,D]; rw [vfDefault_val]
  have hqy : q y.val = QuotientAddGroup.mk' H y := by dsimp [q,D]; rw [vfDefault_val]
  have h := hc x.val hx y.val hy (hqx.trans (he.trans hqy.symm))
  change f (vfDefault x.val) = f (vfDefault y.val) at h
  simpa only [vfDefault_val] using h

end IntegrationInACVF.Section3ACVF.FullProfileCosets
