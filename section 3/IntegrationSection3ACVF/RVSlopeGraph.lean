import IntegrationSection3ACVF.RVMapBijection

/-! A definable slope relation in actual RV. Both source points and all
original imaginary codes are quantified in its full graph. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.RVDifferencePairs

namespace IntegrationInACVF.Section3ACVF.RVSlopeGraph

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def relation (A : Set M) (f : M → M) : Set (Fin 2 → M) :=
  {z | ∃ x ∈ A, ![z 0,z 1] ∈ PairMapFibres.family A f (difference (M := M)) x}

noncomputable def multiply (a b : M) : M :=
  @iRVMul M (CanonicalStructure.normalize (M := M)) a b

noncomputable def slopes (A : Set M) (f : M → M) : Set (Fin 2 → M) :=
  {z | NonzeroRV (z 0) ∧ NonzeroRV (z 1) ∧ ![z 0,multiply (z 1) (z 0)] ∈ relation A f}

theorem relation_definable (B : FullBaseAtomicity.Base (M := M)) {A : Set M} {f : M → M}
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B (relation A f) := by
  have hd := RVDifferencePairs.pair_graph_definable B hf
  have he := FullBaseAtomicity.OverBase.exists_block
    (FullBaseAtomicity.OverBase.preimage_comp hd
      (![.inr 0,.inl 0,.inl 1] : Fin 3 → Fin 2 ⊕ Fin 1))
  apply FullBaseAtomicity.OverBase.congr he
  intro z
  change (∃ x : Fin 1 → M, x 0 ∈ A ∧ ∃ y ∈ A,
      z 0 = difference y (x 0) ∧ z 1 = difference (f y) (f (x 0))) ↔
    ∃ x ∈ A, ∃ y ∈ A, z 0 = difference y x ∧ z 1 = difference (f y) (f x)
  exact ⟨fun ⟨x,hx,y,hy,ht,hu⟩ => ⟨x 0,hx,y,hy,ht,hu⟩,
    fun ⟨x,hx,y,hy,ht,hu⟩ => ⟨![x],hx,y,hy,ht,hu⟩⟩

theorem multiply_rv (a b : CanonicalRV.RVSort M) :
    multiply a.val b.val = iRVMul a.val b.val :=
  CanonicalStructure.normalize_fun Fn.rvMul ![a.val,b.val] (fun i => by
    fin_cases i
    · exact a.property
    · exact b.property)

theorem multiply_map_definable (Q : Set M) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) (Fin 2) (Fin 2) Q
      (fun z => ![z 0,multiply (z 1) (z 0)]) := by
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hm : Q.DefinableFun LRV (fun z : Fin 2 → M => iRVMul (z 1) (z 0)) := by
    have h : Q.DefinableFun LRV (Structure.funMap (L := LRV) Fn.rvMul) :=
      Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV N 2 Fn.rvMul)
    exact h.comp (fun i => by fin_cases i <;> exact Set.DefinableFun.proj LRV)
  intro i
  fin_cases i
  · exact Set.DefinableFun.proj LRV
  · exact hm

theorem slopes_definable (B : FullBaseAtomicity.Base (M := M)) {A : Set M} {f : M → M}
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B (slopes A f) := by
  have hn := FullBaseAtomicity.OverBase.of_real (B := B)
    (nonzero_codes_normalized_definable (M := M) B.real)
  have h0 := FullBaseAtomicity.OverBase.preimage_comp hn (fun _ : Fin 1 => (0 : Fin 2))
  have h1 := FullBaseAtomicity.OverBase.preimage_comp hn (fun _ : Fin 1 => (1 : Fin 2))
  have hR := FullBaseAtomicity.OverBase.preimage_map (relation_definable B hf)
    (multiply_map_definable B.real)
  exact FullBaseAtomicity.OverBase.inter h0 (FullBaseAtomicity.OverBase.inter h1 hR)

end IntegrationInACVF.Section3ACVF.RVSlopeGraph
