import Section9.VolumeChartCertificates

/-! Normalizing RV correspondences jointly in an arbitrary real parameter
tuple and the RV scales. The parameters remain free formula variables. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {π : Type} {n : ℕ} {S : Set M}
local notation "I" => Fin (n+n)
local notation "RV" => CanonicalRV.RVSort M
local notation "K" => ModelResidue M

def volumeFamilyRow (C : Set (π ⊕ I → M)) (z : π → M) : Set (I → RV) :=
  {r | Sum.elim z (rvValues r) ∈ C}

def rawVolumeFamilyNormalized (C : Set (π ⊕ I → M)) : Set ((π ⊕ I) ⊕ I → M) :=
  {w | Sum.elim (w ∘ Sum.inl ∘ Sum.inl)
      (fun i => iRVMul (w (.inl (.inr i))) (w (.inr i))) ∈ C ∧
    w ∘ Sum.inl ∘ Sum.inr ∈ (rawRVSpace (M := M) (n+n)).domain ∧
    w ∘ Sum.inr ∈ rawResidueImage {r : I → K | ∀ i, r i ≠ 0}}

theorem rawVolumeFamilyNormalized_definable
    [Finite π]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {C : Set (π ⊕ I → M)} (hC : S.Definable LRV C) :
    S.Definable LRV (rawVolumeFamilyNormalized C) := by
  let J := (π ⊕ I) ⊕ I
  let F (w : J → M) : π ⊕ I → M :=
    Sum.elim (w ∘ Sum.inl ∘ Sum.inl)
      (fun i => iRVMul (w (.inl (.inr i))) (w (.inr i)))
  have hF : S.DefinableMap LRV F := by
    intro i
    cases i with
    | inl i => exact Set.DefinableFun.proj LRV
    | inr i =>
      exact (Set.DefinableFun.of_empty
        (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
        (show S.DefinableMap LRV (fun w : J → M => ![w (.inl (.inr i)), w (.inr i)]) from
          fun j => by fin_cases j <;> exact Set.DefinableFun.proj LRV)
  let E := residueDefinableField S
  have hNZ : Relative.Def E {r : I → K | ∀ i, r i ≠ 0} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite fun i =>
      ((Relative.projection (E := E) i).eq_const 0 E.zero_mem).compl
  exact (hC.preimage_map hF).inter
    ((((rawRVSpace (M := M) (n+n)).domain_definable.mono (Set.empty_subset S)).preimage_comp
      (Sum.inl ∘ Sum.inr)).inter
        ((residueFieldImage_indexed_definable hc E S le_rfl _ hNZ).preimage_comp Sum.inr))

theorem mem_rawVolumeFamilyNormalized (C : Set (π ⊕ I → M)) (p : π → M)
    (a b : Fin n → RV) (z : I → K) :
    Sum.elim (Sum.elim p (rvValues (productTuple a b))) (residueRaw ∘ z) ∈
      rawVolumeFamilyNormalized C ↔ z ∈ normalizedCorrespondence (volumeFamilyRow C p) a b := by
  have he : (fun i => iRVMul ((productTuple a b i).val) (residueRaw (z i))) =
      rvValues (residueScale (productTuple a b) z) := by
    funext i
    exact (RVOperations.mul_val _ _).symm
  have hsort : rvValues (productTuple a b) ∈ (rawRVSpace (M := M) (n+n)).domain :=
    ⟨productTuple a b,rfl⟩
  change (Sum.elim p (fun i => iRVMul ((productTuple a b i).val) (residueRaw (z i))) ∈ C ∧
    rvValues (productTuple a b) ∈ (rawRVSpace (M := M) (n+n)).domain ∧
    residueRaw ∘ z ∈ rawResidueImage {r : I → K | ∀ i, r i ≠ 0}) ↔ _
  rw [he]
  have hz := mem_rawResidueImage_iff {r : I → K | ∀ i, r i ≠ 0} z
  exact ⟨fun h => ⟨h.1,hz.mp h.2.2⟩,fun h => ⟨h.1,hsort,hz.mpr h.2⟩⟩

end IntegrationInACVF.Section7
