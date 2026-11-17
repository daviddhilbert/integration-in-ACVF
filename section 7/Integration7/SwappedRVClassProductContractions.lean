module

public import Integration7.FixedLabelsVFPermutations
public import Integration7.RVClassProductRawObjectIsomorphisms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual standard contraction in the opposite two-coordinate
order. Its RV volume tuple restores the original coordinate order, so
the fixed class is the tail coordinate of the resulting product object. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {b d : ℕ}
variable (Z : DefSet (M := M) S 2 0) (B : DefSet (M := M) S 1 0)
variable (B' : DefSet (M := M) S 1 b) (T : SpecialBijection B B')
variable (hSat : HeadSaturated (carrier (vfPermutationImage Z (Equiv.swap 0 1)))) (r : RV (M := M))
variable (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
variable (L : ConstantRVLabelSpecialPreparation T
  (headImage (fixedRVLabelDomain (vfPermutationImage Z (Equiv.swap 0 1)) t ht))
  (Fin.append (fun _ : Fin 1 => r) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t)) P)

def swappedRVClassProductStandardContraction :
    StandardContraction (fixedRVLabelDomain Z t ht) (Equiv.swap 0 1) :=
  standardFromProgram _ _ (rvClassProductContractionProgram (vfPermutationImage Z (Equiv.swap 0 1))
    B B' T hSat r t ht L) (fixed_rv_label_domain_vf_permutation Z t ht (Equiv.swap 0 1))

theorem gamma_swapped_rv_class_product_standard_contraction
    (hZ : GammaSetDefinable P (carrier Z))
    (hTuple : DefinableOverBase P (fun _ : Fin d => .rv) {fun i => (t i).val}) :
    GammaProgramDefinable P (swappedRVClassProductStandardContraction Z B B' T hSat r t ht L).program :=
  gamma_standardFromProgram _ _ _ _ (gamma_rv_class_product_contraction_program
    (vfPermutationImage Z (Equiv.swap 0 1)) B B' T (gamma_vfPermutationImage Z hZ (Equiv.swap 0 1))
      hSat r t ht hTuple L)

theorem swapped_rv_class_product_standard_volume_index :
    (swappedRVClassProductStandardContraction Z B B' T hSat r t ht L).volumeIndex =
      (rvClassProductContractionProgram (vfPermutationImage Z (Equiv.swap 0 1)) B B' T hSat r t ht L).volumeIndex ∘
        Equiv.swap 0 1 := by
  funext i
  change (orderedCastSource _ _).volumeIndex ((Equiv.swap 0 1).symm i) = _
  rw [orderedCastSource_volumeIndex]
  rw [Equiv.symm_swap]
  rfl

variable (hc : CanonicalStructure.IsCanonical (M := M)) (hr : r.val ∈ S)
variable (hLF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
  (@CanonicalStructure.normalize M sM) _ _ S _ _ (rvObjectVolume (pullbackObject L.target)))

theorem swapped_rv_class_product_raw_projection_volume :
    let C := canonicalRVObject hc (swappedRVClassProductStandardContraction Z B B' T hSat r t ht L).contractionObject
    let U := canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩
    ∀ p : C.domain, (appendFixedRVCoordinate U r hr).obj.value
      (rvClassProductRawProjection hc (vfPermutationImage Z (Equiv.swap 0 1)) B B' T hSat r t ht L hLF p) =
        C.value p := by
  intro C U p
  funext i
  fin_cases i
  · change p.val (Fin.castAdd L.arity (0 : Fin 1)) =
      p.val ((swappedRVClassProductStandardContraction Z B B' T hSat r t ht L).volumeIndex 0)
    rw [swapped_rv_class_product_standard_volume_index]
    simp only [Function.comp_apply,Equiv.swap_apply_left]
    rw [rv_class_product_program_volume_second]
    exact congrArg p.val (Fin.ext rfl)
  · change r = p.val ((swappedRVClassProductStandardContraction Z B B' T hSat r t ht L).volumeIndex 1)
    rw [swapped_rv_class_product_standard_volume_index]
    simp only [Function.comp_apply,Equiv.swap_apply_right]
    obtain ⟨q,hq⟩ := p.property
    have he : q.val.2 = p.val := hq
    rw [← he]
    exact (rv_class_product_program_volume_first (vfPermutationImage Z (Equiv.swap 0 1))
      B B' T hSat r t ht L q).symm

def swappedRVClassProductRawRVIso :
    canonicalRVObject hc (swappedRVClassProductStandardContraction Z B B' T hSat r t ht L).contractionObject ≅
      (appendFixedRVCoordinate (canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩) r hr).obj :=
  rvIsoOfVolumePreservingBijection
    (rvClassProductRawProjection hc (vfPermutationImage Z (Equiv.swap 0 1)) B B' T hSat r t ht L hLF)
    (rv_class_product_raw_projection_bijective hc (vfPermutationImage Z (Equiv.swap 0 1)) B B' T hSat r t ht L hLF)
    (swapped_rv_class_product_raw_projection_volume Z B B' T hSat r t ht L hc hr hLF)

end IntegrationInACVF.Section7
