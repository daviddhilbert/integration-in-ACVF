module

public import Integration7.RVClassProductContractionValues
public import Integration7.FixedRVVolumeCoordinates
public import Section4.RVIsoTools
public import IntegrationSection5.StandardContractionNormalization

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The RV object of the actual product standard contraction is
isomorphic to the prepared unary object with the fixed class adjoined.
This is an exact coordinate-preserving map on the actual label domains. -/
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
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (A : DefSet (M := M) S 2 0) (B : DefSet (M := M) S 1 0)
variable (B' : DefSet (M := M) S 1 b) (T : SpecialBijection B B')
variable (hSat : HeadSaturated (carrier A)) (r : RV (M := M)) (hr : r.val ∈ S)
variable (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
variable (L : ConstantRVLabelSpecialPreparation T (headImage (fixedRVLabelDomain A t ht))
  (Fin.append (fun _ : Fin 1 => r) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t)) P)
variable (hLF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M (@CanonicalStructure.normalize M sM) _ _ S _ _
  (rvObjectVolume (pullbackObject L.target)))

def rvClassProductRawProjection :
    SpecialTransformations.DefinableGeometry.Map
      (canonicalRVObject hc (rvClassProductStandardContraction A B B' T hSat r t ht L).contractionObject).domain
      (canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩).obj.domain :=
  SpecialTransformations.DefinableGeometry.Map.inclusion
    (rv_class_product_standard_raw_domain A B B' T hSat r t ht L).le

theorem rv_class_product_raw_projection_bijective :
    Function.Bijective (rvClassProductRawProjection hc A B B' T hSat r t ht L hLF) := by
  constructor
  · intro p q he
    have hv := congrArg Subtype.val he
    exact Subtype.ext hv
  · intro q
    exact ⟨⟨q.val,(rv_class_product_standard_raw_domain A B B' T hSat r t ht L).ge q.property⟩,Subtype.ext rfl⟩

theorem rv_class_product_raw_projection_volume :
    let C := canonicalRVObject hc (rvClassProductStandardContraction A B B' T hSat r t ht L).contractionObject
    let U := canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩
    ∀ p : C.domain, (prependFixedRVCoordinate U r hr).obj.value
      (rvClassProductRawProjection hc A B B' T hSat r t ht L hLF p) = C.value p := by
  intro C U p
  funext i
  fin_cases i
  · change r = p.val ((rvClassProductStandardContraction A B B' T hSat r t ht L).volumeIndex 0)
    rw [rv_class_product_standard_volume_index]
    obtain ⟨q,hq⟩ := p.property
    have he : q.val.2 = p.val := hq
    rw [← he]
    exact (rv_class_product_program_volume_first A B B' T hSat r t ht L q).symm
  · change p.val (Fin.castAdd L.arity (0 : Fin 1)) =
      p.val ((rvClassProductStandardContraction A B B' T hSat r t ht L).volumeIndex 1)
    rw [rv_class_product_standard_volume_index,rv_class_product_program_volume_second]
    exact congrArg p.val (Fin.ext rfl)

def rvClassProductRawRVIso :
    canonicalRVObject hc (rvClassProductStandardContraction A B B' T hSat r t ht L).contractionObject ≅
      (prependFixedRVCoordinate (canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩) r hr).obj :=
  rvIsoOfVolumePreservingBijection (rvClassProductRawProjection hc A B B' T hSat r t ht L hLF)
    (rv_class_product_raw_projection_bijective hc A B B' T hSat r t ht L hLF)
    (rv_class_product_raw_projection_volume hc A B B' T hSat r hr t ht L hLF)

def rvClassProductNormalizedFiniteRVIso
    (hCF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M (@CanonicalStructure.normalize M sM) _ _ S _ _
      (rvObjectVolume (rvClassProductStandardContraction A B B' T hSat r t ht L).normalizedObject)) :
    canonicalFiniteRVObject hc ⟨(rvClassProductStandardContraction A B B' T hSat r t ht L).normalizedObject,hCF⟩ ≅
      prependFixedRVCoordinate (canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩) r hr :=
  rvFiniteIsoOfAmbient ((canonicalRVIso hc
    (rvClassProductStandardContraction A B B' T hSat r t ht L).normalizationIso).symm.trans
      (rvClassProductRawRVIso hc A B B' T hSat r hr t ht L hLF))

end IntegrationInACVF.Section7
