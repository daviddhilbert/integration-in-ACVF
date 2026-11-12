import IntegrationSection6.FinitePullbackSubsets
import IntegrationSection6.GammaFiniteMixedUnions
import IntegrationSection6.FiniteGammaPullbackPartitions
import IntegrationSection6.FiniteGammaEmptyIsomorphisms
import IntegrationSection5.RelativeSpecialRestriction

/-! A finite partition of an actual RV-pullback gives its sum of actual
RV[k] isomorphism classes. All labels and volumes are the native ones. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a : ℕ} {ι : Type}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

def gammaPullbackPieceAt (U : DefSet (M := M) Set.univ n a)
    (hUF : Map.FiniteFibres (rvObjectVolume (pullbackObject U)))
    (D : DefSet (M := M) Set.univ n a) (hD : GammaSetDefinable B (carrier D))
    (hDU : carrier D ⊆ carrier U) : GammaObjectAt B Set.univ n :=
  gammaPullbackAt (Set.subset_univ _) D hD (pullback_finite_of_subset hDU hUF)

def gammaPullbackUnionAt (U : DefSet (M := M) Set.univ n a)
    (hUF : Map.FiniteFibres (rvObjectVolume (pullbackObject U)))
    (D : ι → DefSet (M := M) Set.univ n a) (hD : ∀ i, GammaSetDefinable B (carrier (D i)))
    (hDU : ∀ i, carrier (D i) ⊆ carrier U) (F : Finset ι) : GammaObjectAt B Set.univ n :=
  gammaPullbackPieceAt U hUF (gammaMixedFiniteUnion D hD F) (gamma_mixedFiniteUnionSet D hD F)
    (mixedFiniteUnion_subset D hDU F)

theorem gammaPullbackUnion_class_sum (U : DefSet (M := M) Set.univ n a)
    (hUF : Map.FiniteFibres (rvObjectVolume (pullbackObject U)))
    (D : ι → DefSet (M := M) Set.univ n a) (hD : ∀ i, GammaSetDefinable B (carrier (D i)))
    (hDU : ∀ i, carrier (D i) ⊆ carrier U)
    (hDisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hPull : ∀ i, IsRVPullback (carrier (D i))) (F : Finset ι) :
    gammaIsoClassAt (gammaPullbackUnionAt U hUF D hD hDU F) =
      ∑ i ∈ F, gammaIsoClassAt (gammaPullbackPieceAt U hUF (D i) (hD i) (hDU i)) := by
  induction F using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    apply gammaIsoClassAt_eq_zero
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro r ⟨u,hu⟩
    have hp : u.val ∈ mixedFiniteUnionSet D ∅ := u.property
    rw [mixedFiniteUnionSet_empty] at hp
    exact hp
  | insert i F hi ih =>
    let A := gammaMixedFiniteUnion D hD (insert i F)
    let E := gammaMixedFiniteUnion D hD F
    let P := gammaPullbackUnionAt U hUF D hD hDU (insert i F)
    let Q := gammaPullbackPieceAt U hUF (D i) (hD i) (hDU i)
    let R := gammaPullbackUnionAt U hUF D hD hDU F
    have hpart : carrier A = carrier (D i) ∪ carrier E := mixedFiniteUnionSet_insert D i F
    have e := gammaPullbackPartitionIsoAt (Set.subset_univ _) (A := A) (C := D i) (E := E)
      (gamma_mixedFiniteUnionSet D hD (insert i F)) (hD i) (gamma_mixedFiniteUnionSet D hD F)
      P.object.property Q.object.property R.object.property hpart (mixedFiniteUnion_disjoint D hDisj i F hi) (hPull i)
    have he : gammaIsoClassAt P = gammaIsoClassAt (gammaCoprodAt Q R) := gammaIsoClassAt_iso e
    rw [he,gammaIsoClassAt_coprod,Finset.sum_insert hi]
    exact congrArg (gammaIsoClassAt Q + ·) ih

theorem gammaPullbackPartition_class_sum (U : DefSet (M := M) Set.univ n a)
    (hU : GammaSetDefinable B (carrier U))
    (hUF : Map.FiniteFibres (rvObjectVolume (pullbackObject U)))
    (D : ι → DefSet (M := M) Set.univ n a) (hD : ∀ i, GammaSetDefinable B (carrier (D i)))
    (hDU : ∀ i, carrier (D i) ⊆ carrier U)
    (hDisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hPull : ∀ i, IsRVPullback (carrier (D i))) (F : Finset ι)
    (hCover : carrier U = mixedFiniteUnionSet D F) :
    gammaIsoClassAt (gammaPullbackAt (Set.subset_univ _) U hU hUF) =
      ∑ i ∈ F, gammaIsoClassAt (gammaPullbackPieceAt U hUF (D i) (hD i) (hDU i)) := by
  have he : gammaMixedFiniteUnion D hD F = U := defSet_eq_of_carrier_eq hCover.symm
  have H := gammaPullbackUnion_class_sum U hUF D hD hDU hDisj hPull F
  simpa only [gammaPullbackUnionAt,gammaPullbackPieceAt,he] using H

end IntegrationInACVF.Section6.FiniteRV
