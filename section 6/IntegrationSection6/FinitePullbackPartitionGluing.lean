import IntegrationSection6.FinitePullbackPartitionClasses
import IntegrationSection6.GammaIspUniversalPresentation
import IntegrationSection6.FiniteGammaAdditiveCongruence

/-! Actual common blowups on the pieces of finite pullback partitions
glue to a common blowup of the whole RV[k] objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a b : ℕ} {ι : Type}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

theorem gamma_pullback_partition_gluing {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ)
    (U : DefSet (M := M) Set.univ n a) (V : DefSet (M := M) Set.univ n b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hUF : Map.FiniteFibres (rvObjectVolume (pullbackObject U)))
    (hVF : Map.FiniteFibres (rvObjectVolume (pullbackObject V)))
    (D : ι → DefSet (M := M) Set.univ n a) (E : ι → DefSet (M := M) Set.univ n b)
    (hD : ∀ i, GammaSetDefinable B (carrier (D i))) (hE : ∀ i, GammaSetDefinable B (carrier (E i)))
    (hDU : ∀ i, carrier (D i) ⊆ carrier U) (hEV : ∀ i, carrier (E i) ⊆ carrier V)
    (hDdisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hEdisj : ∀ i j, i ≠ j → Disjoint (carrier (E i)) (carrier (E j)))
    (hDP : ∀ i, IsRVPullback (carrier (D i))) (hEP : ∀ i, IsRVPullback (carrier (E i)))
    (F : Finset ι) (hUcover : carrier U = mixedFiniteUnionSet D F) (hVcover : carrier V = mixedFiniteUnionSet E F)
    (hPieces : ∀ i, GammaIsp hκ hs h00 hreal
      (gammaPullbackPieceAt U hUF (D i) (hD i) (hDU i)).toGamma
      (gammaPullbackPieceAt V hVF (E i) (hE i) (hEV i)).toGamma) :
    GammaIsp hκ hs h00 hreal (gammaPullbackAt (Set.subset_univ _) U hU hUF).toGamma
      (gammaPullbackAt (Set.subset_univ _) V hV hVF).toGamma := by
  let R := gammaIspAddConAt (B := B) (S := Set.univ) (n := n) hκ hs h00 hreal
  have hEach (i : ι) : R
      (gammaIsoClassAt (gammaPullbackPieceAt U hUF (D i) (hD i) (hDU i)))
      (gammaIsoClassAt (gammaPullbackPieceAt V hVF (E i) (hE i) (hEV i))) := by
    apply (gammaClassIspAt_class_iff _ _).mpr
    exact (hPieces i).at_univ
  have hSum : R
      (∑ i ∈ F, gammaIsoClassAt (gammaPullbackPieceAt U hUF (D i) (hD i) (hDU i)))
      (∑ i ∈ F, gammaIsoClassAt (gammaPullbackPieceAt V hVF (E i) (hE i) (hEV i))) := by
    clear hUcover hVcover
    induction F using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact R.refl 0
    | insert i F hi ih =>
      rw [Finset.sum_insert hi,Finset.sum_insert hi]
      exact R.add (hEach i) ih
  have hLeft := gammaPullbackPartition_class_sum U hU hUF D hD hDU hDdisj hDP F hUcover
  have hRight := gammaPullbackPartition_class_sum V hV hVF E hE hEV hEdisj hEP F hVcover
  rw [← hLeft,← hRight] at hSum
  exact ((gammaClassIspAt_class_iff _ _).mp hSum).to_global

end IntegrationInACVF.Section6.FiniteRV
