import IntegrationSection6.GammaMixedPreimageComplements
import IntegrationSection6.GammaBinaryMixedPartitions
import IntegrationSection6.PreparedPartitionsAllDegrees
import IntegrationSection6.PreparedPartitionBlowups
import IntegrationSection6.GammaPullbackLiftIsomorphisms
import IntegrationSection6.FiniteIntegrationTarget
import IntegrationSection6.FinitePullbackPartitionClasses

/-! A definable subset of a lifted object and its complement have actual
finite RV representatives whose integration classes add to the original.
This proves the geometric partition law needed for scissor descent. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k n a : ℕ}

theorem binary_lift_partition_values {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
    (U : GammaObjectAt B Set.univ k) {C : Set (Point (M := M) n a)} (e : GammaIso B U.toGamma.lift C)
    (D : Set (Point (M := M) n a)) (hD : GammaSetDefinable B D) (hDC : D ⊆ C) :
    ∃ V W : GammaRVFiniteObject B k,
      rvIntegralClass hκ hs h00 hreal U.toGamma = rvIntegralClass hκ hs h00 hreal V + rvIntegralClass hκ hs h00 hreal W ∧
      Nonempty (GammaIso B D V.lift) ∧ Nonempty (GammaIso B (C \ D) W.lift) := by
  let A := typedLift U.object.obj
  have hA : GammaSetDefinable B (carrier A) := by rw [typedLift_carrier]; exact U.toGamma.toGammaRVObject.lift_definable
  let f := e.congr (typedLift_carrier U.object.obj).symm rfl
  let F := gammaIsoSetPreimage f D
  have hF : GammaSetDefinable B F := gammaIsoSetPreimage_definable f D hD
  let Z := binaryMixedPieces A hA F hF
  obtain ⟨P⟩ := prepared_mixed_partition_all_degrees hs h00 hreal FBase A hA (typedLift_pullback U.object.obj) Z
    (binaryMixedPieces_definable A hA F hF) (binaryMixedPieces_subset A hA F hF (gammaIsoSetPreimage_subset f D))
    (binaryMixedPieces_disjoint A hA F hF) (binaryMixedPieces_cover A hA F hF (gammaIsoSetPreimage_subset f D))
  obtain ⟨hPF,H⟩ := prepared_partition_blowup hκ hs h00 hreal U Z P
  have hPΓ := GammaChainDefinable.target B P.special.chain P.gamma
  let V := gammaPullbackPieceAt P.target hPF (P.pieces false) (P.definable false) (P.subset false)
  let W := gammaPullbackPieceAt P.target hPF (P.pieces true) (P.definable true) (P.subset true)
  have hpart : carrier P.target = carrier (P.pieces false) ∪ carrier (P.pieces true) :=
    P.cover.trans (mixedFiniteUnionSet_bool P.pieces)
  let d := gammaPullbackPartitionIsoAt (Set.subset_univ _) hPΓ (P.definable false) (P.definable true)
    hPF V.object.property W.object.property hpart (P.disjoint false true Bool.false_ne_true) (P.piecePullback false)
  have hClass : rvIntegralClass hκ hs h00 hreal U.toGamma =
      rvIntegralClass hκ hs h00 hreal V.toGamma + rvIntegralClass hκ hs h00 hreal W.toGamma := by
    exact ((rvIntegralClass_eq_iff hκ hs h00 hreal _ _).mpr H).trans
      ((rvIntegralClass_iso hκ hs h00 hreal d.toGamma).trans (rvIntegralClass_coprod hκ hs h00 hreal V W))
  let g := gammaIsoSetPreimageIso f D hDC hD
  let g' := gammaIsoSetPreimageComplementIso f D hD
  let v := ((g.symm (gammaLogicInput B)).trans (gammaLogicInput B) (P.unary false).toIso).trans
    (gammaLogicInput B) (gammaPullbackLiftIso (Set.subset_univ _) (P.pieces false) (P.definable false) (P.piecePullback false))
  let w := ((g'.symm (gammaLogicInput B)).trans (gammaLogicInput B) (P.unary true).toIso).trans
    (gammaLogicInput B) (gammaPullbackLiftIso (Set.subset_univ _) (P.pieces true) (P.definable true) (P.piecePullback true))
  exact ⟨V.toGamma,W.toGamma,hClass,⟨v⟩,⟨w⟩⟩

end IntegrationInACVF.Section6.FiniteRV
