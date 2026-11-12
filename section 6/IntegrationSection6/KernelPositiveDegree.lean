import IntegrationSection6.UnaryPartitionImageFactors
import IntegrationSection6.PreparedPartitionBlowups
import IntegrationSection6.PullbackUnaryChainComparison
import IntegrationSection6.FinitePullbackPartitionGluing

/-! The kernel direction of Lemma6.17 in every positive RV degree.
The finite partition and unary factors come from checked Section5.6.
Section5.8 is the sole unfinished input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

theorem lemma_6_17_kernel_positive {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (h58 : Section5TwoOrderInputAll hκ.le hs)
    (U V : GammaRVFiniteObject B (n+1)) (e : GammaIso B U.lift V.lift) :
    GammaIsp hκ.le hs h00 hreal U V := by
  let UA := gammaUniversalObject U
  let VA := gammaUniversalObject V
  let A := typedLift UA.object.obj
  let C := typedLift VA.object.obj
  have hA : GammaSetDefinable B (carrier A) := by rw [typedLift_carrier]; exact U.toGammaRVObject.lift_definable
  have hC : GammaSetDefinable B (carrier C) := by rw [typedLift_carrier]; exact V.toGammaRVObject.lift_definable
  let e' : GammaIso B (carrier A) (carrier C) := e.congr (typedLift_carrier UA.object.obj).symm (typedLift_carrier VA.object.obj).symm
  obtain ⟨Q,_⟩ := lemma_5_6_iso hκ.le hs h00 hreal δ hδ1 e'
  let D := unaryPartitionSource e' Q
  let E := unaryPartitionTarget e' Q
  have hD (i : Q.pieces) : GammaSetDefinable B (carrier (D i)) := Q.definable i.val i.property
  have hE (i : Q.pieces) : GammaSetDefinable B (carrier (E i)) :=
    (gammaRestrictionIso e' i.val (Q.subset i.val i.property) (Q.definable i.val i.property)).target_definable (gammaLogicInput B)
  have hDA (i : Q.pieces) : carrier (D i) ⊆ carrier A := Q.subset i.val i.property
  have hEC (i : Q.pieces) : carrier (E i) ⊆ carrier C := gammaRestrictionTarget_subset e' i.val (Q.subset i.val i.property)
  have hDdisj (i j : Q.pieces) (hij : i ≠ j) : Disjoint (carrier (D i)) (carrier (D j)) :=
    Q.disjoint i.val i.property j.val j.property (fun h => hij (Subtype.ext h))
  have hEdisj (i j : Q.pieces) (hij : i ≠ j) : Disjoint (carrier (E i)) (carrier (E j)) :=
    gammaRestrictionTarget_disjoint e' i.val j.val (Q.subset i.val i.property) (Q.subset j.val j.property) (hDdisj i j hij)
  obtain ⟨P⟩ := prepared_mixed_partition_exists (Nat.zero_lt_succ n) hs h00 hreal FBase A hA
    (typedLift_pullback UA.object.obj) D hD hDA hDdisj (unaryPartitionSource_cover e' Q)
  obtain ⟨R⟩ := prepared_mixed_partition_exists (Nat.zero_lt_succ n) hs h00 hreal FBase C hC
    (typedLift_pullback VA.object.obj) E hE hEC hEdisj (unaryPartitionTarget_cover e' Q)
  obtain ⟨hPF,HU⟩ := prepared_partition_blowup hκ.le hs h00 hreal UA D P
  obtain ⟨hRF,HV⟩ := prepared_partition_blowup hκ.le hs h00 hreal VA E R
  have hPΓ := GammaChainDefinable.target B P.special.chain P.gamma
  have hRΓ := GammaChainDefinable.target B R.special.chain R.gamma
  have hfinA : ∀ x : Fin (n+1) → VF (M := M),
      {r : Fin (rvObjectArity UA.object.obj) → RV (M := M) | (x,r) ∈ carrier A}.Finite := by
    intro x
    simpa only [A,typedLift_carrier] using finite_lift_fibres_of_finite_volume UA.object.obj UA.object.property x
  have hfinC : ∀ x : Fin (n+1) → VF (M := M),
      {r : Fin (rvObjectArity VA.object.obj) → RV (M := M) | (x,r) ∈ carrier C}.Finite := by
    intro x
    simpa only [C,typedLift_carrier] using finite_lift_fibres_of_finite_volume VA.object.obj VA.object.property x
  have hfinP := finite_rv_fibres_of_gamma_bijection hκ.le hs hreal P.special.toMap P.special.bijective
    (GammaChainDefinable.graph (gammaLogicInput B) P.special.chain P.gamma) hfinA
  have hfinR := finite_rv_fibres_of_gamma_bijection hκ.le hs hreal R.special.toMap R.special.bijective
    (GammaChainDefinable.graph (gammaLogicInput B) R.special.chain R.gamma) hfinC
  have H := gamma_pullback_partition_gluing hκ.le hs h00 hreal P.target R.target hPΓ hRΓ hPF hRF
    P.pieces R.pieces P.definable R.definable P.subset R.subset P.disjoint R.disjoint
    P.piecePullback R.piecePullback Finset.univ P.cover R.cover (fun i => by
      obtain ⟨t⟩ := unaryPartition_image_factor e' Q i
      let chain := (gammaUnaryChainInverse (P.unary i)).append (t.append (R.unary i))
      exact gamma_pullback_unary_chain_comparison hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58
        (P.pieces i) (R.pieces i) (P.definable i) (R.definable i) (P.piecePullback i) (R.piecePullback i)
        (fun x => (hfinP x).subset (fun r hr => P.subset i hr))
        (fun x => (hfinR x).subset (fun r hr => R.subset i hr))
        (pullback_finite_of_subset (P.subset i) hPF) (pullback_finite_of_subset (R.subset i) hRF) chain)
  exact GammaIsp.of_presented (Set.subset_univ _) (Set.subset_univ _) (HU.trans (H.trans HV.symm))

end IntegrationInACVF.Section6.FiniteRV
