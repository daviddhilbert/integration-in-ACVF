import IntegrationSection5.UnaryCoordinateReduction
import IntegrationSection5.GammaUnaryPartitionGlue

/-! The finite-coordinate induction for Lemma5.6. Every refinement,
partition and actual relatively unary factor is constructed internally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {p m w : ℕ}
variable {A : Set (Point (M := M) (p+1) m)} {B : Set (Point (M := M) (p+1) w)}

theorem gamma_unary_partition_fixed {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) (F : Finset (Fin (p+1)))
    (e : GammaIso G A B)
    (hfix : ∀ a : A, ∀ j : Fin (p+1), j ∉ F → (e.equiv a).val.1 j = a.val.1 j) :
    Nonempty (GammaUnaryPartition e) := by
  induction F using Finset.strongInductionOn generalizing m w A B with
  | _ F ih =>
    by_cases hF : F.Nonempty
    · obtain ⟨i,hi⟩ := hF
      obtain ⟨P⟩ := coordinate_injective_iso_partition hκ hs h00 hsmall δ hδ (Nat.zero_lt_succ p) e i
      have hex (k : Option (Fin (p+1))) :
          Nonempty (GammaUnaryPartition (gammaRestrictionIso e (P.pieces k) (P.subset k) (P.definable k))) := by
        obtain ⟨R⟩ := coordinate_piece_reduction e i P F hi hfix k
        have hlt : F.erase R.coordinate ⊂ F := Finset.erase_ssubset R.coordinate_mem
        obtain ⟨Q⟩ := ih (F.erase R.coordinate) hlt R.remainder R.fixed
        exact GammaUnaryPartition.prepend
          (gammaRestrictionIso e (P.pieces k) (P.subset k) (P.definable k))
          R.chain R.remainder R.commutes Q
      let Q := fun k => Classical.choice (hex k)
      exact GammaUnaryPartition.glue e P.pieces P.definable P.subset P.disjoint P.cover Q
    · have hEmpty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      apply GammaUnaryPartition.ofUnary e 0
      intro a j _
      apply hfix a j
      rw [hEmpty]
      exact Finset.notMem_empty j

/-- Lemma5.6's Gamma partition and actual factor chains, for positive VF arity. -/
theorem gamma_unary_partition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) (e : GammaIso G A B) :
    Nonempty (GammaUnaryPartition e) :=
  gamma_unary_partition_fixed hκ hs h00 hsmall δ hδ Finset.univ e
    (fun _ j hj => (hj (Finset.mem_univ j)).elim)

end IntegrationInACVF.Section5
