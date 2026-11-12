import IntegrationSection6.ElementaryBlowup

/-! Finite volume of an elementary blowup needs only finite old-label
slices. This separates the finite-category proof from the original-base
argument supplying those slices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

theorem elementary_finite_volume_of_slices
    (U : RVObject (M := M) S k) (i : Fin k) (h : Admissible U i)
    (hf : ∀ t : Fin k → CanonicalRV.RVSort M,
      {r | (∃ u : U.domain, U.value u = r) ∧ ∀ j, j ≠ i → r j = t j}.Finite)
    (hU : U.volume.FiniteFibres) : (elementary U i).volume.FiniteFibres := by
  intro t
  let R := {r | (∃ u : U.domain, U.value u = r) ∧ ∀ j, j ≠ i → r j = t.val j}
  have hR : R.Finite := hf t.val
  have hF (r : Fin k → CanonicalRV.RVSort M) :
      {u : U.domain | U.value u = r}.Finite := by
    apply (hU ⟨r, Set.mem_univ _⟩).subset
    intro u hu
    exact Subtype.ext hu
  have hB := hR.biUnion (fun r _ => hF r)
  apply hB.of_injOn (f := elementaryProjection U i)
  · intro a ha
    refine Set.mem_iUnion.mpr ⟨U.value (elementaryProjection U i a),
      Set.mem_iUnion.mpr ⟨?_, rfl⟩⟩
    refine ⟨⟨elementaryProjection U i a, rfl⟩, ?_⟩
    intro j hj
    have he := congrFun (congrArg Subtype.val ha) j
    change (elementary U i).value a j = t.val j at he
    simpa only [elementary_value, blowupValue_other i _ _ j hj] using he
  · intro a ha b hb hab
    have hlabels := congrFun (congrArg Subtype.val (ha.trans hb.symm)) i
    change (elementary U i).value a i = (elementary U i).value b i at hlabels
    rw [elementary_value, elementary_value, blowupValue_same, blowupValue_same,
      ← hab] at hlabels
    have hn : U.value (elementaryProjection U i a) i ≠ 0 := by
      intro hz
      apply h.nonzero (elementaryProjection U i a)
      rw [hz, RVOperations.zero_val]
    have hp := mul_right_cancel₀ hn hlabels
    have he : rvUnpack U.domain (positiveRV S) a =
        rvUnpack U.domain (positiveRV S) b := by
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Subtype.val hab
      · funext j
        fin_cases j
        exact hp
    have he' := congrArg (rvPack U.domain (positiveRV S)).toImage he
    simpa only [rvPack_unpack] using he'


end IntegrationInACVF.Section6
