import Integration7.EssentialGammaWeight
import Integration7.RVProductGammaBalance

/-! Encode Gamma weight by the actual coordinate tuple followed by its
nonzero density. Equality of these products is equality in Gamma, with no
claim that the corresponding RV products are equal. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def volumeGammaWeightTuple (U : PositiveRVVolumeObject (M := M) S k)
    (u : U.essential.obj.domain) : Fin ((k+1)+1) → CanonicalRV.RVSort M :=
  Fin.snoc (U.essential.obj.value u) (U.essentialForm.value u)

theorem volumeGammaWeightTuple_nonzero (U : PositiveRVVolumeObject (M := M) S k)
    (u : U.essential.obj.domain) : ∀ i, (volumeGammaWeightTuple U u i).val ≠ iRVZero := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [volumeGammaWeightTuple,Fin.snoc_last] using
      (rv_nonzero_iff_raw _).mp (U.essentialForm_nonzero u)
  · simpa only [volumeGammaWeightTuple,Fin.snoc_castSucc] using U.essential_nonzero u j

theorem volumeGammaWeightTuple_absolute (U : PositiveRVVolumeObject (M := M) S k)
    (u : U.essential.obj.domain) :
    RVOperations.absoluteHom (∏ i, volumeGammaWeightTuple U u i) = essentialGammaWeight U u := by
  rw [Fin.prod_univ_castSucc]
  simp only [volumeGammaWeightTuple,Fin.snoc_castSucc,Fin.snoc_last,map_mul,map_prod,essentialGammaWeight]
  exact mul_comm _ _

theorem volumeGammaWeightTuple_gamma_iff
    (U V : PositiveRVVolumeObject (M := M) S k) (u : U.essential.obj.domain) (v : V.essential.obj.domain) :
    Values.vrv (∏ i, volumeGammaWeightTuple U u i) = Values.vrv (∏ i, volumeGammaWeightTuple V v i) ↔
      essentialGammaWeight U u = essentialGammaWeight V v := by
  constructor
  · intro h
    have ha := congrArg paperAbsoluteHom h
    simpa only [paperAbsoluteHom_vrv,volumeGammaWeightTuple_absolute] using ha
  · intro h
    apply (Values.paperValueEquiv (M := M)).injective
    change RVOperations.absoluteHom (∏ i, volumeGammaWeightTuple U u i) =
      RVOperations.absoluteHom (∏ i, volumeGammaWeightTuple V v i)
    rwa [volumeGammaWeightTuple_absolute,volumeGammaWeightTuple_absolute]

theorem volumeGammaWeightTuple_balance_iff
    (U V : PositiveRVVolumeObject (M := M) S k) (u : U.essential.obj.domain) (v : V.essential.obj.domain) :
    Fin.append (rvValues (volumeGammaWeightTuple U u)) (rvValues (volumeGammaWeightTuple V v)) ∈
      rvProductGammaBalance (M := M) ((k+1)+1) ↔ essentialGammaWeight U u = essentialGammaWeight V v := by
  rw [rvProductGammaBalance_append]
  exact ⟨fun h => (volumeGammaWeightTuple_gamma_iff U V u v).mp h.2.2,
    fun h => ⟨volumeGammaWeightTuple_nonzero U u,volumeGammaWeightTuple_nonzero V v,
      (volumeGammaWeightTuple_gamma_iff U V u v).mpr h⟩⟩

end IntegrationInACVF.Section7
