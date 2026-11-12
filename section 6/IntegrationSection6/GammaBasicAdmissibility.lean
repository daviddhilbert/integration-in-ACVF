import IntegrationSection6.FiniteGammaBasicFactors
import IntegrationSection6.GammaAdmissibility

/-! The global RV unit is algebraic over every original Gamma base.
The singleton degree-one factor is therefore genuinely admissible. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem normalized_rv_one : @iRVOne M N = @iRVOne M sM :=
  @CanonicalStructure.normalize_fun M sM 0 Fn.rvOne Fin.elim0 (fun j => j.elim0)

theorem gamma_rv_one_algebraic (B : Base (M := M)) : AlgebraicAtBase B .rv (iRVOne (M := M)) := by
  let R := B.real
  have hraw : @Set.Definable M R LRV N (Fin 1) {z | z 0 = @iRVOne M sM} := by
    letI := N
    letI := hN
    have hc := rvConstantCode_definable (M := M) R (ι := Fin 1) true
    have hp := (Set.DefinableFun.proj (M := M) (L := LRV) (A := R) (i := (0 : Fin 1))).ofPred_eq hc
    simpa only [ite_true,normalized_rv_one (sM := sM)] using hp
  have hd : DefinableAt B.real .rv {iRVOne (M := M)} := by
    apply (definableAt_iff_normalized_raw B.real .rv _).mpr
    refine ⟨hraw,?_⟩
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact SpecialTransformations.Milestone0.Transfer.rv_one_mem hM
  exact ⟨{iRVOne},real_definableAtBase B .rv _ hd,Set.finite_singleton _,Set.mem_singleton _⟩

namespace FiniteRV
variable {B : Base (M := M)} {S : Set M}

theorem gammaOneAt_volume (hBS : B.real ⊆ S)
    (u : rvObjectDomain (gammaOneAt hBS).object.obj) (j : Fin 1) :
    (gammaVolumeValue (gammaOneAt hBS).toGamma.toGammaRVObject u j).val = iRVOne := by
  letI := N
  letI := hN
  change (1 : @CanonicalRV.RVSort M N).val = @iRVOne M sM
  rw [@RVOperations.one_val M N hN]
  exact @normalized_rv_one M sM hM

theorem gammaOneAt_admissible (hBS : B.real ⊆ S) :
    GammaAdmissible (gammaOneAt hBS).toGamma.toGammaRVObject 0 where
  nonzero u := by
    rw [gammaOneAt_volume]
    exact RVCalc.rv_one_ne_zero hM
  algebraic u := by
    rw [gammaOneAt_volume]
    exact (gamma_rv_one_algebraic B).mono (C := ⟨coordinateBase B.real 0
      (gammaVolumeValue (gammaOneAt hBS).toGamma.toGammaRVObject u),B.gamma⟩)
      Set.subset_union_left (Set.Subset.refl _)

end FiniteRV
end IntegrationInACVF.Section6
