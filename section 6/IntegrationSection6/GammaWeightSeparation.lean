import IntegrationSection6.GammaWeightDecomposition
import IntegrationSection6.GammaFiniteRestrictionIsomorphisms
import IntegrationSection6.FiniteGammaLocusBlowups
import IntegrationSection6.GammaWeightStrata
import Mathlib.Algebra.DirectSum.Ring

/-! The graded semiring of actual original-Gamma RV[k] isomorphism
classes. This follows the pinned RVHomogeneousProducts/RVGradedSemiring
construction, using the finite Gamma structural maps proved here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gammaLeftLocus_mem_iff_low {n : ℕ} (U V : GammaObjectAt B S (n+1))
    (hU : @rvLowWeightProperty M N S n U.object.obj) (hV : GammaFullWeightAt V)
    (u : rvObjectDomain (gammaCoprodAt U V).object.obj) :
    u.val ∈ carrier (gammaLeftLocus U V) ↔
      @rvWeight M N (n+1) (@RVObject.value M N S (n+1) (gammaCoprodAt U V).object.obj u) ≤ n := by
  rcases u.property with ⟨v,hv⟩ | ⟨v,hv⟩
  · have he : u = @rvCoprodLeftMap M N (@CanonicalStructure.normalized_model M sM hM) S (n+1) U.object.obj V.object.obj v := Subtype.ext hv.symm
    have hm : u.val ∈ carrier (gammaLeftLocus U V) := ⟨v,hv⟩
    have hw := congrArg (@rvWeight M N (n+1)) (@rvCoprod_value_left M N (@CanonicalStructure.normalized_model M sM hM) S (n+1) U.object.obj V.object.obj v)
    rw [← he] at hw
    exact ⟨fun _ => hw.symm ▸ hU v,fun _ => hm⟩
  · have he : u = @rvCoprodRightMap M N (@CanonicalStructure.normalized_model M sM hM) S (n+1) U.object.obj V.object.obj v := Subtype.ext hv.symm
    have hm : u.val ∉ carrier (gammaLeftLocus U V) := by
      rintro ⟨w,hw⟩
      exact @rvTag_disjoint M N (@CanonicalStructure.normalized_model M sM hM) (rvObjectArity U.object.obj) (rvObjectArity V.object.obj) w.val v.val (hw.trans hv.symm)
    have hw := (congrArg (@rvWeight M N (n+1)) (@rvCoprod_value_right M N (@CanonicalStructure.normalized_model M sM hM) S (n+1) U.object.obj V.object.obj v)).trans (hV v)
    rw [← he] at hw
    constructor
    · intro h
      exact (hm h).elim
    · intro h
      exact ((Nat.not_succ_le_self n) (hw.ge.trans h)).elim

theorem gammaIsoAt_normalized_weight {U V : GammaObjectAt B S k} (e : GammaIsoAt U V)
    (u : rvObjectDomain U.object.obj) :
    @rvWeight M N k (@RVObject.value M N S k U.object.obj u) =
      @rvWeight M N k (@RVObject.value M N S k V.object.obj (isoAtMap e.iso u)) :=
  (rawWeight_eq_normalized_weight (gammaVolumeValue U.toGamma.toGammaRVObject u)).symm.trans
    ((e.toGamma.weight u).trans (rawWeight_eq_normalized_weight (gammaVolumeValue V.toGamma.toGammaRVObject (e.toGamma.equiv u))))

end IntegrationInACVF.Section6.FiniteRV
