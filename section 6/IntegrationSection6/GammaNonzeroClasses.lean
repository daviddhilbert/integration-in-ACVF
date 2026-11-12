import IntegrationSection6.FiniteGammaGradedSemiring
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

def GammaFullWeightAt (U : GammaObjectAt B S k) : Prop :=
  ∀ u : rvObjectDomain U.object.obj, @rvWeight M N k (@RVObject.value M N S k U.object.obj u) = k

theorem GammaFullWeightAt.iso {U V : GammaObjectAt B S k} (h : GammaFullWeightAt U) (e : GammaIsoAt U V) :
    GammaFullWeightAt V := by
  intro v
  let u := e.toGamma.equiv.symm v
  have hw := e.toGamma.weight u
  rw [Equiv.apply_symm_apply] at hw
  have hwu := rawWeight_eq_normalized_weight (gammaVolumeValue U.toGamma.toGammaRVObject u)
  have hwv := rawWeight_eq_normalized_weight (gammaVolumeValue V.toGamma.toGammaRVObject v)
  rw [hwu,hwv] at hw
  exact hw.symm.trans (h u)

theorem gammaFullWeightAt_empty (hBS : B.real ⊆ S) : GammaFullWeightAt (gammaEmptyAt (n := k) hBS) :=
  fun u => u.property.elim

theorem GammaFullWeightAt.coprod {U V : GammaObjectAt B S k} (hU : GammaFullWeightAt U) (hV : GammaFullWeightAt V) :
    GammaFullWeightAt (gammaCoprodAt U V) := by
  intro u
  rcases u.property with ⟨v,hv⟩ | ⟨v,hv⟩
  · have he : u = @rvCoprodLeftMap M N (@CanonicalStructure.normalized_model M sM hM) S k U.object.obj V.object.obj v := Subtype.ext hv.symm
    rw [he]
    exact (congrArg (@rvWeight M N k) (@rvCoprod_value_left M N (@CanonicalStructure.normalized_model M sM hM) S k U.object.obj V.object.obj v)).trans (hU v)
  · have he : u = @rvCoprodRightMap M N (@CanonicalStructure.normalized_model M sM hM) S k U.object.obj V.object.obj v := Subtype.ext hv.symm
    rw [he]
    exact (congrArg (@rvWeight M N k) (@rvCoprod_value_right M N (@CanonicalStructure.normalized_model M sM hM) S k U.object.obj V.object.obj v)).trans (hV v)

variable [hBS : Fact (B.real ⊆ S)]

def gammaNonzeroClassSubmonoidAt (k : ℕ) : AddSubmonoid (GammaIsoClassesAt B S k) where
  carrier := {a | ∃ U : GammaObjectAt B S k, gammaIsoClassAt U = a ∧ GammaFullWeightAt U}
  zero_mem' := ⟨gammaEmptyAt hBS.out,gammaIsoClassAt_empty hBS.out,gammaFullWeightAt_empty hBS.out⟩
  add_mem' := by
    rintro a b ⟨U,rfl,hU⟩ ⟨V,rfl,hV⟩
    exact ⟨gammaCoprodAt U V,gammaIsoClassAt_coprod U V,hU.coprod hV⟩

abbrev GammaNonzeroClassesAt (k : ℕ) := ↥(gammaNonzeroClassSubmonoidAt (B := B) (S := S) k)

theorem gammaNonzeroClassAt_iff (U : GammaObjectAt B S k) :
    gammaIsoClassAt U ∈ gammaNonzeroClassSubmonoidAt (B := B) (S := S) k ↔ GammaFullWeightAt U := by
  constructor
  · rintro ⟨V,he,hV⟩
    obtain ⟨e⟩ := gammaIsoClassAt_eq_iff.mp he
    exact hV.iso e
  · intro hU
    exact ⟨U,rfl,hU⟩

def gammaNonzeroClassAt (U : GammaObjectAt B S k) (hU : GammaFullWeightAt U) : GammaNonzeroClassesAt (B := B) (S := S) k :=
  ⟨gammaIsoClassAt U,(gammaNonzeroClassAt_iff U).mpr hU⟩

end IntegrationInACVF.Section6.FiniteRV
