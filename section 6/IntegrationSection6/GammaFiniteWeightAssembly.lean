import IntegrationSection6.GammaBinaryWeightAssembly
import IntegrationSection6.GammaPaddingClasses
import IntegrationSection6.GammaNonzeroGradedSemiring
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

variable [hBS : Fact (B.real ⊆ S)]

def gammaNonzeroDegreeZeroEquivAt :
    GammaNonzeroClassesAt (B := B) (S := S) 0 ≃+ GammaIsoClassesAt B S 0 :=
  AddEquiv.ofBijective (gammaNonzeroClassSubmonoidAt (B := B) (S := S) 0).subtype
    ⟨Subtype.val_injective,by
      intro a
      obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
      exact ⟨gammaNonzeroClassAt U (fun u => Nat.eq_zero_of_le_zero
        (@rvWeight_le_arity M N 0 (@RVObject.value M N S 0 U.object.obj u))),rfl⟩⟩

/-- The finite direct sum of nonzero-label pieces through degree k,
written recursively as products of additive monoids. -/
def GammaNonzeroThroughAt : ℕ → Type
  | 0 => GammaNonzeroClassesAt (B := B) (S := S) 0
  | n+1 => GammaNonzeroThroughAt n × GammaNonzeroClassesAt (B := B) (S := S) (n+1)

instance gammaNonzeroThroughAddCommMonoidAt : ∀ n, AddCommMonoid (GammaNonzeroThroughAt (B := B) (S := S) n)
  | 0 => inferInstanceAs (AddCommMonoid (GammaNonzeroClassesAt (B := B) (S := S) 0))
  | n+1 => by
    letI := gammaNonzeroThroughAddCommMonoidAt n
    exact inferInstanceAs (AddCommMonoid (GammaNonzeroThroughAt (B := B) (S := S) n × GammaNonzeroClassesAt (B := B) (S := S) (n+1)))

/-- The actual assembly map F_k, as an additive equivalence. -/
def gammaFiniteWeightAssemblyAt : ∀ n,
    GammaNonzeroThroughAt (B := B) (S := S) n ≃+ GammaIsoClassesAt B S n
  | 0 => gammaNonzeroDegreeZeroEquivAt
  | n+1 => ((gammaFiniteWeightAssemblyAt n).prodCongr (AddEquiv.refl _)).trans (gammaWeightAssembleStepEquivAt n)

def gammaNonzeroThroughInclusionAt (n : ℕ) :
    GammaNonzeroThroughAt (B := B) (S := S) n →+ GammaNonzeroThroughAt (B := B) (S := S) (n+1) where
  toFun a := (a,0)
  map_zero' := rfl
  map_add' _ _ := Prod.ext rfl (zero_add _).symm

theorem gammaFiniteWeightAssemblyAt_compatible (n : ℕ) (a : GammaNonzeroThroughAt (B := B) (S := S) n) :
    gammaFiniteWeightAssemblyAt (n+1) (gammaNonzeroThroughInclusionAt n a) =
      gammaPaddingClassesAt (gammaFiniteWeightAssemblyAt n a) := by
  simp [gammaFiniteWeightAssemblyAt,gammaNonzeroThroughInclusionAt,
    gammaWeightAssembleStepEquivAt,gammaWeightAssembleStepAt]
  change gammaPaddingClassesAt (gammaFiniteWeightAssemblyAt n a) + 0 = _
  exact add_zero _


end IntegrationInACVF.Section6.FiniteRV
