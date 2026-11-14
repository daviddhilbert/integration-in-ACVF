import Integration7.CanonicalFiniteRVObjects
import Integration7.ElementaryBlowupConstruction
import IntegrationSection6.NormalizedLifts
import IntegrationSection6.NormalizedFocus
import IntegrationSection6.AdmissibleFocusRelabeling
import Section3.CanonicalParameters

/-! Literal lift presentations and admissibility transfer with the
actual canonical RV objects, over precisely the same real parameter set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 (rv carrier)
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem canonicalRVObject_presentsLift (hc : CanonicalStructure.IsCanonical (M := M))
    {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (@RVObject.arity M N S n U)}
    (h : @Section6.PresentsLift M N hN S n U (Section6.normalizedPointSet A)) :
    Section6.PresentsLift (canonicalRVObject hc U) A := by
  intro p
  constructor
  · intro hp
    obtain ⟨u,hu,hv⟩ := (h p).mp hp
    refine ⟨⟨u.val,u.property⟩,hu,?_⟩
    exact hv.trans (funext (fun i => Section6.rv_normalize (p.1 i)))
  · rintro ⟨u,hu,hv⟩
    apply (h p).mpr
    refine ⟨⟨u.val,u.property⟩,hu,?_⟩
    exact hv.trans (funext (fun i => (Section6.rv_normalize (p.1 i)).symm))

theorem canonicalRVObject_admissible (hc : CanonicalStructure.IsCanonical (M := M))
    {U : @RVObject M N S n} (i : Fin n) (h : @Section6.Admissible M N S n U i) :
    Section6.Admissible (canonicalRVObject hc U) i := by
  constructor
  · intro u
    exact @Section6.Admissible.nonzero M N S n U i h ⟨u.val,u.property⟩
  · intro u
    exact (algebraicAt_normalize_iff _ .rv _).mp (@Section6.Admissible.algebraic M N S n U i h ⟨u.val,u.property⟩)

theorem canonicalRVObject_blowupAdmissible (hc : CanonicalStructure.IsCanonical (M := M))
    {k : ℕ} (U : @RVFiniteObject M N S (k+1))
    (h : @Section6.Admissible M N S (k+1) U.obj (Fin.last k))
    (ω : VolumeForm (canonicalFiniteRVObject hc U).obj.domain) :
    BlowupAdmissible (⟨canonicalFiniteRVObject hc U,ω⟩ : PositiveRVVolumeObject (M := M) S k) := by
  have hA := canonicalRVObject_admissible hc (Fin.last k) h
  exact ⟨hA.rv_nonzero,hA.algebraic⟩

end IntegrationInACVF.Section7
