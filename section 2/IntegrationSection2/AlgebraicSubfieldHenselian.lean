import IntegrationSection2.ValuedSubfieldRestriction
import IntegrationSection2.AlgebraicEnvelopeBases
import IntegrationSection2.HenselianAlgebraicTower
import Section9.GaussExtension

/-! Algebraic extensions of henselian subfields inside the actual
algebraically closed valued ambient field are henselian in residue
characteristic zero. The algebraic envelope and both Galois instances
are constructed, rather than assumed for the original ambient field. -/

set_option backward.isDefEq.respectTransparency false

open IsLocalRing IntermediateField
open SpecialTransformations.Section9

namespace IntegrationInACVF.Section2.AlgebraicSubfieldHenselian

variable {K Γ : Type} [Field K] [IsAlgClosed K] [CharZero K]
  [LinearOrderedCommGroupWithZero Γ]

theorem algebraic_henselian (v : Valuation K Γ) (F E : Subfield K)
    [HenselianLocalRing (v.comap F.subtype).valuationSubring]
    [CharZero (ResidueField v.valuationSubring)] (hFE : F ≤ E)
    (hE : ∀ x : K, x ∈ E → IsAlgebraic F x) :
    HenselianLocalRing (v.comap E.subtype).valuationSubring := by
  let C : IntermediateField F K := algebraicClosure F K
  letI : IsAlgClosed C := IsAlgClosure.isAlgClosed F
  have hFC : F ≤ C.toSubfield := by
    intro x hx
    exact C.algebraMap_mem ⟨x,hx⟩
  have hEC : E ≤ C.toSubfield := by
    intro x hx
    exact mem_algebraicClosure_iff.mpr (hE x hx)
  let w := v.comap C.toSubfield.subtype
  let F' := F.comap C.toSubfield.subtype
  let E' := E.comap C.toSubfield.subtype
  letI : IsGalois F' C := AlgebraicEnvelopeBases.galois_comap F C F le_rfl
  letI : IsGalois E' C := AlgebraicEnvelopeBases.galois_comap F C E hFE
  letI : HenselianLocalRing (w.comap F'.subtype).valuationSubring :=
    (ValuedSubfieldRestriction.henselian_iff v C.toSubfield F hFC).mpr inferInstance
  letI : CharZero (ResidueField w.valuationSubring) := residueCharZero_of_subfield v C.toSubfield
  apply (ValuedSubfieldRestriction.henselian_iff v C.toSubfield E hEC).mp
  exact HenselianAlgebraicTower.henselian_intermediate w F' E' (fun _ hx => hFE hx)

end IntegrationInACVF.Section2.AlgebraicSubfieldHenselian
