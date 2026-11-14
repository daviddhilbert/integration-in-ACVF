import Integration7.GammaVolumeCoproductFormulas
import Integration7.GammaFunctionalRowRecognition

/-! The tagged coproduct density is a genuine function on its exact
domain. Existing RV zero/one tags give injectivity and disjointness. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaRVVolumeSchema.coprod_rowDensity_unique
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (z : Fin p → M) (hF : F.valid z) (hG : G.valid z)
    (w : (F.object.coprodFormula G.object).rowDomain z) :
    ∃! ω : Fin 1 → CanonicalRV.RVSort M, (F.coprodFormula G).rowDensity z w.val ω := by
  rcases (F.object.coprod_row_domain_formula G.object z hF.1.1 w.val).mp w.property with
    ⟨x,hx,htag⟩ | ⟨y,hy,htag⟩
  · obtain ⟨ω,hω,hu⟩ := F.rowDensity_unique z hF ⟨x,hx⟩
    refine ⟨ω,(F.coprod_rowDensity G z hF.1.1 w.val ω).mpr (Or.inl ⟨x,hω,htag⟩),?_⟩
    intro ω' hω'
    rcases (F.coprod_rowDensity G z hF.1.1 w.val ω').mp hω' with ⟨x',hx',htag'⟩ | ⟨y,hy,htag'⟩
    · have he : x' = x := @rvLeftTag_injective M N hN a b _ _ (htag'.trans htag.symm)
      subst x'
      exact hu ω' hx'
    · exact False.elim (@rvTag_disjoint M N hN a b x y (htag.trans htag'.symm))
  · obtain ⟨ω,hω,hu⟩ := G.rowDensity_unique z hG ⟨y,hy⟩
    refine ⟨ω,(F.coprod_rowDensity G z hF.1.1 w.val ω).mpr (Or.inr ⟨y,hω,htag⟩),?_⟩
    intro ω' hω'
    rcases (F.coprod_rowDensity G z hF.1.1 w.val ω').mp hω' with ⟨x,hx,htag'⟩ | ⟨y',hy',htag'⟩
    · exact False.elim (@rvTag_disjoint M N hN a b x y (htag'.trans htag.symm))
    · have he : y' = y := @rvRightTag_injective M N hN b a _ _ (htag'.trans htag.symm)
      subst y'
      exact hu ω' hy'

theorem GammaRVVolumeSchema.coprod_rowDensity_support
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (z : Fin p → M) (hF : F.valid z) (hG : G.valid z)
    (w : Fin (1+(a+b)) → CanonicalRV.RVSort M) (ω : Fin 1 → CanonicalRV.RVSort M)
    (h : (F.coprodFormula G).rowDensity z w ω) :
    w ∈ (F.object.coprodFormula G.object).rowDomain z := by
  apply (F.object.coprod_row_domain_formula G.object z hF.1.1 w).mpr
  rcases (F.coprod_rowDensity G z hF.1.1 w ω).mp h with ⟨x,hx,htag⟩ | ⟨y,hy,htag⟩
  · exact Or.inl ⟨x,F.rowDensity_support z hF x ω hx,htag⟩
  · exact Or.inr ⟨y,G.rowDensity_support z hG y ω hy,htag⟩

theorem GammaRVVolumeSchema.coprod_density_valid
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (z : Fin p → M) (hF : F.valid z) (hG : G.valid z) :
    functionMapRowValid sp (F.coprodFormula G).object.domain (F.coprodFormula G).density z :=
  functionMapRowValid_of_typed (F.coprodFormula G).object.domain_definable
    (F.coprodFormula G).density_definable z hF.1.1
    (fun w hw => F.coprod_rowDensity_unique G z hF hG ⟨w,hw⟩)
    (fun w ω h => F.coprod_rowDensity_support G z hF hG w ω h)

end IntegrationInACVF.Section7
