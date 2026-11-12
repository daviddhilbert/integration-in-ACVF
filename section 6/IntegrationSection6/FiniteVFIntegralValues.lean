import IntegrationSection6.FiniteIntegrationTarget
import Section5.GammaSurjectivity
import Section7.GammaScissors

/-! The representative-independent integration value of an actual VF[k]
object with finite RV fibres. Representatives come from the checked5.7
surjectivity theorem; independence uses the proved6.17 kernel implication. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

abbrev GammaVFFiniteObject (B : Base (M := M)) (k : ℕ) := {A : GammaVFObject B k // A.finiteFibres}

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)

include hκ hs h00 hreal FBase in
theorem finiteVFLiftRepresentative_exists (A : GammaVFFiniteObject B k) :
    Nonempty (Σ U : GammaRVFiniteObject B k, GammaIso B A.val.domain U.lift) := by
  obtain ⟨U,⟨e⟩⟩ := SpecialTransformations.Section5.Paper.corollary_5_7_finite_gamma
    hκ hs h00 B hreal FBase A.val.domain A.val.definable A.val.dimension A.property
  exact ⟨⟨U,e⟩⟩

def finiteVFLiftRepresentative (A : GammaVFFiniteObject B k) :
    Σ U : GammaRVFiniteObject B k, GammaIso B A.val.domain U.lift :=
  Classical.choice (finiteVFLiftRepresentative_exists hκ hs h00 hreal FBase A)

def vfIntegralValue (A : GammaVFFiniteObject B k) : IntegrationTarget hκ hs h00 hreal k :=
  rvIntegralClass hκ hs h00 hreal (finiteVFLiftRepresentative hκ hs h00 hreal FBase A).1

variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (h58 : Section5TwoOrderInputAll hκ hs)

include hgamma δ hδ hδ1 h58 in
theorem vfIntegralValue_of_lift_representation (A : GammaVFFiniteObject B k) (U : GammaRVFiniteObject B k)
    (e : GammaIso B A.val.domain U.lift) :
    vfIntegralValue hκ hs h00 hreal FBase A = rvIntegralClass hκ hs h00 hreal U := by
  let R := finiteVFLiftRepresentative hκ hs h00 hreal FBase A
  have f := (e.symm (gammaLogicInput B)).trans (gammaLogicInput B) R.2
  exact ((rvIntegralClass_eq_iff hκ hs h00 hreal U R.1).mpr
    (lemma_6_17_kernel hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58 U R.1 f)).symm

include hgamma δ hδ hδ1 h58 in
theorem vfIntegralValue_iso {A C : GammaVFFiniteObject B k} (e : GammaIso B A.val.domain C.val.domain) :
    vfIntegralValue hκ hs h00 hreal FBase A = vfIntegralValue hκ hs h00 hreal FBase C := by
  let R := finiteVFLiftRepresentative hκ hs h00 hreal FBase A
  let T := finiteVFLiftRepresentative hκ hs h00 hreal FBase C
  let f := ((R.2.symm (gammaLogicInput B)).trans (gammaLogicInput B) e).trans (gammaLogicInput B) T.2
  exact (rvIntegralClass_eq_iff hκ hs h00 hreal R.1 T.1).mpr
    (lemma_6_17_kernel hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58 R.1 T.1 f)

end IntegrationInACVF.Section6.FiniteRV
