module

public import Integration7.OrdinaryFinitePointIsomorphisms
public import Integration7.GammaFiniteRowIsomorphismWitnesses

@[expose] public section

/-! An actual Gamma isomorphism of ordinary finite point rows promotes
to a finite formula witness with the specified endpoint schemata. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

theorem gamma_ordinary_point_formula_witness {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a 0 sp) (G : GammaFiniteRVSchema B p b 0 sp)
    (z : Fin p → M) (hF : F.valid z) (hG : G.valid z)
    (e : GammaIso ⟨B.real ∪ Set.range z,B.gamma⟩
      {q : Point (M := M) 0 a | q.2 ∈ F.rowDomain z}
      {q : Point (M := M) 0 b | q.2 ∈ G.rowDomain z}) :
    ∃ H : GammaRelationFormula B p a b sp, (gammaFiniteRowChartSchema F G H).valid z := by
  obtain ⟨P⟩ := F.realize z hF
  obtain ⟨Q⟩ := G.realize z hG
  exact gamma_finite_row_isomorphism_formula_witness hκ hs hreal hgamma F G z hF hG P Q
    (ordinaryFinitePointGammaIso P Q e)

end IntegrationInACVF.Section7
