module

public import Integration7.GammaFiniteRowIsomorphismWitnesses
public import IntegrationSection6.GammaSortedParameterPreservation

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Formula witnesses of finite-row isomorphisms uniformize to an
actual original-Gamma bijection of total sets fixing every parameter. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem gamma_finite_row_chart_uniformity {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp) (G : GammaFiniteRVSchema B p b k sp)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (hWitness : ∀ z ∈ A, ∃ H : GammaRelationFormula B p a b sp,
      (gammaFiniteRowChartSchema F G H).valid z) :
    ∃ e : GammaSortedIso B (Fin.append sp (fun _ : Fin a => .rv))
      (Fin.append sp (fun _ : Fin b => .rv)) (rawRowTotal A F.domain) (rawRowTotal A G.domain),
      ∀ u, (e.equiv u).val ∘ Fin.castAdd b = u.val ∘ Fin.castAdd a := by
  obtain ⟨C,hC⟩ := gamma_uniform_bijection_chart hκ hs hreal hgamma A hA
    F.domain_definable G.domain_definable (by
      intro z hz
      obtain ⟨H,hH⟩ := hWitness z hz
      exact ⟨⟨H.val,H.property⟩,hH.2.2.1⟩)
  exact ⟨gammaSortedTotalIso C hA G.domain_definable hC,
    gammaSortedTotalEquiv_prefix C G.domain_definable hC⟩

end IntegrationInACVF.Section7
