import Integration7.HKConstrainedBijectionRealization
import Integration7.HKDensityLabelConstraints
import Integration7.GammaFiniteRowIsomorphismWitnesses

/-! A uniform family of exact-density finite row charts yields one
actual parameter-preserving bijection with the same density equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem finite_constrained_row_chart_uniformity {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp) (G : GammaFiniteRVSchema B p b k sp)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A) (δ : Fin a) (ε : Fin b)
    (hrow : ∀ z ∈ A, ∃ H : GammaRelationFormula B p a b sp,
      H.val ⊆ densityLabelConstraint sp δ ε ∧ (gammaFiniteRowChartSchema F G H).valid z) :
    ∃ e : GammaSortedIso B (Fin.append sp (fun _ : Fin a => .rv))
      (Fin.append sp (fun _ : Fin b => .rv)) (rawRowTotal A F.domain) (rawRowTotal A G.domain),
      (∀ u, (e.equiv u).val ∘ Fin.castAdd b = u.val ∘ Fin.castAdd a) ∧
      ∀ u, (e.equiv u).val (Fin.natAdd p ε) = u.val (Fin.natAdd p δ) := by
  obtain ⟨C,hCK,hC⟩ := uniform_bijection_chart_within hκ hs hr hg A hA
    F.domain_definable G.domain_definable (densityLabelConstraint sp δ ε) (by
      intro z hz
      obtain ⟨H,hHK,hH⟩ := hrow z hz
      exact ⟨⟨H.val,H.property⟩,hHK,hH.2.2.1⟩)
  refine ⟨gammaSortedTotalIso C hA G.domain_definable hC,
    gammaSortedTotalEquiv_prefix C G.domain_definable hC,?_⟩
  intro u
  have h := (constrained_total_graph C hA G.domain_definable hC _ hCK u).1
  simpa only [Fin.append_left,Fin.append_right,Function.comp_apply] using h.symm

end IntegrationInACVF.Section7.HK
