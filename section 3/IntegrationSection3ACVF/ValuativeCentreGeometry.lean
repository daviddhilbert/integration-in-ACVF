import IntegrationSection3ACVF.PaperBalls
import IntegrationSection3ACVF.CanonicalBallSupport

/-! Existence and uniqueness of the valuative centre on actual ball point
sets. The constant-value step reuses the pinned predecessor's proved disc
geometry, and all values lie in its unchanged Gamma quotient. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.ValuativeCentreGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem valuativeCentre_unique {D : Set M} (hD : D ⊆ {x | iVF x})
    (hne : D.Nonempty) {c d : Values.GammaTop (M := M)}
    (hc : PaperBalls.HasValuativeCentre D c) (hd : PaperBalls.HasValuativeCentre D d) : c = d := by
  by_cases h0 : iVFZero ∈ D
  · rw [PaperBalls.HasValuativeCentre,if_pos h0] at hc hd
    exact hc.trans hd.symm
  · rw [PaperBalls.HasValuativeCentre,if_neg h0] at hc hd
    obtain ⟨x,hx⟩ := hne
    exact (hc ⟨x,hD hx⟩ hx).symm.trans (hd ⟨x,hD hx⟩ hx)

theorem valuativeCentre_exists {D : Set M} (hD : IsBall D) :
    ∃ c : Values.GammaTop (M := M), PaperBalls.HasValuativeCentre D c := by
  by_cases h0 : iVFZero ∈ D
  · exact ⟨Values.infinity,by rw [PaperBalls.HasValuativeCentre,if_pos h0]⟩
  · obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hΓ
    obtain ⟨a,r,he | he⟩ := SpecialTransformations.Section3.encodedBall_disc v hv D hD
    · have hn : (0 : VFType (M := M)) ∉ Balls.openDisc v a r := by
        intro hx
        exact h0 ((Set.ext_iff.mp he 0).mpr hx)
      refine ⟨Values.vfValueHom a,?_⟩
      rw [PaperBalls.HasValuativeCentre,if_neg h0]
      intro x hx
      exact (Values.vf_value_eq_iff v hv x a).mpr
        (Balls.openDisc_value_constant v a r hn x ((Set.ext_iff.mp he x).mp hx))
    · have hn : (0 : VFType (M := M)) ∉ Balls.closedDisc v a r := by
        intro hx
        exact h0 ((Set.ext_iff.mp he 0).mpr hx)
      refine ⟨Values.vfValueHom a,?_⟩
      rw [PaperBalls.HasValuativeCentre,if_neg h0]
      intro x hx
      exact (Values.vf_value_eq_iff v hv x a).mpr
        (Balls.closedDisc_value_constant v a r hn x ((Set.ext_iff.mp he x).mp hx))

end IntegrationInACVF.Section3ACVF.ValuativeCentreGeometry
