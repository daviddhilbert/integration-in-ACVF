import IntegrationSection6.GammaRawElementaryNativeRows
import IntegrationSection6.GammaAdmissibilitySchemata
import IntegrationSection6.GammaFiniteElementary

/-! The uniform elementary family has valid finite schema rows whenever
the represented center row is admissible. The actual native elementary
object supplies the presentation, keeping the center's internal codes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

theorem GammaFiniteRVSchema.elementary_row_support (F : GammaFiniteRVSchema B p a k sp)
    (i : Fin k) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j)) (x : Fin (a+1) → RV (M := M))
    (y : Fin k → RV (M := M)) (h : (F.elementaryFormula i).rowVolume z x y) :
    x ∈ (F.elementaryFormula i).rowDomain z := by
  exact ((F.elementary_row_volume_formula i z hz x y).mp h).1

def GammaFiniteRVSchema.elementaryPresentation {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) (i : Fin k)
    (hAd : GammaAdmissible P.toGamma.toGammaRVObject i) :
    GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ (a+1) k
      ((F.elementaryFormula i).rowDomain z) ((F.elementaryFormula i).rowVolume z) := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range z,B.gamma⟩
  have hsmall : Cardinal.mk C.real < κ := small_union_range hκ B.real hreal z
  let E := @gammaFiniteElementaryBasic M sM hM C k κ hκ hs h00 hsmall P.toGamma i hAd
  refine {
    codes := P.codes
    real_contains := P.real_contains
    finite_extra := P.finite_extra
    domain := rvObjectDomain E.object
    domain_eq := Set.ext (fun x => (F.elementary_row_domain z hz P i x).symm)
    volume := rvObjectVolume E.object
    graph_iff := ?_
    finite_volume := E.finite_volume
    domain_graph := by
      have hD : GammaSetDefinable C {x : Point (M := M) 0 (a+1) |
          x.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M
            (@CanonicalStructure.normalize M sM) _ P.codes (rvObjectDomain E.object)} := E.domain_graph
      convert hD using 1
      apply Set.ext
      intro x
      exact F.elementary_row_domain z hz P i x.2
    volume_graph := E.volume_graph }
  intro x y
  have he := F.elementary_row_graph z hz P i x y
  constructor
  · intro hxy
    have hr := he.mpr hxy
    exact ⟨F.elementary_row_support i z hz x y hr,hr⟩
  · exact fun hxy => he.mp hxy.2

theorem GammaFiniteRVSchema.exists_valid_elementary_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) (i : Fin k)
    (hAd : GammaAdmissible P.toGamma.toGammaRVObject i) :
    ∃ bound : ℕ, ((F.elementaryFormula i).withBound bound).valid z := by
  let E := F.elementaryPresentation hκ hs h00 hreal z hz P i hAd
  exact (F.elementaryFormula i).exists_valid_bound hκ hs hreal hgamma z hz
    (F.elementary_row_support i z hz) E

end IntegrationInACVF.Section6
