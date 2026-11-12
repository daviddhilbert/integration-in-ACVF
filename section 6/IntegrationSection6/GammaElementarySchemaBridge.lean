import IntegrationSection6.GammaElementaryFamilyRows
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
variable {B : Base (M := M)} {p a k : ℕ}

theorem GammaRVFamilyFormula.elementary_row_support (F : GammaRVFamilyFormula B p a k)
    (i : Fin k) (z : Fin p → VF (M := M)) (x : Fin (a+1) → RV (M := M))
    (y : Fin k → RV (M := M)) (h : (F.elementary i).rowVolume z x y) :
    x ∈ (F.elementary i).rowDomain z := by
  obtain ⟨r,⟨hd,_⟩,_⟩ := h
  exact hd

def GammaRVFamilyFormula.elementaryPresentation {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (F : GammaRVFamilyFormula B p a k)
    (z : Fin p → VF (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) (i : Fin k)
    (hAd : GammaAdmissible P.toGamma.toGammaRVObject i) :
    GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ (a+1) k
      ((F.elementary i).rowDomain z) ((F.elementary i).rowVolume z) := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩
  have hsmall : Cardinal.mk C.real < κ := small_union_range hκ B.real hreal (fun j => (z j).val)
  let E := @gammaFiniteElementaryBasic M sM hM C k κ hκ hs h00 hsmall P.toGamma i hAd
  refine {
    codes := P.codes
    real_contains := P.real_contains
    finite_extra := P.finite_extra
    domain := rvObjectDomain E.object
    domain_eq := Set.ext (fun x => (F.elementary_row_domain z P i x).symm)
    volume := rvObjectVolume E.object
    graph_iff := ?_
    finite_volume := E.finite_volume
    domain_graph := (F.elementary i).row_domain_definable z
    volume_graph := E.volume_graph }
  intro x y
  have he := F.elementary_row_graph z P i x y
  constructor
  · intro hxy
    have hr := he.mpr hxy
    exact ⟨F.elementary_row_support i z x y hr,hr⟩
  · exact fun hxy => he.mp hxy.2

theorem GammaRVFamilyFormula.exists_valid_elementary_schema {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVFamilyFormula B p a k) (z : Fin p → VF (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) (i : Fin k)
    (hAd : GammaAdmissible P.toGamma.toGammaRVObject i) :
    ∃ N : ℕ, ((F.elementary i).schema N).valid (fun j => (z j).val) := by
  let E := F.elementaryPresentation hκ hs h00 hreal z P i hAd
  exact (F.elementary i).exists_valid_schema hκ hs hreal hgamma z
    (F.elementary_row_support i z) E

end IntegrationInACVF.Section6
