import IntegrationSection6.GammaSchemaIndexedPresentations
import IntegrationSection6.FiniteGammaEmptyIsomorphisms
import IntegrationSection6.FiniteGammaCommonBlowups
import IntegrationSection6.FiniteGammaUniversalCharts

/-! Indexed objects over an empty index domain are actually empty in the
finite Gamma category, at arbitrary fibre label arities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
open FiniteRV

theorem gammaIndexed_empty_isp {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ)
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (G : GammaFiniteRVSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hEmpty : ∀ t, t ∉ T)
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP) :
    GammaIspAt hκ hs h00 hreal (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma) := by
  have hP : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ
      (rvObjectDomain (gammaUniversalObject P.toGamma).object.obj) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hEmpty _ ((Set.ext_iff.mp P.domain_eq x).mp hx).1
  have hQ : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ
      (rvObjectDomain (gammaUniversalObject Q.toGamma).object.obj) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hEmpty _ ((Set.ext_iff.mp Q.domain_eq x).mp hx).1
  let eP := gammaEmptyIsoAt (gammaUniversalObject P.toGamma) hP
  let eQ := gammaEmptyIsoAt (gammaUniversalObject Q.toGamma) hQ
  exact ⟨0,0,gammaUniversalObject P.toGamma,gammaUniversalObject Q.toGamma,
    GammaIteratedBlowup.refl _,GammaIteratedBlowup.refl _,⟨eP.trans eQ.symm⟩⟩

end IntegrationInACVF.Section6
