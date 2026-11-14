import Integration7.GammaVolumeSchemaRowEquality
import Integration7.GammaVolumeGraphPresentations
import IntegrationSection6.GammaGraphFormulaCongruence

/-! Replace equivalent domain, coordinate and density relations while
retaining the actual native presentation and its original-Gamma graphs. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a d : ℕ}
variable {D D' : Set (Fin a → RV (M := M))}
variable {R R' : (Fin a → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
variable {W W' : (Fin a → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}

def GammaVolumeGraphPresentation.congrFormula (P : GammaVolumeGraphPresentation B a d D R W)
    (hD : D = D') (hR : ∀ x t, R x t ↔ R' x t) (hW : ∀ x ω, W x ω ↔ W' x ω) :
    GammaVolumeGraphPresentation B a d D' R' W' := by
  cases hD
  exact {
    finite := P.finite.congrFormula rfl hR
    form := P.form
    density_iff := fun x ω => (P.density_iff x ω).trans (hW x ω)
    density_graph := GammaGraphDefinable.congr P.density_graph (fun x y => hW x.2 y.2) }

theorem GammaVolumeGraphPresentation.congrFormula_codes (P : GammaVolumeGraphPresentation B a d D R W)
    (hD : D = D') (hR : ∀ x t, R x t ↔ R' x t) (hW : ∀ x ω, W x ω ↔ W' x ω) :
    (P.congrFormula hD hR hW).finite.codes = P.finite.codes := by
  cases hD
  rfl

def GammaRVVolumeSchema.sameRowPresentation {p k : ℕ} {sp : Fin p → SortTag}
    (F G : GammaRVVolumeSchema B p a k sp) (z : Fin p → M) (h : F.sameRow G z)
    (P : GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1)
      (F.object.rowDomain z) (F.object.rowVolume z) (F.rowDensity z)) :
    GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1)
      (G.object.rowDomain z) (G.object.rowVolume z) (G.rowDensity z) :=
  P.congrFormula (F.object.sameRow_domains G.object h.1)
    (fun x t => h.1.2.2 (fun i => (x i).val) (fun i => (t i).val))
    (fun x ω => h.2.2.2 (fun i => (x i).val) (fun i => (ω i).val))

end IntegrationInACVF.Section7
