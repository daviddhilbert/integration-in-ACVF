import IntegrationSection6.GammaVFSelectedSourceFibres
import IntegrationSection6.FiniteSelectedContractions

/-! Actual finite selected-volume contractions of a mixed set presented
by a finite VF-parameter family. Relative finiteness and the source Gamma
certificate are derived from the presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {R : Set M} {p a k : ℕ}

theorem schemaSource_gamma (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) (U : DefSet (M := M) R p a)
    (hSource : carrier U = vfSchemaSource A F) : GammaSetDefinable B (carrier U) :=
  Eq.mpr (congrArg (fun E : Set (Point (M := M) p a) => GammaSetDefinable B E) hSource)
    (gamma_vf_schema_source_definable A hA F)

theorem schemaSource_selected_fibres (A : Set (Point (M := M) p 0))
    (F : GammaFiniteRVSchema B p a k) (ρ : Fin k → Fin a)
    (hF : ∀ b : A, F.finiteRow (rawVFParameter b.val))
    (hLabels : ∀ b : A, ∀ r y, F.rowVolume (rawVFParameter b.val) r y ↔
      r ∈ F.rowDomain (rawVFParameter b.val) ∧ r ∘ ρ = y)
    (U : DefSet (M := M) R p a) (hSource : carrier U = vfSchemaSource A F) :
    ∀ (x : Fin p → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite := by
  rw [hSource]
  exact vfSchemaSource_selected_fibres A F ρ hF hLabels

def gammaFiniteSchemaContraction {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hBR : B.real ⊆ R)
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) (ρ : Fin k → Fin a)
    (hF : ∀ b : A, F.finiteRow (rawVFParameter b.val))
    (hLabels : ∀ b : A, ∀ r y, F.rowVolume (rawVFParameter b.val) r y ↔
      r ∈ F.rowDomain (rawVFParameter b.val) ∧ r ∘ ρ = y)
    (U : DefSet (M := M) R p a) (hSource : carrier U = vfSchemaSource A F)
    {σ : Equiv.Perm (Fin p)} (T : StandardContraction U σ) (hT : GammaProgramDefinable B T.program) :
    GammaRVFiniteObject B (p+k) :=
  FiniteRV.gammaFiniteSelectedContraction hκ hs hreal hBR (schemaSource_gamma A hA F U hSource) ρ
    (schemaSource_selected_fibres A F ρ hF hLabels U hSource) T hT

end IntegrationInACVF.Section6
