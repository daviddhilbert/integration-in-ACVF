import IntegrationSection6.DefinableFamilyCoefficients
import IntegrationSection6.MixedVFFibreCompactness

/-! Representative independence in6.20 follows from the actual varying
coefficient semirings and original-base fibre-bijection compactness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
variable (FBase : VFFieldBase B.real) (hB : VFGammaGeneratedBase B)
variable (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (h58 : Section5TwoOrderInputAll hκ hs)

theorem familyLiftDomain_fibre {a k : ℕ} (A : Set (Point (M := M) p 0))
    (F : GammaFiniteRVSchema B p a k) (x : A) :
    vfParameterFibre (familyLiftDomain A F) x.val.1 = schemaRowLift F x.val.1 := by
  ext q
  change ((Fin.append x.val.1 q.1 ∘ Fin.castAdd k,Fin.elim0) ∈ A ∧
    F.rowVolume (fun j => ((Fin.append x.val.1 q.1) (Fin.castAdd k j)).val) q.2
      (tupleRV (Fin.append x.val.1 q.1 ∘ Fin.natAdd p))) ↔
    F.rowVolume (fun j => (x.val.1 j).val) q.2 (tupleRV q.1)
  have hl : Fin.append x.val.1 q.1 ∘ Fin.castAdd k = x.val.1 := funext (fun j => Fin.append_left _ _ j)
  have ht : Fin.append x.val.1 q.1 ∘ Fin.natAdd p = q.1 := funext (fun j => Fin.append_right _ _ j)
  have hv : (fun j => ((Fin.append x.val.1 q.1) (Fin.castAdd k j)).val) =
      (fun j => (x.val.1 j).val) := funext (fun j => congrArg Subtype.val (Fin.append_left _ _ j))
  rw [hl,ht,hv]
  have hx : (x.val.1,Fin.elim0) ∈ A := by
    have he : (x.val.1,Fin.elim0) = x.val := Prod.ext rfl (Subsingleton.elim _ _)
    exact he.symm ▸ x.property
  exact and_iff_right hx

theorem gamma_family_lifts_iso {a b k l : ℕ} (A : Set (Point (M := M) p 0))
    (hA : GammaSetDefinable B A) (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b l)
    (hF : ∀ x : A, F.finiteRow (fun j => (x.val.1 j).val))
    (hG : ∀ x : A, G.finiteRow (fun j => (x.val.1 j).val))
    (he : ∀ x : A, schemaRowCoefficient hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 F x.val.1 (hF x) =
      schemaRowCoefficient hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 G x.val.1 (hG x)) :
    Nonempty (GammaIso B (familyLiftDomain A F) (familyLiftDomain A G)) := by
  apply gamma_mixed_fibre_compactness hκ hs hr hg A hA
    (familyLiftDomain A F) (familyLiftDomain A G)
    (gamma_family_lift_definable A hA F) (gamma_family_lift_definable A hA G)
    (fun q hq => hq.1) (fun q hq => hq.1)
  intro x
  obtain ⟨e⟩ := (schemaRowCoefficient_eq_iff hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 F G x.val.1 (hF x) (hG x)).mp (he x)
  exact ⟨e.congr (familyLiftDomain_fibre A F x).symm (familyLiftDomain_fibre A G x).symm⟩

def familyIntegralValue {a k : ℕ} (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) (hF : ∀ x : A, F.finiteRow (fun j => (x.val.1 j).val)) :
    GlobalIntegrationSemiringTarget hκ hs h00 hr FBase hg δ hδ hδ1 h58 hB :=
  globalAdditiveIntegrationToSemiring hκ hs h00 hr FBase hg δ hδ hδ1 h58 hB
    (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaFamilyLift A hA F hF))

theorem remark_6_20_representative_independence {a b k l : ℕ}
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b l)
    (hF : ∀ x : A, F.finiteRow (fun j => (x.val.1 j).val))
    (hG : ∀ x : A, G.finiteRow (fun j => (x.val.1 j).val))
    (he : ∀ x : A, schemaRowCoefficient hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 F x.val.1 (hF x) =
      schemaRowCoefficient hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 G x.val.1 (hG x)) :
    familyIntegralValue hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 A hA F hF =
      familyIntegralValue hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 A hA G hG := by
  obtain ⟨e⟩ := gamma_family_lifts_iso hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 A hA F G hF hG he
  exact congrArg (globalAdditiveIntegrationToSemiring hκ hs h00 hr FBase hg δ hδ hδ1 h58 hB)
    (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) ⟨e⟩)

end IntegrationInACVF.Section6
