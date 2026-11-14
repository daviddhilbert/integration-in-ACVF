import Integration7.HeadTangentDeterminant
import Integration7.RVVolumeMorphisms
import Section9.ResidueSimpleEquations

/-! A defined full Jacobian is the head Jacobian times the last-coordinate
ratio when the normalized correspondence has the actual free vertical line. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7 SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
local notation "RV" => CanonicalRV.RVSort M
local notation "K" => ModelResidue M

theorem normalizedCorrespondence_head_projection
    {C : Set (Fin ((k + 1) + (k + 1)) → RV)} {D : Set (Fin (k + k) → RV)}
    (hproj : ∀ z ∈ C, z ∘ headPairIndex k ∈ D) (t s : Fin (k + 1) → RV)
    (z : Fin ((k + 1) + (k + 1)) → K) (hz : z ∈ normalizedCorrespondence C t s) :
    z ∘ headPairIndex k ∈ normalizedCorrespondence D (t ∘ Fin.castSucc) (s ∘ Fin.castSucc) := by
  refine ⟨?_, fun i => hz.2 (headPairIndex k i)⟩
  have hr := hproj _ hz.1
  have he : residueScale (productTuple (t ∘ Fin.castSucc) (s ∘ Fin.castSucc)) (z ∘ headPairIndex k) =
      residueScale (productTuple t s) z ∘ headPairIndex k := by
    funext i
    exact congrArg (fun a => a * residueRV (z (headPairIndex k i)))
      (congrFun (productTuple_comp_headPairIndex t s) i).symm
  rw [he]
  exact hr

theorem rvJacobian_eq_head_mul_last_ratio
    {C : Set (Fin ((k + 1) + (k + 1)) → RV)} {D : Set (Fin (k + k) → RV)}
    (hproj : ∀ z ∈ C, z ∘ headPairIndex k ∈ D) {t s : Fin (k + 1) → RV}
    (hline : ∀ a : K, a ≠ 0 →
      productTuple (Fin.snoc (fun _ : Fin k => 1) a) (Fin.snoc (fun _ : Fin k => 1) a) ∈
        normalizedCorrespondence C t s)
    {ω J : RV} (hfull : IsRVJacobianAt C t s ω)
    (hhead : IsRVJacobianAt D (t ∘ Fin.castSucc) (s ∘ Fin.castSucc) J) :
    ω = J * (s (Fin.last k) / t (Fin.last k)) := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed K := ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  obtain ⟨_, _, _, L, hL, _, hω⟩ := hfull
  obtain ⟨_, _, _, H, hH, _, hJ⟩ := hhead
  have hd := residueJacobian_det_of_head
    (fun z hz => normalizedCorrespondence_head_projection hproj t s z hz) hline L H hL hH
  rw [hω, hd, hJ, Fin.prod_univ_castSucc s, Fin.prod_univ_castSucc t, ← div_mul_div_comm]
  ac_rfl

end IntegrationInACVF.Section7
