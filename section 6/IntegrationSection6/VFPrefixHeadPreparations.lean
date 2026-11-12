import IntegrationSection6.VFPrefixSpecialRestriction
import IntegrationSection6.VFPrefixHeadImages
import IntegrationSection6.GammaVFPrefixFibreMaps

/-! Actual head preparations restrict to any active VF prefix after a
complementary tuple is fixed. Their contracted sets are exactly the frozen
fibres of the original contracted set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n p a : ℕ}
variable {U : DefSet (M := M) S (n+(p+1)) a}

def vfPrefixHeadPreparation (T : HeadPreparation U) (x : Fin n → VF (M := M)) :
    HeadPreparation (vfPrefixFibre (n := n) (p := p+1) U x) where
  arity := T.arity
  target := vfPrefixFibre (n := n) (p := p+1) T.target x
  map := vfPrefixFibreMap (n := n) (p := p+1) T.map (vfPrefixRelative_of_unaryHead T.map T.special.choose) x
  special := specialRelative_vfPrefix T.map T.special x
  saturated := by
    intro q hq z hz
    change vfPrefixInsert (n := n) (p := p+1) x (replace 0 q z) ∈ carrier T.target
    rw [vfPrefixInsert_replace]
    exact T.saturated (vfPrefixInsert (n := n) (p := p+1) x q) hq z
      (hz.trans (congrArg (@rv M sM hM) (vfPrefixTuple_head x q.1 0)).symm)

theorem vfPrefixHeadPreparation_contracted (T : HeadPreparation U) (x : Fin n → VF (M := M)) :
    (vfPrefixHeadPreparation T x).contractedSet = vfPrefixFibre (n := n) (p := p) T.contractedSet x :=
  defSet_eq_of_carrier_eq (vfPrefixFibre_headImage (n := n) (p := p) T.target x)

theorem gamma_vfPrefixHeadPreparation_map (T : HeadPreparation U)
    (hT : GammaGraphDefinable B (pointMapGraph T.map)) (x : Fin n → VF (M := M)) :
    GammaGraphDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
      (pointMapGraph (vfPrefixHeadPreparation T x).map) :=
  gamma_vfPrefixFibreMap (n := n) (p := p+1) T.map hT
    (vfPrefixRelative_of_unaryHead T.map T.special.choose) x

theorem gamma_vfPrefixHeadPreparation_target (T : HeadPreparation U)
    (hT : GammaSetDefinable B (carrier T.target)) (x : Fin n → VF (M := M)) :
    GammaSetDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
      (carrier (vfPrefixHeadPreparation T x).target) :=
  gamma_vfPrefixFibre (n := n) (p := p+1) T.target hT x

end IntegrationInACVF.Section6
