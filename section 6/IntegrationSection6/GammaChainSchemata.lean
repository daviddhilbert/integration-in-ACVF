import IntegrationSection6.GammaBlowupSchemata

/-! Finite formula witnesses for forward blowup chains, with their exact
length and every intermediate RV[k] object retained. Validity is a genuine
first-order locus over the original parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

inductive GammaFiniteChainSchema :
    {a b : ℕ} → GammaFiniteRVSchema B p a k sp → GammaFiniteRVSchema B p b k sp → ℕ → Type
  | iso {a b : ℕ} {U : GammaFiniteRVSchema B p a k sp} {V : GammaFiniteRVSchema B p b k sp}
      (chart : GammaFiniteRVIsoSchema B p a b k sp) : GammaFiniteChainSchema U V 0
  | step {a b c : ℕ} {U : GammaFiniteRVSchema B p a k sp} {V : GammaFiniteRVSchema B p b k sp}
      (W : GammaFiniteRVSchema B p c k sp) {r : ℕ}
      (head : GammaFiniteBlowupSchema U W) (tail : GammaFiniteChainSchema W V r) :
      GammaFiniteChainSchema U V (r+1)

variable {a b : ℕ} {U : GammaFiniteRVSchema B p a k sp} {V : GammaFiniteRVSchema B p b k sp} {r : ℕ}

def GammaFiniteChainSchema.valid :
    {a b : ℕ} → {U : GammaFiniteRVSchema B p a k sp} → {V : GammaFiniteRVSchema B p b k sp} →
      {r : ℕ} → GammaFiniteChainSchema U V r → (Fin p → M) → Prop
  | _, _, U, V, _, .iso chart, z => chart.valid z ∧ chart.source.sameRow U z ∧ chart.target.sameRow V z
  | _, _, _, _, _, .step W head tail, z => W.valid z ∧ head.valid z ∧ tail.valid z

theorem GammaFiniteChainSchema.valid_definable (H : GammaFiniteChainSchema U V r) :
    DefinableOverBase B sp {z | H.valid z} := by
  induction H with
  | iso chart =>
    exact chart.valid_definable.inter
      ((chart.source.sameRow_definable _).inter (chart.target.sameRow_definable _))
  | step W head tail ih => exact W.valid_definable.inter (head.valid_definable.inter ih)

end IntegrationInACVF.Section6
