import Integration7.GammaVolumeRowAgreements
import Integration7.VolumeSchemaCorrespondences

/-! Complete primitive row agreement preserves the derived volume
correspondence, including its full raw rows and improper-tuple behavior. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b d : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem schemaVolumeCorrespondence_rowAgreement
    {F : GammaFiniteRVSchema B p a d sp} {F' : GammaFiniteRVSchema B q a d sq}
    {G : GammaFiniteRVSchema B p b d sp} {G' : GammaFiniteRVSchema B q b d sq}
    {H : Set (Fin ((p+a)+b) → M)} {H' : Set (Fin ((q+a)+b) → M)}
    {z : Fin p → M} {t : Fin q → M}
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hF : GammaSchemaRowAgreement F z F' t) (hG : GammaSchemaRowAgreement G z G' t)
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔ Fin.append (Fin.append t x) y ∈ H')
    (r : Fin (d+d) → M) :
    Fin.append z r ∈ schemaVolumeCorrespondence F G H ↔
      Fin.append t r ∈ schemaVolumeCorrespondence F' G' H' := by
  let u := r ∘ Fin.castAdd d
  let v := r ∘ Fin.natAdd d
  have hr : Fin.append u v = r := Fin.append_castAdd_natAdd
  have hZ := (Fin.append_assoc z u v).symm
  have hT := (Fin.append_assoc t u v).symm
  rw [hr] at hZ hT
  have hSort : Fin.append z r ∈ sortedUniverse (Fin.append sp (fun _ : Fin (d+d) => .rv)) ↔
      Fin.append t r ∈ sortedUniverse (Fin.append sq (fun _ : Fin (d+d) => .rv)) := by
    constructor
    · intro hs i
      refine Fin.addCases (m := q) (n := d+d) (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using ht i
      · have h := hs (Fin.natAdd p i)
        simpa only [Fin.append_right] using h
    · intro hs i
      refine Fin.addCases (m := p) (n := d+d) (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using hz i
      · have h := hs (Fin.natAdd q i)
        simpa only [Fin.append_right] using h
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [hZ,hT,schemaVolumePairRelation_append,schemaVolumePairRelation_append]
  exact and_congr (exists_congr (fun x => exists_congr (fun y =>
    and_congr (hF.2 x u) (and_congr (hH x y) (hG.2 y v))))) hSort

end IntegrationInACVF.Section7
