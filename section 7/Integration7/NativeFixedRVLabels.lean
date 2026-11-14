import Integration7.RVLabelChainLifts
import Integration7.GammaRVLabelFocusLifts
import IntegrationSection6.GammaRawRVFormulas

/-! Actual native graphs of fixed RV label tuples. They project
bijectively onto the original domain and retain the original Gamma base
when the tuple singleton has a certificate over that base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a d : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def appendFixedRVLabelsMap (A : DefSet (M := M) S n a) (t : Fin d → RV (M := M))
    (ht : ∀ i, (t i).val ∈ S) : Map A (PresentedSet.univ (pointSpace n (a+d)) S) :=
  Map.ofCodes A (fun p => (p.1,Fin.append p.2 t))
    (fun z => Sum.elim (fun i => z (.inl i))
      (Fin.addCases (fun i => z (.inr i)) (fun i => (t i).val)))
    (by
      intro i
      cases i with
      | inl i => exact rawProj S (.inl i : Fin n ⊕ Fin a)
      | inr i =>
        cases i using Fin.addCases with
        | left j => simpa only [Sum.elim_inr,Fin.addCases_left] using (rawProj S (.inr j : Fin n ⊕ Fin a))
        | right j =>
          letI : LRV.Structure M := N
          simpa only [Sum.elim_inr,Fin.addCases_right] using (LRV.definableFun_const _ (ht j)))
    (by
      intro c
      refine ⟨c.property.1,?_⟩
      intro i
      cases i using Fin.addCases with
      | left j => simpa only [Function.comp_apply,Sum.elim_inr,Fin.addCases_left] using c.property.2 j
      | right j =>
          simpa only [Function.comp_apply,Sum.elim_inr,Fin.addCases_right] using
            ((@CanonicalStructure.sortEval_normalize M sM .rv _).mp (t j).property))
    (by
      intro c
      refine Prod.ext rfl ?_
      funext i
      apply Subtype.ext
      change Fin.addCases (fun j => c.val (.inr j)) (fun j => (t j).val) i =
        (Fin.append (pDecode (pointSpace n a) c).2 t i).val
      cases i using Fin.addCases <;>
        simp only [Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right] <;> rfl)

def fixedRVLabelDomain (A : DefSet (M := M) S n a) (t : Fin d → RV (M := M))
    (ht : ∀ i, (t i).val ∈ S) : DefSet (M := M) S n (a+d) := Map.image (appendFixedRVLabelsMap A t ht)

theorem retain_fixed_rv_labels (A : DefSet (M := M) S n a) (t : Fin d → RV (M := M))
    (ht : ∀ i, (t i).val ∈ S) (p : A) :
    retainVFLabels (Fin.castAdd d) (appendFixedRVLabelsMap A t ht p).val = p.val := by
  refine Prod.ext rfl ?_
  funext i
  exact Fin.append_left _ _ i

theorem fixed_rv_label_domain_carrier (A : DefSet (M := M) S n a) (t : Fin d → RV (M := M))
    (ht : ∀ i, (t i).val ∈ S) (p : Point (M := M) n (a+d)) :
    p ∈ carrier (fixedRVLabelDomain A t ht) ↔
      retainVFLabels (Fin.castAdd d) p ∈ carrier A ∧ p.2 ∘ Fin.natAdd a = t := by
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨(retain_fixed_rv_labels A t ht q).symm ▸ q.property,funext fun i => Fin.append_right _ _ i⟩
  · rintro ⟨hp,he⟩
    refine ⟨⟨retainVFLabels (Fin.castAdd d) p,hp⟩,Prod.ext rfl ?_⟩
    change Fin.append (p.2 ∘ Fin.castAdd d) t = p.2
    rw [← he]
    exact Fin.append_castAdd_natAdd

theorem fixed_rv_label_projection_surjective (A : DefSet (M := M) S n a) (t : Fin d → RV (M := M))
    (ht : ∀ i, (t i).val ∈ S) :
    ∀ p : A, ∃ q : fixedRVLabelDomain A t ht, retainVFLabels (Fin.castAdd d) q.val = p.val := by
  intro p
  exact ⟨Map.toImage (appendFixedRVLabelsMap A t ht) p,retain_fixed_rv_labels A t ht p⟩

theorem fixed_rv_labels_jointly_determine :
    RVLabelsJointlyDetermine (M := M) (Fin.castAdd d : Fin a → Fin (a+d)) (Fin.natAdd a) := by
  intro x y hx hy
  calc
    x = Fin.append (x ∘ Fin.castAdd d) (x ∘ Fin.natAdd a) := Fin.append_castAdd_natAdd.symm
    _ = Fin.append (y ∘ Fin.castAdd d) (y ∘ Fin.natAdd a) := congrArg₂ Fin.append hx hy
    _ = y := Fin.append_castAdd_natAdd

theorem gamma_fixed_rv_tuple_locus {B : Base (M := M)} (t : Fin d → RV (M := M))
    (hT : DefinableOverBase B (fun _ : Fin d => .rv) {fun i => (t i).val}) :
    GammaSetDefinable B {p : Point (M := M) n (a+d) | p.2 ∘ Fin.natAdd a = t} := by
  let ρ : Fin d → Fin (n+(a+d)) := fun j => Fin.natAdd n (Fin.natAdd a j)
  have h := gamma_set_of_sorted_formula (hT.preimage_real (gammaPointSort n (a+d)) ρ)
  convert h using 1
  ext p
  have he : gammaPointCode p ∘ ρ = fun j => (p.2 (Fin.natAdd a j)).val := by
    funext j
    simp only [ρ,Function.comp_apply,gammaPointCode,Fin.append_right]
  change _ ↔ (_ ∈ {fun i => (t i).val} ∧ _)
  rw [he,Set.mem_singleton_iff]
  constructor
  · intro hp
    exact ⟨congrArg (fun r => fun i => (r i).val) hp,gammaPointCode_proper p⟩
  · rintro ⟨hp,_⟩
    funext j
    exact Subtype.ext (congrFun hp j)

theorem gamma_fixed_rv_label_domain {B : Base (M := M)}
    (A : DefSet (M := M) S n a) (hA : GammaSetDefinable B (carrier A))
    (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
    (hT : DefinableOverBase B (fun _ : Fin d => .rv) {fun i => (t i).val}) :
    GammaSetDefinable B (carrier (fixedRVLabelDomain A t ht)) := by
  have h := (gammaLogicInput B).inter (gamma_retain_vf_labels_preimage (Fin.castAdd d) (carrier A) hA)
    (gamma_fixed_rv_tuple_locus (n := n) (a := a) t hT)
  convert h using 1
  ext p
  exact fixed_rv_label_domain_carrier A t ht p

end IntegrationInACVF.Section7
