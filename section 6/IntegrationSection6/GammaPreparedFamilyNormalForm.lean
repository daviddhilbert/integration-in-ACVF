import IntegrationSection6.GammaPreparedFamilyValues
import IntegrationSection6.GammaSchemaRowAgreement

/-! The actual prepared-family image consists exactly of prepared base
points with their unchanged fibre RV labels. Exact row descent may then
replace the original fibre-domain formula by its RV-key formula. -/
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
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p l a k : ℕ}
variable {A : Set (Point (M := M) p 0)} {C : Set (Point (M := M) p l)}

theorem preparedFamilyImage_iff (e : GammaIso B A C) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) (q : Point (M := M) p ((p+l)+a)) :
    q ∈ preparedFamilyImage e F ↔ ∃ c : C, ∃ r : Fin a → RV (M := M),
      r ∈ F.rowDomain (rawVFParameter (e.equiv.symm c).val) ∧
        (c.val.1,Fin.append (flatKey c.val).2 r) = q := by
  let f := gammaPreparedFamilyIso e hA F
  constructor
  · intro hq
    obtain ⟨z,hz⟩ := f.equiv.surjective ⟨q,hq⟩
    let b : A := ⟨(z.val.1,Fin.elim0),z.property.1⟩
    let c := e.equiv b
    refine ⟨c,z.val.2,?_,?_⟩
    · have hb : e.equiv.symm c = b := e.equiv.symm_apply_apply b
      rw [hb]
      exact z.property.2
    · exact (gammaPreparedFamilyIso_value e hA F z).symm.trans
        (congrArg (fun y : preparedFamilyImage e F => y.val) hz)
  · rintro ⟨c,r,hr,hq⟩
    let b := e.equiv.symm c
    have hb : (b.val.1,Fin.elim0) ∈ A := by
      have he : (b.val.1,Fin.elim0) = b.val := Prod.ext rfl (Subsingleton.elim _ _)
      exact Eq.mpr (congrArg (fun v : Point (M := M) p 0 => v ∈ A) he) b.property
    let z : vfSchemaSource A F := ⟨(b.val.1,r),hb,hr⟩
    have he : e.equiv ⟨(z.val.1,Fin.elim0),z.property.1⟩ = c := by
      have hb' : (⟨(z.val.1,Fin.elim0),z.property.1⟩ : A) = b :=
        Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _))
      exact (congrArg e.equiv hb').trans (e.equiv.apply_symm_apply c)
    have hval : (f.equiv z).val = q := by
      have h := gammaPreparedFamilyIso_value e hA F z
      dsimp only at h
      rw [he] at h
      exact h.trans hq
    exact hval ▸ (f.equiv z).property

theorem preparedFamilyImage_descended_iff (e : GammaIso B A C) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B (p+l) a k (fun _ => .rv))
    (hRows : ∀ c : C, GammaSchemaRowAgreement F (rawVFParameter (e.equiv.symm c).val) G (rawPreparedKey c.val))
    (q : Point (M := M) p ((p+l)+a)) :
    q ∈ preparedFamilyImage e F ↔ ∃ c : C, ∃ r : Fin a → RV (M := M),
      r ∈ G.rowDomain (rawPreparedKey c.val) ∧ (c.val.1,Fin.append (flatKey c.val).2 r) = q := by
  rw [preparedFamilyImage_iff e hA F q]
  exact exists_congr (fun c => exists_congr (fun r =>
    and_congr (Iff.of_eq (congrArg (fun D => r ∈ D) (hRows c).domains)) Iff.rfl))

end IntegrationInACVF.Section6
