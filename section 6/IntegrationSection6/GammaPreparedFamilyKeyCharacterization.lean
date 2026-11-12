import IntegrationSection6.GammaPreparedFamilyNormalForm
import IntegrationSection6.GammaPreparedIndexValues
import IntegrationSection6.GammaIndexedFiniteObjects

/-! A prepared mixed-family image is exactly the indexed RV domain with
its VF leading terms fixed by the first key coordinates. -/
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
variable {B : Base (M := M)} {S : Set M} {p l a k : ℕ}
variable {A : Set (Point (M := M) p 0)}

theorem preparedFamilyImage_key_iff (C : DefSet (M := M) S p l)
    (e : GammaIso B A (carrier C)) (hA : GammaSetDefinable B A) (hC : IsRVPullback (carrier C))
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B (p+l) a k (fun _ => .rv))
    (hRows : ∀ c : C, GammaSchemaRowAgreement F (rawVFParameter (e.equiv.symm c).val) G (rawPreparedKey c.val))
    (q : Point (M := M) p ((p+l)+a)) :
    q ∈ preparedFamilyImage e F ↔
      q.2 ∈ indexedDomain (preparedKeyDomain C) (fun t => G.rowDomain (fun j => (t j).val)) ∧
      indexedLeft q.2 ∘ Fin.castAdd l = (fun j => rv (q.1 j)) := by
  rw [preparedFamilyImage_descended_iff e hA F G hRows q]
  constructor
  · rintro ⟨c,r,hr,rfl⟩
    simp only [indexedDomain,Set.mem_setOf_eq,indexedLeft,indexedRight,Function.comp_def,
      Fin.append_left,Fin.append_right]
    exact ⟨⟨⟨c,rfl⟩,hr⟩,funext (fun j => Fin.append_left _ _ j)⟩
  · rintro ⟨hD,hPrefix⟩
    let t := indexedLeft q.2
    let r := indexedRight q.2
    let b : Point (M := M) p l := (q.1,t ∘ Fin.natAdd p)
    have hKey : (flatKey b).2 = t := by
      change Fin.append (fun j => rv (q.1 j)) (t ∘ Fin.natAdd p) = t
      exact (congrArg (fun v => Fin.append v (t ∘ Fin.natAdd p)) hPrefix).symm.trans Fin.append_castAdd_natAdd
    have hb : b ∈ carrier C := (prepared_key_domain_iff C hC b).mp (hKey.symm ▸ hD.1)
    let c : C := ⟨b,hb⟩
    refine ⟨c,r,?_,?_⟩
    · change r ∈ G.rowDomain (fun j => ((flatKey b).2 j).val)
      rw [hKey]
      exact hD.2
    · change (q.1,Fin.append (flatKey b).2 r) = q
      rw [hKey]
      exact congrArg (fun v => (q.1,v)) (Fin.append_castAdd_natAdd (f := q.2))

end IntegrationInACVF.Section6
