import IntegrationSection6.VFPrefixMaps
import IntegrationSection6.VFPrefixHeadCoordinates

/-! The actual head image commutes with freezing a complementary VF tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n p m : ℕ}

theorem vfPrefixTailFixed_of_headKey (x : Fin n → VF (M := M))
    (q : Point (M := M) (n+(p+1)) m) (h : VFPrefixTailFixed (p := p) x (headKey q)) :
    VFPrefixTailFixed (p := p+1) x q := by
  intro j
  have hi : (⟨(p+1)+j.val,by omega⟩ : Fin (n+(p+1))) =
      (⟨p+j.val,by omega⟩ : Fin (n+p)).succ := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  change q.1 ⟨(p+1)+j.val,by omega⟩ = x j
  rw [hi]
  exact h j

theorem vfPrefixFibre_headImage (A : DefSet (M := M) S (n+(p+1)) m)
    (x : Fin n → VF (M := M)) :
    carrier (headImage (vfPrefixFibre A x)) = carrier (vfPrefixFibre (headImage A) x) := by
  ext q
  constructor
  · rintro ⟨a,ha⟩
    let b : A := ⟨vfPrefixInsert x a.val,a.property⟩
    refine ⟨b,?_⟩
    have ha' : headKey a.val = q := (headKeyMap_apply (vfPrefixFibre A x) a).symm.trans ha
    exact (headKeyMap_apply A b).trans
      ((vfPrefixInsert_headKey x a.val).symm.trans (congrArg (vfPrefixInsert x) ha'))
  · rintro ⟨b,hb⟩
    have hb' : headKey b.val = vfPrefixInsert x q := (headKeyMap_apply A b).symm.trans hb
    have ht : VFPrefixTailFixed (p := p) x (headKey b.val) := by
      rw [hb']
      exact fun j => vfPrefixTuple_tail x q.1 j
    have hr := vfPrefixInsert_project (p := p+1) x b.val (vfPrefixTailFixed_of_headKey x b.val ht)
    let a : vfPrefixFibre (p := p+1) A x := ⟨vfPrefixProject (p := p+1) b.val,by
      change vfPrefixInsert (p := p+1) x (vfPrefixProject (p := p+1) b.val) ∈ carrier A
      rw [hr]
      exact b.property⟩
    refine ⟨a,?_⟩
    apply (headKeyMap_apply (vfPrefixFibre A x) a).trans
    apply vfPrefixInsert_injective x
    exact (vfPrefixInsert_headKey x a.val).trans ((congrArg headKey hr).trans hb')

end IntegrationInACVF.Section6
