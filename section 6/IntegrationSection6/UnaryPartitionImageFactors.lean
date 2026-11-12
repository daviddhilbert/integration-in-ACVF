import IntegrationSection5.UnaryPartition
import IntegrationSection6.GammaFiniteMixedUnions

/-! The particular factors of Section5.6 have exactly the images of the
partition pieces under the original isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a b : ℕ}
variable {A : Set (Point (M := M) n a)} {C : Set (Point (M := M) n b)}

theorem unaryPartition_image_factor (e : GammaIso B A C) (Q : GammaUnaryPartition e) (i : Q.pieces) :
    Nonempty (GammaUnaryChain B n i.val (gammaRestrictionTarget e i.val (Q.subset i.val i.property))) := by
  obtain ⟨E,T,hT⟩ := Q.factors i.val i.property
  have he : E = gammaRestrictionTarget e i.val (Q.subset i.val i.property) := by
    ext q
    constructor
    · intro hq
      obtain ⟨p,hp⟩ := T.toIso.equiv.surjective ⟨q,hq⟩
      exact ⟨p,(hT p).symm.trans (congrArg (fun z : E => z.val) hp)⟩
    · rintro ⟨p,hp⟩
      exact ((hT p).trans hp) ▸ (T.toIso.equiv p).property
  exact ⟨T.congrTarget he⟩

theorem gammaRestrictionTarget_disjoint (e : GammaIso B A C)
    (D E : Set (Point (M := M) n a)) (hDA : D ⊆ A) (hEA : E ⊆ A) (hDisj : Disjoint D E) :
    Disjoint (gammaRestrictionTarget e D hDA) (gammaRestrictionTarget e E hEA) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨p,hp⟩ ⟨r,hr⟩
  have he := e.equiv.injective (Subtype.ext (hp.trans hr.symm))
  have hv := congrArg (fun z : A => z.val) he
  exact Set.disjoint_left.mp hDisj p.property (hv.symm ▸ r.property)

def unaryPartitionSource (e : GammaIso B A C) (Q : GammaUnaryPartition e) (i : Q.pieces) :
    DefSet (M := M) Set.univ n a := gammaDefSetUniv i.val (Q.definable i.val i.property)

def unaryPartitionTarget (e : GammaIso B A C) (Q : GammaUnaryPartition e) (i : Q.pieces) :
    DefSet (M := M) Set.univ n b :=
  gammaDefSetUniv (gammaRestrictionTarget e i.val (Q.subset i.val i.property))
    ((gammaRestrictionIso e i.val (Q.subset i.val i.property) (Q.definable i.val i.property)).target_definable (gammaLogicInput B))

theorem unaryPartitionSource_cover (e : GammaIso B A C) (Q : GammaUnaryPartition e) :
    A = mixedFiniteUnionSet (unaryPartitionSource e Q) Finset.univ := by
  ext p
  constructor
  · intro hp
    obtain ⟨D,hD,hpD⟩ := Q.cover ⟨p,hp⟩
    exact ⟨⟨D,hD⟩,Finset.mem_univ _,hpD⟩
  · rintro ⟨i,_,hi⟩
    exact Q.subset i.val i.property hi

theorem unaryPartitionTarget_cover (e : GammaIso B A C) (Q : GammaUnaryPartition e) :
    C = mixedFiniteUnionSet (unaryPartitionTarget e Q) Finset.univ := by
  ext q
  constructor
  · intro hq
    let c : C := ⟨q,hq⟩
    let p := e.equiv.symm c
    obtain ⟨D,hD,hpD⟩ := Q.cover p
    refine ⟨⟨D,hD⟩,Finset.mem_univ _,⟨⟨p.val,hpD⟩,?_⟩⟩
    change (e.equiv ⟨p.val,Q.subset D hD hpD⟩).val = q
    have he : (⟨p.val,Q.subset D hD hpD⟩ : A) = p := Subtype.ext rfl
    rw [he]
    exact congrArg (fun z : C => z.val) (e.equiv.apply_symm_apply c)
  · rintro ⟨i,_,hi⟩
    exact gammaRestrictionTarget_subset e i.val (Q.subset i.val i.property) hi

end IntegrationInACVF.Section6
