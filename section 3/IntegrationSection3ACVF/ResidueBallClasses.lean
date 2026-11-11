import IntegrationSection3ACVF.BallResidueChart

/-! Each residue coordinate gives one actual ball imaginary, and every
maximal open subball of the closed parent occurs exactly once. The choices
below construct a bijection of quotient sets, not a definable point selector. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.BallResidueChart

noncomputable section

namespace IntegrationInACVF.Section3ACVF.ResidueBallClasses

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def centre (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (t : ModelResidue M) : Point a α :=
  Classical.choose (surjective a r α hr t)

theorem centre_coordinate (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (t : ModelResidue M) :
    coordinate a r α hr (centre a r α hr t) = t :=
  Classical.choose_spec (surjective a r α hr t)

def ball (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (t : ModelResidue M) : BallImaginaries.Ball M :=
  Classical.choose (GammaCosetGeometry.gammaBall_coded (centre a r α hr t).val α)

theorem underlying_ball (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (t : ModelResidue M) :
    BallImaginaries.underlying (ball a r α hr t) = gammaBall (centre a r α hr t).val α true :=
  Classical.choose_spec (GammaCosetGeometry.gammaBall_coded (centre a r α hr t).val α)

theorem mem_ball (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (t : ModelResidue M) (x : Point a α) :
    x.val.val ∈ BallImaginaries.underlying (ball a r α hr t) ↔ coordinate a r α hr x = t := by
  rw [underlying_ball,← same_fibres a r α hr x (centre a r α hr t),centre_coordinate]

theorem underlying_injective (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) :
    Function.Injective (fun t => BallImaginaries.underlying (ball a r α hr t)) := by
  intro t u he
  have ht : (centre a r α hr t).val.val ∈ BallImaginaries.underlying (ball a r α hr t) :=
    (mem_ball a r α hr t _).mpr (centre_coordinate a r α hr t)
  have hu := (Set.ext_iff.mp he ((centre a r α hr t).val.val)).mp ht
  exact (centre_coordinate a r α hr t).symm.trans ((mem_ball a r α hr u _).mp hu)

theorem ball_injective (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) : Function.Injective (ball a r α hr) := by
  intro t u he
  exact underlying_injective a r α hr (congrArg BallImaginaries.underlying he)

theorem ball_coordinate (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (x : Point a α) :
    BallImaginaries.underlying (ball a r α hr (coordinate a r α hr x)) = gammaBall x.val α true := by
  rw [underlying_ball]
  apply MaximalSubballGeometry.equal_of_inter
  refine ⟨x.val.val,?_,BallEnlargementGeometry.gammaBall_centre_mem x.val α true⟩
  exact (same_fibres a r α hr x _).mp (centre_coordinate a r α hr _).symm

def family (a : VFType (M := M)) (α : Values.Gamma (M := M)) : Set (BallImaginaries.Ball M) :=
  {j | ∃ x : Point a α, BallImaginaries.underlying j = gammaBall x.val α true}

theorem range_ball (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) : Set.range (ball a r α hr) = family a α := by
  ext j
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨centre a r α hr t,underlying_ball a r α hr t⟩
  · rintro ⟨x,hx⟩
    refine ⟨coordinate a r α hr x,BallImaginaries.underlying_injective ?_⟩
    exact (ball_coordinate a r α hr x).trans hx.symm

end IntegrationInACVF.Section3ACVF.ResidueBallClasses
