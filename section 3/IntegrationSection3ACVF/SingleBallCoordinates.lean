import IntegrationSection3ACVF.ResiduePunctures
import IntegrationSection3ACVF.OpenToOpenQuotient

/-! Actual total residue-coordinate functions for one thin punctured ball,
with surjectivity onto the cofinite line and exact entire-ball fibres. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.BallResidueChart
open IntegrationInACVF.Section3ACVF.ResidueBallClasses

noncomputable section

namespace IntegrationInACVF.Section3ACVF.SingleBallCoordinates

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def value (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (x : M) : ModelResidue M := by
  classical
  exact if hx : x ∈ gammaBall a α false then
    coordinate a r α hr ⟨⟨x,hx.choose⟩,hx⟩ else 0

theorem value_of_point (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (x : Point a α) :
    value a r α hr x.val.val = coordinate a r α hr x := by
  simp only [value,dif_pos x.property]
  apply congrArg (coordinate a r α hr)
  apply Subtype.ext
  rfl

theorem cofinite_image (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (d : PuncturedBall M)
    (hd : d.parent = gammaBall a α false)
    (hholes : ∀ h ∈ d.holes, ∃ b : VFType (M := M), h = gammaBall b α true) :
    ∃ F : Finset (ModelResidue M), F.card = d.holes.card ∧
      (∀ x : Point a α, x.val.val ∈ d.body ↔ coordinate a r α hr x ∉ F) ∧
      d.body.MapsTo (value a r α hr) (Set.univ \ F) ∧
      d.body.SurjOn (value a r α hr) (Set.univ \ F) := by
  obtain ⟨F,hCard,_,hBody⟩ := ResiduePunctures.finite_holes a r α hr d hd hholes
  refine ⟨F,hCard,hBody,?_,?_⟩
  · intro x hx
    let p : Point a α := ⟨⟨x,d.body_subset_vf hx⟩,hd ▸ hx.1⟩
    refine ⟨Set.mem_univ _,?_⟩
    change value a r α hr p.val.val ∉ F
    rw [value_of_point]
    exact (hBody p).mp hx
  · intro t ht
    obtain ⟨p,hp⟩ := BallResidueChart.surjective a r α hr t
    have hpBody := (hBody p).mpr (hp.symm ▸ ht.2)
    exact ⟨p.val.val,hpBody,(value_of_point a r α hr p).trans hp⟩

theorem fibre_ball (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (d : PuncturedBall M)
    (hd : d.parent = gammaBall a α false)
    (hholes : ∀ h ∈ d.holes, ∃ b : VFType (M := M), h = gammaBall b α true)
    (x : M) (hx : x ∈ d.body) :
    OpenToOpenQuotient.fibre d.body (value a r α hr) (value a r α hr x) =
      BallImaginaries.underlying (ball a r α hr (value a r α hr x)) := by
  let p : Point a α := ⟨⟨x,d.body_subset_vf hx⟩,hd ▸ hx.1⟩
  have hpx : coordinate a r α hr p = value a r α hr x := (value_of_point a r α hr p).symm
  have hxBall : x ∈ BallImaginaries.underlying (ball a r α hr (value a r α hr x)) :=
    (mem_ball a r α hr _ p).mpr hpx
  let c := centre a r α hr (value a r α hr x)
  have hWhole : BallImaginaries.underlying (ball a r α hr (value a r α hr x)) ⊆ d.body := by
    rw [underlying_ball] at hxBall ⊢
    exact MaximalSubballGeometry.class_subset_body d α a hd hholes c.val p.val hx hxBall
  ext y
  constructor
  · rintro ⟨hy,he⟩
    let q : Point a α := ⟨⟨y,d.body_subset_vf hy⟩,hd ▸ hy.1⟩
    exact (mem_ball a r α hr _ q).mpr ((value_of_point a r α hr q).symm.trans he)
  · intro hy
    have hyBody := hWhole hy
    let q : Point a α := ⟨⟨y,d.body_subset_vf hyBody⟩,hd ▸ hyBody.1⟩
    exact ⟨hyBody,(value_of_point a r α hr q).trans ((mem_ball a r α hr _ q).mp hy)⟩

end IntegrationInACVF.Section3ACVF.SingleBallCoordinates
