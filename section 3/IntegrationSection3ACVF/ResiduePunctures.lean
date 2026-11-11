import IntegrationSection3ACVF.ResidueBallClasses

/-! Maximal open holes of one closed parent correspond bijectively to a
finite set of actual residue coordinates. The complement is the actual
punctured point set, not an assumed quotient interpretation. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.BallResidueChart
open IntegrationInACVF.Section3ACVF.ResidueBallClasses
open IntegrationInACVF.Section3ACVF.PuncturedGeometry

noncomputable section

namespace IntegrationInACVF.Section3ACVF.ResiduePunctures

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem hole_coordinate (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (d : PuncturedBall M)
    (hd : d.parent = gammaBall a α false)
    (hholes : ∀ h ∈ d.holes, ∃ b : VFType (M := M), h = gammaBall b α true)
    (h : Set M) (hh : h ∈ d.holes) :
    ∃ t : ModelResidue M, BallImaginaries.underlying (ball a r α hr t) = h := by
  obtain ⟨b,hb⟩ := hholes h hh
  have hbh : b.val ∈ h := hb.symm ▸ BallEnlargementGeometry.gammaBall_centre_mem b α true
  have hbp : b.val ∈ gammaBall a α false := hd ▸ (d.holes_proper h hh).1 hbh
  let x : Point a α := ⟨b,hbp⟩
  exact ⟨coordinate a r α hr x,(ball_coordinate a r α hr x).trans hb.symm⟩

theorem finite_holes (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (d : PuncturedBall M)
    (hd : d.parent = gammaBall a α false)
    (hholes : ∀ h ∈ d.holes, ∃ b : VFType (M := M), h = gammaBall b α true) :
    ∃ F : Finset (ModelResidue M), F.card = d.holes.card ∧
      (∀ t, t ∈ F ↔ BallImaginaries.underlying (ball a r α hr t) ∈ d.holes) ∧
      ∀ x : Point a α, x.val.val ∈ d.body ↔ coordinate a r α hr x ∉ F := by
  classical
  let c : d.holes → ModelResidue M := fun h =>
    Classical.choose (hole_coordinate a r α hr d hd hholes h.val h.property)
  have hc (h : d.holes) : BallImaginaries.underlying (ball a r α hr (c h)) = h.val :=
    Classical.choose_spec (hole_coordinate a r α hr d hd hholes h.val h.property)
  have hinj : Function.Injective c := by
    intro h k he
    apply Subtype.ext
    exact (hc h).symm.trans ((congrArg (fun t => BallImaginaries.underlying (ball a r α hr t)) he).trans (hc k))
  let F := d.holes.attach.image c
  have hCard : F.card = d.holes.card := by
    rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
  have hMem (t : ModelResidue M) : t ∈ F ↔ BallImaginaries.underlying (ball a r α hr t) ∈ d.holes := by
    constructor
    · intro ht
      obtain ⟨h,_,rfl⟩ := Finset.mem_image.mp ht
      exact (hc h).symm ▸ h.property
    · intro ht
      let h : d.holes := ⟨BallImaginaries.underlying (ball a r α hr t),ht⟩
      have he : c h = t := underlying_injective a r α hr (hc h)
      exact Finset.mem_image.mpr ⟨h,Finset.mem_attach _ h,he⟩
  refine ⟨F,hCard,hMem,?_⟩
  intro x
  constructor
  · intro hx ht
    exact hx.2 ⟨BallImaginaries.underlying (ball a r α hr (coordinate a r α hr x)),
      (hMem _).mp ht,(mem_ball a r α hr _ x).mpr rfl⟩
  · intro hx
    refine ⟨hd.symm ▸ x.property,?_⟩
    rintro ⟨h,hh,hxh⟩
    obtain ⟨t,ht⟩ := hole_coordinate a r α hr d hd hholes h hh
    have hxt : coordinate a r α hr x = t := (mem_ball a r α hr t x).mp (ht.symm ▸ hxh)
    apply hx
    rw [hxt]
    exact (hMem t).mpr (ht.symm ▸ hh)

end IntegrationInACVF.Section3ACVF.ResiduePunctures
