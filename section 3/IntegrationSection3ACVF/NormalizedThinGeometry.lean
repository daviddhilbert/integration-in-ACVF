import IntegrationSection3ACVF.NormalizedBallParameters

/-! Normalize actual punctured-ball families without changing any parent,
hole, body, component count or total hole count. Gamma quotients remain
distinct; their same-radius families are transported by common RV codes. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.ThinFamilyGeometry
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.NormalizedThinGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => @CanonicalStructure.normalize M sM
local notation "hN" => @CanonicalStructure.normalized_model M sM hM

def normalize (d : PuncturedBall M) : @PuncturedBall M N :=
  @PuncturedBall.mk M N d.parent (isBall_normalize d.parent d.parent_ball) d.holes
    (fun h hh => isBall_normalize h (d.holes_ball h hh)) d.holes_proper d.holes_disjoint

theorem body_normalize (d : PuncturedBall M) : @PuncturedBall.body M N (normalize d) = d.body := rfl

theorem punctured_ext {d e : PuncturedBall M} (hp : d.parent = e.parent) (hh : d.holes = e.holes) : d = e := by
  cases d
  cases e
  cases hp
  cases hh
  rfl

theorem normalize_injective : Function.Injective (normalize (M := M)) := by
  intro d e he
  apply punctured_ext
  · exact congrArg (fun b : @PuncturedBall M N => @PuncturedBall.parent M N b) he
  · exact congrArg (fun b : @PuncturedBall M N => @PuncturedBall.holes M N b) he

theorem thin_normalize {d : PuncturedBall M} (hd : IsThin d) :
    @IsThin M N hN (normalize d) := by
  obtain ⟨a,α,hParent,hHoles⟩ := hd
  obtain ⟨β,hβ⟩ := NormalizedBallParameters.gamma_family α
  refine ⟨⟨a.val,a.property⟩,β,?_,?_⟩
  · exact hParent.trans (hβ a false).symm
  · intro h hh
    obtain ⟨b,hb⟩ := hHoles h hh
    exact ⟨⟨b.val,b.property⟩,hb.trans (hβ b true).symm⟩

theorem open_normalize_iff (D : Set M) :
    @PaperBalls.IsOpenBall M N hN D ↔ PaperBalls.IsOpenBall D := by
  constructor
  · rintro (hv | ⟨b,β,hD⟩)
    · exact Or.inl hv
    · obtain ⟨α,hα⟩ := NormalizedBallParameters.gamma_family_back β
      let a : VFType (M := M) := ⟨b.val,b.property⟩
      exact Or.inr ⟨a,α,hD.trans (hα a true)⟩
  · rintro (hv | ⟨a,α,hD⟩)
    · exact Or.inl hv
    · obtain ⟨β,hβ⟩ := NormalizedBallParameters.gamma_family α
      exact Or.inr ⟨⟨a.val,a.property⟩,β,hD.trans (hβ a true).symm⟩

end IntegrationInACVF.Section3ACVF.NormalizedThinGeometry
