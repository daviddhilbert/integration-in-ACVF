import IntegrationSection6.GammaAdmissibility
import Section5.GammaLiftRelation
import Section5.GammaInvariantLogic

/-! The actual RV volume image is definable over the original Gamma base.
No representatives of Gamma names are added to its real parameter set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

def gammaVolumeImage (U : GammaRVObject B n) : Set (Fin n → M) :=
  {t | ∃ u : rvObjectDomain U.object, (fun i => (gammaVolumeValue U u i).val) = t}

theorem gammaVolumeImage_definable (U : GammaRVObject B n) :
    DefinableOverBase B (fun _ => .rv) (gammaVolumeImage U) := by
  have hi := (gammaLogicInput B).image_graph U.volume_graph
  have hh := DefinableOverBase.image_real hi (Fin.natAdd 0 : Fin n → Fin (0+n))
  have hs : gammaPointSort 0 n ∘ (Fin.natAdd 0) = (fun _ : Fin n => SortTag.rv) := by
    funext i
    simp only [Function.comp_apply,gammaPointSort,Fin.append_right]
  rw [hs] at hh
  convert hh using 1
  ext z
  constructor
  · rintro ⟨u,rfl⟩
    let q : Point (M := M) 0 n := (Fin.elim0,gammaVolumeValue U u)
    let p : Point (M := M) 0 (rvObjectArity U.object) := (Fin.elim0,u.val)
    refine ⟨gammaPointCode q,⟨q,⟨p,u,rfl,rfl⟩,rfl⟩,?_⟩
    funext i
    change gammaPointCode q (Fin.natAdd 0 i) = _
    exact Fin.append_right (fun j => (vfAt q j).val) (fun j => (q.2 j).val) i
  · rintro ⟨_,⟨q,⟨p,u,hu,hv⟩,rfl⟩,rfl⟩
    refine ⟨u,?_⟩
    change gammaVolumeValue U u = q.2 at hv
    funext i
    simpa only [Function.comp_apply,gammaPointCode,Fin.append_right] using
      congrArg Subtype.val (congrFun hv i)

theorem GammaAdmissible.image_nonzero {U : GammaRVObject B n} {i : Fin n}
    (h : GammaAdmissible U i) {t : Fin n → M} (ht : t ∈ gammaVolumeImage U) :
    t i ≠ iRVZero := by
  obtain ⟨u,rfl⟩ := ht
  exact h.nonzero u

theorem GammaAdmissible.image_algebraic {U : GammaRVObject B n} {i : Fin n}
    (h : GammaAdmissible U i) (t : Fin n → CanonicalRV.RVSort M)
    (ht : rvValues t ∈ gammaVolumeImage U) :
    AlgebraicAtBase ⟨coordinateBase B.real i t,B.gamma⟩ .rv (t i).val := by
  obtain ⟨u,hu⟩ := ht
  have he : gammaVolumeValue U u = t := rvValues_injective hu
  simpa only [he] using h.algebraic u

end IntegrationInACVF.Section6
