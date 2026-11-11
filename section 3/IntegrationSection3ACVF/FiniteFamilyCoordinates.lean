import IntegrationSection3ACVF.ThinResidueCoordinates
import IntegrationSection3.FiniteTaggedHoles

/-! Actual coordinates for a finite disjoint family of thin components.
The tag is an actual distinct residue-field element, and each fibre is
proved to be the corresponding component's entire maximal open class. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.ThinFamilyGeometry
open IntegrationInACVF.Section3ACVF.ThinResidueCoordinates

noncomputable section

namespace IntegrationInACVF.Section3ACVF.FiniteFamilyCoordinates

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def member (F : Finset (PuncturedBall M)) (x : body F) : F :=
  ⟨Classical.choose x.property,(Classical.choose_spec x.property).1⟩

theorem member_body (F : Finset (PuncturedBall M)) (x : body F) :
    x.val ∈ (member F x).val.body := (Classical.choose_spec x.property).2

theorem member_eq (F : Finset (PuncturedBall M))
    (hDis : (F : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body))
    (d : F) (x : body F) (hx : x.val ∈ d.val.body) : member F x = d := by
  apply Subtype.ext
  by_contra hn
  exact (Set.disjoint_left.mp (hDis (member F x).property d.property hn) (member_body F x) hx).elim

def value (F : Finset (PuncturedBall M)) (C : ∀ d : F, Chart d.val)
    (e : F ↪ ModelResidue M) (x : M) : Fin 2 → ModelResidue M := by
  classical
  exact if hx : x ∈ body F then
    ![ThinResidueCoordinates.value (C (member F ⟨x,hx⟩)) x,e (member F ⟨x,hx⟩)] else fun _ => 0

theorem value_on (F : Finset (PuncturedBall M)) (C : ∀ d : F, Chart d.val)
    (e : F ↪ ModelResidue M)
    (hDis : (F : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body))
    (d : F) (x : M) (hx : x ∈ d.val.body) :
    value F C e x = ![ThinResidueCoordinates.value (C d) x,e d] := by
  have hxF : x ∈ body F := ⟨d.val,d.property,hx⟩
  have hm := member_eq F hDis d ⟨x,hxF⟩ hx
  unfold value
  rw [dif_pos hxF,hm]

theorem cofinite_image (F : Finset (PuncturedBall M)) (C : ∀ d : F, Chart d.val)
    (e : F ↪ ModelResidue M)
    (hDis : (F : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body)) :
    (body F).MapsTo (value F C e)
        (TaggedLineMaps.space (FiniteTaggedHoles.tags e) \ FiniteTaggedHoles.holes e (fun d => (C d).excluded)) ∧
      (body F).SurjOn (value F C e)
        (TaggedLineMaps.space (FiniteTaggedHoles.tags e) \ FiniteTaggedHoles.holes e (fun d => (C d).excluded)) := by
  constructor
  · intro x hx
    obtain ⟨d,hd,hxd⟩ := hx
    let i : F := ⟨d,hd⟩
    rw [value_on F C e hDis i x hxd]
    apply (FiniteTaggedHoles.cofinite_mem e (fun d => (C d).excluded) _).mpr
    exact ⟨i,rfl,(ThinResidueCoordinates.cofinite_image (C i)).1 hxd |>.2⟩
  · intro z hz
    obtain ⟨i,hi,hNot⟩ := (FiniteTaggedHoles.cofinite_mem e (fun d => (C d).excluded) z).mp hz
    obtain ⟨x,hx,hv⟩ := (ThinResidueCoordinates.cofinite_image (C i)).2 ⟨Set.mem_univ _,hNot⟩
    refine ⟨x,⟨i.val,i.property,hx⟩,?_⟩
    rw [value_on F C e hDis i x hx,hv]
    funext k
    fin_cases k
    · rfl
    · exact hi.symm

theorem fibre_component (F : Finset (PuncturedBall M)) (C : ∀ d : F, Chart d.val)
    (e : F ↪ ModelResidue M)
    (hDis : (F : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body))
    (d : F) (x : M) (hx : x ∈ d.val.body) :
    OpenToOpenQuotient.fibre (body F) (value F C e) (value F C e x) =
      OpenToOpenQuotient.fibre d.val.body (ThinResidueCoordinates.value (C d))
        (ThinResidueCoordinates.value (C d) x) := by
  ext y
  constructor
  · rintro ⟨⟨a,ha,hya⟩,he⟩
    let j : F := ⟨a,ha⟩
    rw [value_on F C e hDis j y hya,value_on F C e hDis d x hx] at he
    have hjd : j = d := e.injective (by
      simpa only [Matrix.cons_val_one,Matrix.cons_val_zero] using congrFun he 1)
    have hy : y ∈ d.val.body := (congrArg (fun i : F => i.val.body) hjd) ▸ hya
    have hVal := congrArg (fun i : F => ThinResidueCoordinates.value (C i) y) hjd
    exact ⟨hy,hVal.symm.trans (congrFun he 0)⟩

  · rintro ⟨hy,he⟩
    refine ⟨⟨d.val,d.property,hy⟩,?_⟩
    change value F C e y = value F C e x
    rw [value_on F C e hDis d y hy,value_on F C e hDis d x hx,he]

end IntegrationInACVF.Section3ACVF.FiniteFamilyCoordinates
