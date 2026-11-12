import IntegrationSection6.GammaRawRVFormulas
import IntegrationSection6.GammaFiniteTupleBounds
import IntegrationSection6.FiniteGammaIsomorphisms

/-! Raw sorted domain and volume formulas of actual original-Gamma RV
objects. These retain the full Gamma base and expose the fixed finite
volume bounds needed to promote an actual object to a finite schema. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

def gammaRawObjectDomain (U : GammaRVObject B k) : Set (Fin (rvObjectArity U.object) → M) :=
  {x | ∃ u : rvObjectDomain U.object, (fun j => (u.val j).val) = x}

def gammaRawObjectVolume (U : GammaRVObject B k) : Set (Fin (rvObjectArity U.object+k) → M) :=
  {z | ∃ u : rvObjectDomain U.object,
    Fin.append (fun j => (u.val j).val) (fun j => (gammaVolumeValue U u j).val) = z}

theorem pureRVPairCoordinates_code {a b : ℕ}
    (p : Point (M := M) 0 a) (q : Point (M := M) 0 b) :
    Fin.append (gammaPointCode p) (gammaPointCode q) ∘ pureRVPairCoordinates a b =
      Fin.append (fun j => (p.2 j).val) (fun j => (q.2 j).val) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp only [pureRVPairCoordinates,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right,gammaPointCode]

theorem gammaRawObjectDomain_definable (U : GammaRVObject B k) :
    DefinableOverBase B (fun _ => .rv) (gammaRawObjectDomain U) := by
  have h := DefinableOverBase.image_real U.domain_graph (Fin.natAdd 0)
  have hs : gammaPointSort 0 (rvObjectArity U.object) ∘ Fin.natAdd 0 =
      (fun _ => SortTag.rv) := by
    funext j
    simp only [gammaPointSort,Function.comp_apply,Fin.append_right]
  rw [hs] at h
  convert h using 1
  apply Set.ext
  intro x
  constructor
  · rintro ⟨u,hu⟩
    let p : Point (M := M) 0 (rvObjectArity U.object) := (Fin.elim0,u.val)
    refine ⟨gammaPointCode p,⟨p,u.property,rfl⟩,?_⟩
    simpa only [gammaPointCode,Function.comp_def,Fin.append_right] using hu
  · rintro ⟨z,⟨p,hp,rfl⟩,he⟩
    refine ⟨⟨p.2,hp⟩,?_⟩
    simpa only [gammaPointCode,Function.comp_def,Fin.append_right] using he

theorem gammaRawObjectVolume_definable (U : GammaRVObject B k) :
    DefinableOverBase B (fun _ => .rv) (gammaRawObjectVolume U) := by
  let a := rvObjectArity U.object
  have h := DefinableOverBase.image_real U.volume_graph (pureRVPairCoordinates a k)
  have hs : Fin.append (gammaPointSort 0 a) (gammaPointSort 0 k) ∘ pureRVPairCoordinates a k =
      (fun _ => SortTag.rv) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp only [pureRVPairCoordinates,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
        Fin.append_left,Fin.append_right,gammaPointSort]
  rw [hs] at h
  convert h using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨u,hu⟩
    let p : Point (M := M) 0 a := (Fin.elim0,u.val)
    let q : Point (M := M) 0 k := (Fin.elim0,gammaVolumeValue U u)
    refine ⟨Fin.append (gammaPointCode p) (gammaPointCode q),⟨p,q,⟨u,rfl,rfl⟩,rfl⟩,?_⟩
    exact (pureRVPairCoordinates_code p q).trans hu
  · rintro ⟨_,⟨p,q,⟨u,hp,hq⟩,rfl⟩,he⟩
    refine ⟨u,?_⟩
    have hpr := pureRVPairCoordinates_code p q
    have hl : (fun j => (u.val j).val) = (fun j => (p.2 j).val) := congrArg (fun v => fun j => (v j).val) hp
    have hr : (fun j => (gammaVolumeValue U u j).val) = (fun j => (q.2 j).val) :=
      congrArg (fun v => fun j => (v j).val) hq
    rw [hl,hr]
    exact hpr.symm.trans he

theorem append_finAddFlip {Y : Type*} {a b : ℕ} (x : Fin a → Y) (y : Fin b → Y) :
    Fin.append x y ∘ (@finAddFlip b a) = Fin.append y x := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp only [Function.comp_apply,finAddFlip_apply_castAdd,finAddFlip_apply_natAdd,Fin.append_right,Fin.append_left]

theorem gammaRawObjectVolume_reverse_definable (U : GammaRVObject B k) :
    DefinableOverBase B (Fin.append (fun _ : Fin k => .rv) (fun _ : Fin (rvObjectArity U.object) => .rv))
      {z | Fin.append (fun j => z (Fin.natAdd k j)) (fun j => z (Fin.castAdd (rvObjectArity U.object) j))
        ∈ gammaRawObjectVolume U} := by
  let a := rvObjectArity U.object
  have h := (gammaRawObjectVolume_definable U).image_real (@finAddFlip k a)
  have hs : (fun _ : Fin (a+k) => SortTag.rv) ∘ (@finAddFlip k a) =
      Fin.append (fun _ : Fin k => .rv) (fun _ : Fin a => .rv) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp only [Function.comp_apply,Fin.append_left,Fin.append_right]
  rw [hs] at h
  convert h using 1
  apply Set.ext
  intro z
  constructor
  · intro hz
    exact ⟨Fin.append (fun j => z (Fin.natAdd k j)) (fun j => z (Fin.castAdd a j)),hz,by
      change Fin.append (fun j => z (Fin.natAdd k j)) (fun j => z (Fin.castAdd a j)) ∘ (@finAddFlip k a) = z
      rw [append_finAddFlip]
      exact Fin.append_castAdd_natAdd⟩
  · rintro ⟨v,hv,he⟩
    have hleft : (fun j => z (Fin.natAdd k j)) = fun j => v (Fin.castAdd k j) := by
      funext j
      simpa only [Function.comp_apply,finAddFlip_apply_natAdd] using (congrFun he (Fin.natAdd k j)).symm
    have hright : (fun j => z (Fin.castAdd a j)) = fun j => v (Fin.natAdd a j) := by
      funext j
      simpa only [Function.comp_apply,finAddFlip_apply_castAdd] using (congrFun he (Fin.castAdd a j)).symm
    change Fin.append (fun j => z (Fin.natAdd k j)) (fun j => z (Fin.castAdd a j)) ∈ gammaRawObjectVolume U
    rw [hleft,hright,Fin.append_castAdd_natAdd]
    exact hv

end IntegrationInACVF.Section6
