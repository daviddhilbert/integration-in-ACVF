import Integration7.VolumeAlmostEverywhere
import Integration7.DefinableMapPreimages

/-! Pulling a small exceptional set back through a finite-fibre map. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {a b n : ℕ}

theorem RVAlmostEverywhere.pullback_finite
    {A : DefSet (rawRVSpace (M := M) a) S} {B : DefSet (rawRVSpace (M := M) b) S}
    (F : Map A B) (hF : F.FiniteFibres) {P : B → Prop}
    (hP : RVAlmostEverywhere B n P) : RVAlmostEverywhere A n (fun x => P (F x)) := by
  obtain ⟨D,hDB,hd,hP⟩ := hP
  let E := definableMapPreimage F D
  have hEA := definableMapPreimage_subset F D
  let g := (F.restrict hEA).corestrict (fun x =>
    (mem_definableMapPreimage F D ⟨x.val,hEA x.property⟩).mp x.property)
  have hg : g.FiniteFibres := by
    intro z
    apply ((hF.restrict hEA) (⟨z.val,hDB z.property⟩ : B)).subset
    intro x hx
    exact Subtype.ext (congrArg (fun v : D => v.val) hx)
  refine ⟨E,hEA,(rvDim_le_of_finite_map g hg).trans_lt hd,?_⟩
  intro u hu
  exact hP (F u) (fun h => hu ((mem_definableMapPreimage F D u).mpr h))

end IntegrationInACVF.Section7
