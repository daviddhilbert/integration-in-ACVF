import Section4.RVFiniteScissors
import Section4.RVIsoTools

/-! Morphism construction in RV[k] only. Finite input volume fibres
supply finite volume images for any definable map satisfying the weight
inequality. Weight-preserving definable bijections give RV[k] isomorphisms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

def homOfDefinableMap (U V : RVFiniteObject (M := M) S k)
    (F : Map U.obj.domain V.obj.domain)
    (hw : ∀ a, rvWeight (U.obj.value a) ≤ rvWeight (V.obj.value (F a))) : U ⟶ V :=
  ObjectProperty.homMk {
    map := F
    volumetric := hw
    finite_volume_images := by
      intro t
      have hf : {a : U.obj.domain | U.obj.value a = t}.Finite := by
        apply (U.property ⟨t,Set.mem_univ _⟩).subset
        intro a ha
        exact Subtype.ext ha
      apply (hf.image (fun a => V.obj.value (F a))).subset
      rintro s ⟨a,ha,hs⟩
      exact ⟨a,ha,hs⟩ }

def isoOfDefinableBijection (U V : RVFiniteObject (M := M) S k)
    (F : Map U.obj.domain V.obj.domain) (hF : Function.Bijective F)
    (hw : ∀ a, rvWeight (U.obj.value a) = rvWeight (V.obj.value (F a))) : U ≅ V where
  hom := homOfDefinableMap U V F (fun a => (hw a).le)
  inv := homOfDefinableMap V U (F.inverse hF) (by
    intro v
    have h := hw (F.inverse hF v)
    rw [Map.apply_inverse] at h
    exact h.ge)
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply RVHom.ext
    apply Map.ext
    intro u
    exact Map.inverse_apply F hF u
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply RVHom.ext
    apply Map.ext
    intro v
    exact Map.apply_inverse F hF v

end IntegrationInACVF.Section6.FiniteRV
