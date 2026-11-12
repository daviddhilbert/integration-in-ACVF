import IntegrationSection6.GammaPermutedFibrePresentations
import IntegrationSection5.GammaGraphOperations
import IntegrationSection5.RelativelyUnary

/-! Conjugating a relatively unary map by a VF permutation moves its active
coordinate to the head and preserves every selected old RV label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a b k : ℕ}
variable {U : DefSet (M := M) S n a} {V : DefSet (M := M) S n b}

def vfPermutedMap (f : Map U V) (σ : Equiv.Perm (Fin n)) :
    Map (vfPermutationImage U σ) (vfPermutationImage V σ) :=
  Map.comp (vfPermutationBijection V σ)
    (Map.comp f (Map.inverse (vfPermutationBijection U σ) (vfPermutationBijection_bijective U σ)))

theorem vfPermutedMap_bijective (f : Map U V) (hf : Function.Bijective f) (σ : Equiv.Perm (Fin n)) :
    Function.Bijective (vfPermutedMap f σ) := by
  let g := vfPermutationBijection U σ
  let hg := vfPermutationBijection_bijective U σ
  have hi : Function.Bijective (Map.inverse g hg) := by
    constructor
    · intro u v he
      exact (Map.apply_inverse g hg u).symm.trans ((congrArg g he).trans (Map.apply_inverse g hg v))
    · intro a
      exact ⟨g a,Map.inverse_apply g hg a⟩
  exact (vfPermutationBijection_bijective V σ).comp (hf.comp hi)

theorem gamma_vfPermutedMap (f : Map U V) (hU : GammaSetDefinable B (carrier U))
    (hV : GammaSetDefinable B (carrier V)) (hF : GammaGraphDefinable B (pointMapGraph f))
    (σ : Equiv.Perm (Fin n)) : GammaGraphDefinable B (pointMapGraph (vfPermutedMap f σ)) :=
  gamma_composition_graph _ _
    (gamma_composition_graph _ _
      (gamma_inverse_map_graph _ (vfPermutationBijection_bijective U σ) (gamma_vfPermutation_graph U hU σ)) hF)
    (gamma_vfPermutation_graph V hV σ)

theorem vfPermutedMap_labels (f : Map U V) (σ : Equiv.Perm (Fin n))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ)
    (u : vfPermutationImage U σ) :
    ((vfPermutedMap f σ) u).val.2 ∘ τ = u.val.2 ∘ ρ := by
  let g := vfPermutationBijection U σ
  let hg := vfPermutationBijection_bijective U σ
  let a := Map.inverse g hg u
  have he := congrArg (fun v : vfPermutationImage U σ => v.val.2) (Map.apply_inverse g hg u)
  exact (hLabels a).trans (congrArg (fun r => r ∘ ρ) he)

theorem vfPermutedMap_relative {p : ℕ} {U : DefSet (M := M) S (p+1) a}
    {V : DefSet (M := M) S (p+1) b} (f : Map U V) (σ : Equiv.Perm (Fin (p+1)))
    (hi : UnaryRelative f (σ 0)) : UnaryRelative (vfPermutedMap f σ) 0 := by
  intro u j hj
  let g := vfPermutationBijection U σ
  let hg := vfPermutationBijection_bijective U σ
  let a := Map.inverse g hg u
  have he := congrArg (fun v : vfPermutationImage U σ => v.val.1 j) (Map.apply_inverse g hg u)
  change (f a).val.1 (σ j) = u.val.1 j
  exact (hi a (σ j) (fun h => hj (σ.injective h))).trans he

end IntegrationInACVF.Section6
