module

public import Integration7.NativeRelativeTranslations
public import IntegrationSection5.GammaScalarUpdate

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Replace one VF coordinate by an actual scalar map while retaining
every RV label. The complete graph retains the scalar map's original
Gamma certificate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n m : ℕ}

def nativeScalarReplacementMap (A : DefSet (M := M) S n m) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)) :
    Map A (PresentedSet.univ (pointSpace n m) S) :=
  Map.comp (replaceCoordinateMap i (PresentedSet.prod A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)))
    (Map.pair (Map.id A) c)

theorem native_scalar_replacement_value (A : DefSet (M := M) S n m) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)) (p : A) :
    (nativeScalarReplacementMap A i c p).val = replace i p.val ((c p).val 0) := rfl

theorem gamma_native_scalar_replacement_graph (A : DefSet (M := M) S n m) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hcΓ : GammaScalarGraphDefinable G (fun p z => ∃ q : A, q.val = p ∧ (c q).val 0 = z)) :
    GammaGraphDefinable G (pointMapGraph (nativeScalarReplacementMap A i c)) :=
  gamma_scalar_replacement_graph i (fun p => (c p).val 0) hcΓ

theorem native_scalar_replacement_to_image_bijective (A : DefSet (M := M) S n m) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hi : Function.Injective (nativeScalarReplacementMap A i c)) :
    Function.Bijective (Map.toImage (nativeScalarReplacementMap A i c)) := by
  constructor
  · intro p q he
    apply hi
    have hv := congrArg Subtype.val he
    exact Subtype.ext hv
  · rintro ⟨q,p,hp⟩
    exact ⟨p,Subtype.ext hp⟩

end IntegrationInACVF.Section7
