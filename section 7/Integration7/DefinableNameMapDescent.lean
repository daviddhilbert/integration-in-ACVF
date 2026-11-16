module

public import Integration7.TermClosureDefinability
public import Section4.MapParameters

@[expose] public section

/-! Maps descend across an extension consisting of already definable
names. Their actual point functions and complete graphs are preserved. -/
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

theorem eliminate_definable_names_finite_index {L : Language} {M : Type} [L.Structure M]
    {S T : Set M} {ι : Type} [Finite ι] (R : Set (ι → M))
    (hT : ∀ t ∈ T, S.Definable₁ L {t}) (hR : T.Definable L R) : S.Definable L R := by
  letI := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  have h := SpecialTransformations.DefinableConstants.eliminate_parameters
    {z : Fin (Fintype.card ι) → M | z ∘ e ∈ R} hT (hR.preimage_comp e)
  have h' := h.preimage_comp e.symm
  convert h' using 1
  ext z
  have he : (z ∘ e.symm) ∘ e = z := by
    funext i
    exact congrArg z (e.symm_apply_apply i)
  exact Iff.of_eq (congrArg (fun t => t ∈ R) he).symm

def mapDescendDefinableNames {L : Language} {M : Type} [L.Structure M]
    {P Q : Space L M} {S T : Set M} (hST : S ⊆ T)
    (hT : ∀ t ∈ T, S.Definable₁ L {t}) {A : DefSet P S} {B : DefSet Q S}
    (f : Map (A.extend hST) (B.extend hST)) : Map A B where
  toFun := f
  graph_definable := eliminate_definable_names_finite_index _ hT f.graph_definable

end IntegrationInACVF.Section7
