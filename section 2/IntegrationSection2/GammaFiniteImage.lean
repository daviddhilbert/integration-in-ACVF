import Section3.Library
import Section4.Library

/-!
# Corollary 2.15: finite image of a Gamma-to-RV function

The pinned predecessor proves the stronger finite-projection result for a
uniform Gamma-to-RV relation with finite rows. Apply it to the full graph of
a partial function. Gamma parameters in the base are removed only inside
the finiteness proof by the predecessor's finite-support specialization.
The stated graph retains every RV representative of every Gamma input.
-/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section2

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def gammaRVGraph (A : Set (Values.Gamma (M := M))) (f : A → M) : Set (M × M) :=
  {p | NonzeroRV p.1 ∧ ∃ γ : A, γ.val = codeValue p.1 ∧ f γ = p.2}

/-- Corollary 2.15 over an arbitrary small real base. The genuine saturation
and characteristic-zero assumptions are inherited from the proved theorem. -/
theorem corollary_2_15_real_base {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (Q : Set M) (hsmall : Cardinal.mk Q < κ)
    (A : Set (Values.Gamma (M := M))) (f : A → M) (hf : ∀ γ, iRV (f γ))
    (hgraph : @Set.Definable₂ M Q LRV (CanonicalStructure.normalize (M := M))
      (gammaRVGraph A f)) : (Set.range f).Finite := by
  let F : GammaRVFamily Q :=
    { relation := fun γ t => ∃ a : A, a.val = γ ∧ f a = t
      sorted := by
        rintro γ t ⟨a,_,rfl⟩
        exact hf a
      definable := hgraph }
  have hrows (γ : Values.Gamma (M := M)) : {t | F.relation γ t}.Finite := by
    apply Set.Subsingleton.finite
    rintro x ⟨a,ha,hax⟩ y ⟨b,hb,hby⟩
    have hab : a = b := Subtype.ext (ha.trans hb.symm)
    subst b
    exact hax.symm.trans hby
  have he : Set.range f = F.nonemptyDomain := by
    ext t
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨a.val,a,rfl,rfl⟩
    · rintro ⟨γ,a,_,ha⟩
      exact ⟨a,ha⟩
  rw [he]
  exact F.finite_projection hκ hs h00 hsmall hrows

/-- Corollary 2.15 with arbitrary genuine Gamma names in the base. The
entire graph is definable over that base; no chosen representative is part
of the hypothesis. Only its real part needs the usual smallness bound. -/
theorem corollary_2_15 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (A : Set (Values.Gamma (M := M))) (f : A → M) (hf : ∀ γ, iRV (f γ))
    (hgraph : DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | (z 0,z 1) ∈ gammaRVGraph A f}) : (Set.range f).Finite := by
  obtain ⟨k,t,hG⟩ := hgraph.specialize
  have hraw := ((definableOver_iff_normalized_raw
    (B.real ∪ Set.range (rawTuple t)) (fun _ : Fin 2 => .rv) _).mp hG).1
  exact corollary_2_15_real_base hκ hs h00 (B.real ∪ Set.range (rawTuple t))
    (small_union_range hκ B.real hsmall (rawTuple t)) A f hf hraw

end IntegrationInACVF.Section2
