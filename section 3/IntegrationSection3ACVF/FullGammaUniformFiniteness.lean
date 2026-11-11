import IntegrationSection3ACVF.FullGammaCounting
import IntegrationSection3ACVF.FiniteBaseTupleCovers

/-! Genuine uniform finiteness of actual Gamma rows. The first-order
count is on distinct quotient values, not the infinite RV code fibres.
Only finite formula support is specialized internally. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullGammaUniformFiniteness

variable {M α : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [Finite α]

theorem exists_bound {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (P : (α ⊕ Fin 1 → Values.Gamma (M := M)) → Prop)
    (hP : FullGammaSyntax.Definable B P)
    (hFinite : ∀ a : α → Values.Gamma (M := M), (FullGammaCounting.row P a).Finite) :
    ∃ N : ℕ, ∀ a : α → Values.Gamma (M := M), (FullGammaCounting.row P a).ncard ≤ N := by
  classical
  obtain ⟨F,hF,hData⟩ := hP
  let B0 : FullBaseAtomicity.Base (M := M) := ⟨B.real,(F : Set (ParameterPresentation.Name (M := M)))⟩
  have hP0 : FullGammaSyntax.Definable B0 P := ⟨F,fun _ hi => hi,hData⟩
  let D (k : ℕ) : Set (α → M) :=
    {a | GammaSyntax.Proper a ∧ ¬ FullGammaCounting.hasMore P k (GammaSyntax.decode a)}
  have hD (k : ℕ) : FullBaseAtomicity.OverBase B0 (D k) :=
    (FullGammaCounting.hasMore_definable B0 P hP0 k).not
  have hCover (a : α → M) (ha : GammaSyntax.Proper a) : ∃ U ∈ Set.range D, a ∈ U := by
    let k := (FullGammaCounting.row P (GammaSyntax.decode a)).ncard
    refine ⟨D k,⟨k,rfl⟩,ha,?_⟩
    exact fun hMore => (FullGammaCounting.hasMore_iff P _ k).mp hMore ⟨hFinite _,le_rfl⟩
  obtain ⟨G,hG,hCov⟩ := FiniteBaseTupleCovers.finite_subcover hκ hs B0 F.finite_toSet hsmall
    {a : α → M | GammaSyntax.Proper a} (FullGammaSyntax.proper_definable B0)
    (Set.range D) (by rintro U ⟨k,rfl⟩; exact hD k) hCover
  have hCode (U : G) : ∃ k, D k = U.val := hG U.val U.property
  choose k hk using hCode
  let N := ∑ U : G, k U
  refine ⟨N,?_⟩
  intro a
  choose c hc hca using fun j => EndpointLogic.codeValue_surjective (a j)
  have he : GammaSyntax.decode c = a := funext hca
  obtain ⟨U,hUG,hcU⟩ := hCov c hc
  let u : G := ⟨U,hUG⟩
  have hcD : c ∈ D (k u) := by rw [hk u]; exact hcU
  have hLe : (FullGammaCounting.row P a).ncard ≤ k u := by
    have hNot := hcD.2
    rw [he] at hNot
    exact ((GammaParameters.no_injection_iff_finite_ncard_le).mp hNot).2
  exact hLe.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ u))

end IntegrationInACVF.Section3ACVF.FullGammaUniformFiniteness
