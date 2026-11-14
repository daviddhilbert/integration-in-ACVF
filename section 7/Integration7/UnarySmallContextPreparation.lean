import Integration7.GammaFiniteFamilyContexts
import IntegrationSection5.UnaryBijectionPreparation

/-! The checked Section5.2 construction in a small containing context.
The proof follows UnaryBijectionPreparation, replacing the finite partition's
real presentation by gamma_finite_family_context. No smallness or field
property of an arbitrary presentation set is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem unary_bijection_preparation_in_context
    (C : BaseContext M) (P : GammaParameters.Base (M := M))
    (hPC : P.real ⊆ (C.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ P.gamma) (hδ1 : 1 < δ)
    (FBase : VFFieldBase P.real) {m l : ℕ}
    {A : DefSet (M := M) (C.base : Set M) 1 m}
    {B : DefSet (M := M) (C.base : Set M) 1 l}
    (f : Map A B) (hf : Function.Bijective f)
    (hADef : GammaSetDefinable P (carrier A))
    (hBDef : GammaSetDefinable P (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
    ∃ r s : ℕ, ∃ A' : DefSet (M := M) (D.base : Set M) 1 r,
      ∃ B' : DefSet (M := M) (D.base : Set M) 1 s,
      ∃ TA : SpecialBijection (extendBase A hCD) A',
      ∃ TB : SpecialBijection (extendBase B hCD) B',
        let fD := @SpecialTransformations.DefinableGeometry.Map.extend LRV M
          (@CanonicalStructure.normalize M sM) (pointSpace 1 m) (pointSpace 1 l)
          (C.base : Set M) (D.base : Set M) A B f hCD
        GammaChainDefinable P TA.chain ∧ GammaChainDefinable P TB.chain ∧
        IsRVPullback (carrier A') ∧ IsRVPullback (carrier B') ∧
        Contractible (unaryConjugate TA TB fD) ∧
        Contractible (Map.inverse (unaryConjugate TA TB fD)
          (unaryConjugate_bijective TA TB fD hf)) ∧
        GammaGraphDefinable P (pointMapGraph (unaryConjugate TA TB fD)) ∧
        ∃! g : Map (keyImage A') (keyImage B'), Function.Bijective g ∧
          ∀ a : A', g (toKeyImage A' a) =
            toKeyImage B' (unaryConjugate TA TB fD a) := by
  have hsmall : Cardinal.mk P.real < C.κ :=
    (Cardinal.mk_le_mk_of_subset hPC).trans_lt C.small
  obtain ⟨F, hF, hCover⟩ := unary_coordinate_partition C.uncountable.le
    C.saturated hsmall C.model00 δ hδ hδ1 f hf.1 hfDef
  let I := (F : Finset (Set (Fin 1 ⊕ Fin m → M)))
  let U : I → Set (Point (M := M) 1 m) := fun i => {p | pointValues p ∈ i.val}
  have hU : ∀ i, GammaSetDefinable P (U i) := fun i => (hF i.val i.property).2.1
  obtain ⟨D, hCD, Q, hQ⟩ := gamma_finite_family_context C P hPC U hU
  let AD := extendBase A hCD
  let BD := extendBase B hCD
  let fD : Map AD BD := @SpecialTransformations.DefinableGeometry.Map.extend LRV M
    (@CanonicalStructure.normalize M sM) (pointSpace 1 m) (pointSpace 1 l)
    (C.base : Set M) (D.base : Set M) A B f hCD
  have hQDef : ∀ i ∈ (Finset.univ : Finset I),
      GammaSetDefinable P (carrier (Q i)) := by
    intro i _
    rw [hQ i]
    exact hU i
  have hQCover : ∀ a : AD, ∃ i ∈ (Finset.univ : Finset I), a.val ∈ carrier (Q i) := by
    intro a
    obtain ⟨W, hW, haW⟩ := hCover ⟨a.val, a.property⟩
    let i : I := ⟨W, hW⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [hQ i]
    exact haW
  have hQOpen : ∀ i ∈ (Finset.univ : Finset I),
      CoordinateOpenToOpen.At (pointValues '' carrier (Q i))
        (unaryTupleMap fD) (.inl 0) (.inl 0) := by
    intro i _
    have hsub : pointValues '' carrier (Q i) ⊆ i.val := by
      rintro z ⟨p, hp, rfl⟩
      rw [hQ i] at hp
      exact hp
    exact CoordinateOpenToOpen.at_mono hsub (unaryTupleMap fD) (.inl 0) (.inl 0)
      (hF i.val i.property).2.2
  refine ⟨D, hCD, ?_⟩
  exact unary_bijection_from_partition C.saturated C.model00 hsmall FBase
    (fun _ h => hCD (hPC h)) fD hf hADef hBDef hfDef Q Finset.univ
    hQDef hQCover hQOpen

end IntegrationInACVF.Section7
