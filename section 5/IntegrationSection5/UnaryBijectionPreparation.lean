import IntegrationSection5.UnaryBijectionFromPartition
import IntegrationSection5.UnaryCoordinatePartition
import IntegrationSection5.FiniteGammaPresentation

/-! Lemma5.2: compatible preparation of an arbitrary unary definable
bijection over the original real/Gamma base. The partition, membership
preparation, focus graphs and inverse preparation are all constructed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem lemma_5_2_gamma_presented {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ : δ ∈ P.gamma) (hδ1 : 1 < δ)
    (FBase : VFFieldBase P.real) (hPS : P.real ⊆ S)
    (f : Map A B) (hf : Function.Bijective f)
    (hADef : GammaSetDefinable P (carrier A)) (hBDef : GammaSetDefinable P (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) :
    ∃ R : Set M, ∃ hSR : S ⊆ R,
    ∃ r s : ℕ, ∃ A' : DefSet (M := M) R 1 r, ∃ B' : DefSet (M := M) R 1 s,
      ∃ TA : SpecialBijection (extendBase A hSR) A', ∃ TB : SpecialBijection (extendBase B hSR) B',
        let fR := @SpecialTransformations.DefinableGeometry.Map.extend LRV M
          (@CanonicalStructure.normalize M sM) (pointSpace 1 m) (pointSpace 1 l) S R A B f hSR
        GammaChainDefinable P TA.chain ∧ GammaChainDefinable P TB.chain ∧
        IsRVPullback (carrier A') ∧ IsRVPullback (carrier B') ∧
        Contractible (unaryConjugate TA TB fR) ∧
        Contractible (Map.inverse (unaryConjugate TA TB fR) (unaryConjugate_bijective TA TB fR hf)) ∧
        GammaGraphDefinable P (pointMapGraph (unaryConjugate TA TB fR)) ∧
        ∃! g : Map (keyImage A') (keyImage B'), Function.Bijective g ∧
          ∀ a : A', g (toKeyImage A' a) = toKeyImage B' (unaryConjugate TA TB fR a) := by
  classical
  obtain ⟨F,hF,hCover⟩ := unary_coordinate_partition hκ hs hsmall h00 δ hδ hδ1 f hf.1 hfDef
  let I := (F : Finset (Set (Fin 1 ⊕ Fin m → M)))
  let U : I → Set (Point (M := M) 1 m) := fun i => {p | pointValues p ∈ i.val}
  have hU : ∀ i, GammaSetDefinable P (U i) := fun i => (hF i.val i.property).2.1
  obtain ⟨R,hSR,D,hD⟩ := family_gamma_real_presentation U hU hPS
  let AR := extendBase A hSR
  let BR := extendBase B hSR
  let fR : Map AR BR := @SpecialTransformations.DefinableGeometry.Map.extend LRV M
          (@CanonicalStructure.normalize M sM) (pointSpace 1 m) (pointSpace 1 l) S R A B f hSR
  have hDDef : ∀ i ∈ (Finset.univ : Finset I), GammaSetDefinable P (carrier (D i)) := by
    intro i _
    rw [hD i]
    exact hU i
  have hDCover : ∀ a : AR, ∃ i ∈ (Finset.univ : Finset I), a.val ∈ carrier (D i) := by
    intro a
    obtain ⟨W,hW,haW⟩ := hCover ⟨a.val,a.property⟩
    let i : I := ⟨W,hW⟩
    refine ⟨i,Finset.mem_univ _,?_⟩
    rw [hD i]
    exact haW
  have hDOpen : ∀ i ∈ (Finset.univ : Finset I),
      CoordinateOpenToOpen.At (pointValues '' carrier (D i)) (unaryTupleMap fR) (.inl 0) (.inl 0) := by
    intro i _
    have hsub : pointValues '' carrier (D i) ⊆ i.val := by
      rintro z ⟨p,hp,rfl⟩
      rw [hD i] at hp
      exact hp
    exact CoordinateOpenToOpen.at_mono hsub (unaryTupleMap fR) (.inl 0) (.inl 0) (hF i.val i.property).2.2
  refine ⟨R,hSR,?_⟩
  exact unary_bijection_from_partition hs h00 hsmall FBase (fun _ h => hSR (hPS h))
    fR hf hADef hBDef hfDef D Finset.univ hDDef hDCover hDOpen

end IntegrationInACVF.Section5
