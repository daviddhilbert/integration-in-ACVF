import Integration7.GammaNativeCommonNames
import Section5.GammaGraphs

/-! Actual Gamma special chains admit fixed-name real presentations.
Each focus has exactly its original geometry; only definability proofs change. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S R : Set M} {n m l : ℕ}

def gammaNativePresentation (A : DefSet (M := M) S n m)
    (hA : GammaSetDefinable P (carrier A)) (hNames : commonRealNames P ⊆ R) :
    DefSet (M := M) R n m :=
  PresentedSet.mk (carrier A) (SetDefinable.mono _ (gamma_native_set_common_names hA) hNames)

def gammaFocusPresentation {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
    (D : Focus A j k) (hA : GammaSetDefinable P (carrier A))
    (hD : GammaFocusDefinable P D) (hNames : commonRealNames P ⊆ R) :
    Focus (gammaNativePresentation A hA hNames) j k where
  toFocusGeometry := D.toFocusGeometry
  locus_definable := SetDefinable.mono _ (gamma_native_set_common_names hD.1) hNames
  center_graph := RelationDefinable.mono _ _ (gamma_native_scalar_common_names
    (r := fun p z => p ∈ carrier A ∩ D.locus ∧ z = D.center p) hD.2) hNames

private def chainCastSource {a b : ℕ} {A A' : DefSet (M := M) R n a}
    {B : DefSet (M := M) R n b} (T : Chain R n A B) (h : A = A') : Chain R n A' B := h ▸ T

private theorem chainCastSource_gamma {a b : ℕ} {A A' : DefSet (M := M) R n a}
    {B : DefSet (M := M) R n b} (T : Chain R n A B) (h : A = A')
    (hT : GammaChainDefinable P T) : GammaChainDefinable P (chainCastSource T h) := by
  subst A'
  exact hT

private theorem chainCastSource_alternating {a b : ℕ} {A A' : DefSet (M := M) R n a}
    {B : DefSet (M := M) R n b} (T : Chain R n A B) (h : A = A') (prev : Option Bool)
    (hT : T.Alternating prev) : (chainCastSource T h).Alternating prev := by
  subst A'
  exact hT

private theorem chainCastSource_apply {a b : ℕ} {A A' : DefSet (M := M) R n a}
    {B : DefSet (M := M) R n b} (T : Chain R n A B) (h : A = A') (p : A') :
    ((chainCastSource T h).toMap p).val =
      (T.toMap ⟨p.val,(Set.ext_iff.mp (congrArg carrier h) p.val).mpr p.property⟩).val := by
  subst A'
  rfl

def gammaChainPresentation {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (T : Chain S n A B) (hT : GammaChainDefinable P T) (hNames : commonRealNames P ⊆ R) :
    Chain R n (gammaNativePresentation A (hT.source P T) hNames)
      (gammaNativePresentation B (hT.target P T) hNames) := by
  induction T with
  | nil A => exact .nil _
  | @cons a b c A B C p tail ih =>
    cases p with
    | canonical A =>
      exact .cons (.canonical (gammaNativePresentation A hT.1 hNames)) (ih hT.2)
    | centripetal D =>
      have he : (gammaFocusPresentation D hT.1.1 hT.1.2 hNames).etaImage =
          gammaNativePresentation D.etaImage (GammaChainDefinable.source P tail hT.2) hNames :=
        PresentedSet.eq_of_carrier_eq rfl
      exact .cons (.centripetal (gammaFocusPresentation D hT.1.1 hT.1.2 hNames))
        (chainCastSource (ih hT.2) he.symm)

theorem gamma_chain_presentation_gamma {A : DefSet (M := M) S n m}
    {B : DefSet (M := M) S n l} (T : Chain S n A B)
    (hT : GammaChainDefinable P T) (hNames : commonRealNames P ⊆ R) :
    GammaChainDefinable P (gammaChainPresentation T hT hNames) := by
  induction T with
  | nil A => exact hT
  | cons p tail ih =>
    cases p with
    | canonical A => exact ⟨hT.1,ih hT.2⟩
    | centripetal D => exact ⟨hT.1,chainCastSource_gamma _ _ (ih hT.2)⟩

theorem gamma_chain_presentation_alternating {A : DefSet (M := M) S n m}
    {B : DefSet (M := M) S n l} (T : Chain S n A B)
    (hT : GammaChainDefinable P T) (hNames : commonRealNames P ⊆ R)
    (prev : Option Bool) (hAlt : T.Alternating prev) :
    (gammaChainPresentation T hT hNames).Alternating prev := by
  induction T generalizing prev with
  | nil A => trivial
  | cons p tail ih =>
    cases p with
    | canonical A => exact ⟨hAlt.1,ih hT.2 _ hAlt.2⟩
    | centripetal D => exact ⟨hAlt.1,chainCastSource_alternating _ _ _ (ih hT.2 _ hAlt.2)⟩

theorem gamma_chain_presentation_apply {A : DefSet (M := M) S n m}
    {B : DefSet (M := M) S n l} (T : Chain S n A B)
    (hT : GammaChainDefinable P T) (hNames : commonRealNames P ⊆ R)
    (p : gammaNativePresentation A (hT.source P T) hNames) :
    ((gammaChainPresentation T hT hNames).toMap p).val = (T.toMap ⟨p.val,p.property⟩).val := by
  induction T with
  | nil A => rfl
  | cons prim tail ih =>
    cases prim with
    | canonical A => exact ih hT.2 _
    | centripetal D =>
      change ((chainCastSource _ _).toMap
        ((Primitive.centripetal (gammaFocusPresentation D hT.1.1 hT.1.2 hNames)).toMap p)).val = _
      rw [chainCastSource_apply]
      exact ih hT.2 _

def gammaSpecialPresentation {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (T : SpecialBijection A B) (hT : GammaChainDefinable P T.chain)
    (hNames : commonRealNames P ⊆ R) :
    SpecialBijection (gammaNativePresentation A (hT.source P T.chain) hNames)
      (gammaNativePresentation B (hT.target P T.chain) hNames) where
  chain := gammaChainPresentation T.chain hT hNames
  alternating := gamma_chain_presentation_alternating T.chain hT hNames none T.alternating

end IntegrationInACVF.Section7
