import IntegrationSection6.FiniteVFIntegralValues
import IntegrationSection6.GammaMixedProducts
import Section4.PositivePresentation
import Section5.GammaSurjectivity
import Section7.GammaScissors

/-! The representative-independent integration value of an actual VF[k]
object with finite RV fibres. Representatives come from the checked5.7
surjectivity theorem; independence uses the proved6.17 kernel implication. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

structure GammaVFAllFiniteObject (B : Base (M := M)) where
  arity : ℕ × ℕ
  domain : Set (Point (M := M) arity.1 arity.2)
  definable : GammaSetDefinable B domain
  finiteFibres : ∀ x, {t | (x,t) ∈ domain}.Finite

def gammaVFAllFromBounded (A : GammaVFFiniteObject B k) : GammaVFAllFiniteObject B :=
  ⟨A.val.arity,A.val.domain,A.val.definable,A.property⟩

theorem gammaDimension_mono {n a i j : ℕ} {A : Set (Point (M := M) n a)}
    (h : GammaHasVFDimLE B A i) (hij : i ≤ j) : GammaHasVFDimLE B A j := by
  obtain ⟨d,hd,r,l,f,hf,hΓ⟩ := h
  exact ⟨d,hd.trans hij,r,l,f,hf,hΓ⟩

def gammaVFAllBounded (A : GammaVFAllFiniteObject B) : GammaVFFiniteObject B A.arity.1 :=
  ⟨⟨A.arity,A.domain,A.definable,(gammaIso_reflexive A.domain A.definable).dimension_le⟩,A.finiteFibres⟩

def gammaVFAllAtDegree (A : GammaVFAllFiniteObject B) (n : ℕ) (hn : A.arity.1 ≤ n) : GammaVFFiniteObject B n :=
  ⟨⟨A.arity,A.domain,A.definable,gammaDimension_mono (gammaVFAllBounded A).val.dimension hn⟩,A.finiteFibres⟩

def gammaVFAllProduct (A C : GammaVFAllFiniteObject B) : GammaVFAllFiniteObject B :=
  ⟨(A.arity.1+C.arity.1,A.arity.2+C.arity.2),mixedProductSet A.domain C.domain,
    gamma_mixed_product_set A.definable C.definable,mixedProductSet_finite_fibres A.finiteFibres C.finiteFibres⟩

def gammaVFAllEmpty (B : Base (M := M)) : GammaVFAllFiniteObject B where
  arity := (0,0)
  domain := ∅
  definable := gamma_empty_set 0
  finiteFibres := fun _ => Set.finite_empty

def gammaVFAllUnit (B : Base (M := M)) : GammaVFAllFiniteObject B where
  arity := (0,0)
  domain := Set.univ
  definable := (gammaLogicInput B).real_set _ (setDefinable (PresentedSet.univ (pointSpace (M := M) 0 0) B.real))
  finiteFibres := fun _ => Set.toFinite _

def gammaVFAllPacked (A : GammaVFAllFiniteObject B) : Set (Σ a : ℕ × ℕ, Point (M := M) a.1 a.2) :=
  Set.range (fun x : A.domain => Sigma.mk A.arity x.val)

def GammaVFAllScissor (A C D E : GammaVFAllFiniteObject B) : Prop :=
  A.arity = C.arity ∧ A.arity = D.arity ∧ A.arity = E.arity ∧
    gammaVFAllPacked D = gammaVFAllPacked A ∪ gammaVFAllPacked C ∧
    gammaVFAllPacked E = gammaVFAllPacked A ∩ gammaVFAllPacked C

def gammaVFAllPositivePresentation (B : Base (M := M)) : PositiveGrothendieck.Presentation (GammaVFAllFiniteObject B) where
  iso A C := Nonempty (GammaIso B A.domain C.domain)
  empty := gammaVFAllEmpty B
  unit := gammaVFAllUnit B
  product := gammaVFAllProduct
  scissor := GammaVFAllScissor

abbrev GammaVFAllKPlus (B : Base (M := M)) := PositiveGrothendieck.KPlus (gammaVFAllPositivePresentation B)

end IntegrationInACVF.Section6.FiniteRV
