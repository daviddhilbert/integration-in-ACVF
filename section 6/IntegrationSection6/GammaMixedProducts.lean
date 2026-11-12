import IntegrationSection6.GammaRVProductRelations
import IntegrationSection6.MixedCoordinatePointMaps
import IntegrationSection5.CoordinateFibreMaps

/-! Definable insertion and projection of a VF prefix with a frozen tail. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n p m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def mixedProductLeft {a b : ℕ} (p : Point (M := M) (n+a) (m+b)) : Point (M := M) n m :=
  (p.1 ∘ Fin.castAdd a,p.2 ∘ Fin.castAdd b)

def mixedProductRight {a b : ℕ} (p : Point (M := M) (n+a) (m+b)) : Point (M := M) a b :=
  (p.1 ∘ Fin.natAdd n,p.2 ∘ Fin.natAdd m)

def mixedProductSet {a b : ℕ} (A : Set (Point (M := M) n m)) (C : Set (Point (M := M) a b)) :
    Set (Point (M := M) (n+a) (m+b)) := {p | mixedProductLeft p ∈ A ∧ mixedProductRight p ∈ C}

variable {B : SpecialTransformations.Section3.GammaParameters.Base (M := M)}

theorem gamma_mixed_product_set {a b : ℕ} {A : Set (Point (M := M) n m)} {C : Set (Point (M := M) a b)}
    (hA : GammaSetDefinable B A) (hC : GammaSetDefinable B C) : GammaSetDefinable B (mixedProductSet A C) := by
  have h := (gammaLogicInput B).inter
    ((gammaLogicInput B).preimage_real (mixedCoordinatePointMap (Fin.castAdd a) (Fin.castAdd b) B.real) hA)
    ((gammaLogicInput B).preimage_real (mixedCoordinatePointMap (Fin.natAdd n) (Fin.natAdd m) B.real) hC)
  convert h using 1
  ext p
  constructor
  · rintro ⟨hp,hq⟩
    exact ⟨⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩,⟨⟨p,Set.mem_univ _⟩,rfl,hq⟩⟩
  · rintro ⟨⟨x,hx,hA⟩,⟨y,hy,hC⟩⟩
    exact ⟨hx ▸ hA,hy ▸ hC⟩

theorem mixedProductSet_finite_fibres {a b : ℕ} {A : Set (Point (M := M) n m)} {C : Set (Point (M := M) a b)}
    (hA : ∀ x, {t | (x,t) ∈ A}.Finite) (hC : ∀ x, {t | (x,t) ∈ C}.Finite) :
    ∀ x, {t | (x,t) ∈ mixedProductSet A C}.Finite := by
  intro x
  apply (((hA (x ∘ Fin.castAdd a)).prod (hC (x ∘ Fin.natAdd n))).image
    (fun t => Fin.append t.1 t.2)).subset
  intro r hr
  exact ⟨(r ∘ Fin.castAdd b,r ∘ Fin.natAdd m),hr,Fin.append_castAdd_natAdd⟩

end IntegrationInACVF.Section6
