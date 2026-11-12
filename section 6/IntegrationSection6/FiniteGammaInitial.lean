import IntegrationSection6.FiniteGammaCategoricalCoproducts

/-! Empty objects and the initial object in the finite original-Gamma category. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gamma_empty_set (a : ℕ) : GammaSetDefinable B (∅ : Set (Point (M := M) 0 a)) := by
  let A := @SpecialTransformations.DefinableGeometry.DefSet.empty LRV M N (@pointSpace M sM hM 0 a) B.real
  exact (gammaLogicInput B).real_set (carrier A) (setDefinable A)

theorem gamma_empty_graph (a b : ℕ) :
    GammaGraphDefinable B (fun (_ : Point (M := M) 0 a) (_ : Point (M := M) 0 b) => False) := by
  let Q := PresentedSet.univ (pointSpace (M := M) 0 b) B.real
  let F := @SpecialTransformations.DefinableGeometry.Map.emptyTo LRV M N (@pointSpace M sM hM 0 a) _ B.real Q
  apply GammaGraphDefinable.congr ((gammaLogicInput B).real_map_graph F)
  intro p q
  constructor
  · rintro ⟨x,hx,hq⟩
    exact False.elim x.property
  · intro h
    exact False.elim h

def gammaEmptyAt (hBS : B.real ⊆ S) : GammaObjectAt B S n where
  object := @rvFiniteEmpty M N S n
  real_contains := hBS
  domain_graph := by
    change GammaSetDefinable B (∅ : Set (Point (M := M) 0 0))
    exact gamma_empty_set 0
  volume_graph := by
    apply GammaGraphDefinable.congr (gamma_empty_graph (B := B) 0 n)
    intro p q
    constructor
    · intro h; exact False.elim h
    · rintro ⟨u,hu,hv⟩; exact False.elim u.property

def gammaEmptyHomAt (hBS : B.real ⊆ S) (U : GammaObjectAt B S n) : gammaEmptyAt hBS ⟶ U where
  hom := ObjectProperty.homMk (@rvEmptyHom M N S n U.object.obj)
  graph := by
    apply GammaGraphDefinable.congr (gamma_empty_graph (B := B) 0 (rvObjectArity U.object.obj))
    intro p q
    constructor
    · intro h; exact False.elim h
    · rintro ⟨u,hu,hv⟩; exact False.elim u.property

def gammaEmptyIsInitial (hBS : B.real ⊆ S) : IsInitial (gammaEmptyAt (n := n) hBS) :=
  IsInitial.ofUniqueHom (gammaEmptyHomAt hBS) (fun U f => by
    apply GammaHomAt.hom_ext
    apply ObjectProperty.hom_ext
    apply @RVHom.ext M N S n _ _
    apply @SpecialTransformations.DefinableGeometry.Map.ext LRV M N _ _ S _ _
    intro a
    exact False.elim a.property)

instance gammaAtHasInitial [hBS : Fact (B.real ⊆ S)] : HasInitial (GammaObjectAt B S n) :=
  (gammaEmptyIsInitial (n := n) hBS.out).hasInitial

end IntegrationInACVF.Section6.FiniteRV
