import IntegrationSection6.GammaCompressionIsomorphisms
import IntegrationSection6.FiniteGammaEmptyIsomorphisms
import IntegrationSection6.FiniteGammaScissorComparison
import IntegrationSection6.FiniteGammaAmbientIsos
import Section4.RVPaddingSplit
import IntegrationSection6.GammaWeightStrata
import Section4.RVFinitePadding
import IntegrationSection6.FiniteGammaIsoLaws

/-! Original-Gamma RV[k] data at a fixed internal real presentation.
The parameter set S describes codes only; every domain and volume graph
is still certified over the original Base B. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaPadCoprodIsoAt (U V : GammaObjectAt B S n) :
    GammaIsoAt (gammaPadAt (gammaCoprodAt U V)) (gammaCoprodAt (gammaPadAt U) (gammaPadAt V)) := by
  let A := gammaPadAt (gammaCoprodAt U V)
  let C := gammaCoprodAt (gammaPadAt U) (gammaPadAt V)
  let F := @SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S (rvObjectDomain A.object.obj)
  let Uo := U.object.obj
  let Vo := V.object.obj
  have hw (u : rvObjectDomain A.object.obj) :
      @rvWeight M N (n+1) (@RVObject.value M N S (n+1) A.object.obj u) =
      @rvWeight M N (n+1) (@RVObject.value M N S (n+1) C.object.obj (F u)) := by
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    change rvWeight ((rvPadObject (rvCoprodObject Uo Vo)).value u) =
      rvWeight ((rvCoprodObject (rvPadObject Uo) (rvPadObject Vo)).value u)
    rcases u.property with ⟨v,hv⟩ | ⟨v,hv⟩
    · have he : u = rvCoprodLeftMap Uo Vo v := Subtype.ext hv.symm
      rw [he,rvPadObject_value,rvCoprod_value_left]
      have ht := rvCoprod_value_left (rvPadObject Uo) (rvPadObject Vo) v
      exact (congrArg rvWeight ht).symm
    · have he : u = rvCoprodRightMap Uo Vo v := Subtype.ext hv.symm
      rw [he,rvPadObject_value,rvCoprod_value_right]
      have ht := rvCoprod_value_right (rvPadObject Uo) (rvPadObject Vo) v
      exact (congrArg rvWeight ht).symm
  exact {
    iso := @isoOfDefinableBijection M N S (n+1) A.object C.object F Function.bijective_id hw
    graph := (gammaIsoRefl A.toGamma).graph }

variable [hBS : Fact (B.real ⊆ S)]

def gammaPadClassValueAt (a : GammaIsoClassesAt B S n) : GammaIsoClassesAt B S (n+1) :=
  gammaIsoClassAt (gammaPadAt (gammaIsoClassRepresentativeAt a))

theorem gammaPadClassValueAt_class (U : GammaObjectAt B S n) :
    gammaPadClassValueAt (gammaIsoClassAt U) = gammaIsoClassAt (gammaPadAt U) := by
  obtain ⟨e⟩ := gammaIsoClassAt_eq_iff.mp (gammaIsoClassRepresentativeAt_class (gammaIsoClassAt U))
  exact gammaIsoClassAt_iso (gammaPadIsoAt e)

def gammaPaddingClassesAt : GammaIsoClassesAt B S n →+ GammaIsoClassesAt B S (n+1) where
  toFun := gammaPadClassValueAt
  map_zero' := by
    rw [← gammaIsoClassAt_empty (n := n) hBS.out,gammaPadClassValueAt_class]
    exact gammaIsoClassAt_eq_zero _ rfl
  map_add' a b := by
    obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
    obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
    rw [← gammaIsoClassAt_coprod,gammaPadClassValueAt_class,gammaPadClassValueAt_class,gammaPadClassValueAt_class]
    exact (gammaIsoClassAt_iso (gammaPadCoprodIsoAt U V)).trans (gammaIsoClassAt_coprod _ _)

theorem gammaPaddingClassesAt_class (U : GammaObjectAt B S n) :
    gammaPaddingClassesAt (gammaIsoClassAt U) = gammaIsoClassAt (gammaPadAt U) :=
  gammaPadClassValueAt_class U

theorem gammaPaddingClassesAt_injective :
    Function.Injective (gammaPaddingClassesAt (B := B) (S := S) (n := n)) := by
  intro a b he
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
  rw [gammaPaddingClassesAt_class,gammaPaddingClassesAt_class] at he
  obtain ⟨e⟩ := gammaIsoClassAt_eq_iff.mp he
  exact gammaIsoClassAt_iso (((gammaWeightProjectionPadIsoAt U).symm.trans
    (gammaWeightProjectionIsoAt e)).trans (gammaWeightProjectionPadIsoAt V))

end IntegrationInACVF.Section6.FiniteRV
