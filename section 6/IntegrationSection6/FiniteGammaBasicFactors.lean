import IntegrationSection6.GammaElementaryDomains
import IntegrationSection6.GammaRVGlobalRestriction
import IntegrationSection6.FiniteGammaObjects
import Section3.RVOperations

/-! The degree-one singleton and positive-parameter objects, in the
actual finite-volume category and over the original Gamma base. The
positive object includes the absorbing RV point. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M}

def constantOneVolumeMap (S : Set M) {a : ℕ}
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M sM (@SpecialTransformations.Section4.rawRVSpace M sM a) S) :=
  @rvMapOfCode M sM S a 1 A (fun _ => fun _ => (1 : CanonicalRV.RVSort M))
    (fun _ => fun _ => iRVOne)
    (fun _ => by simpa using rvConstantCode_definable (M := M) S (ι := Fin a) true)
    (fun _ => funext (fun _ => RVOperations.one_val))

def oneVolumeRVObject (S : Set M) : RVFiniteObject (M := M) S 1 :=
  ⟨RVObject.mk 0
    (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M sM (@SpecialTransformations.Section4.rawRVSpace M sM 0) S)
    (constantOneVolumeMap S _),fun _ => Set.toFinite _⟩

def positiveVolumeRVObject (S : Set M) : RVFiniteObject (M := M) S 1 :=
  ⟨RVObject.mk 1 (positiveRV S) (selectRVTuple id (positiveRV S)),
    @SpecialTransformations.DefinableGeometry.Map.finiteFibres_of_injective LRV M sM _ _ S _ _ _
      (fun u v h => Subtype.ext (congrArg
        (fun q : @SpecialTransformations.DefinableGeometry.DefSet.univ LRV M sM
          (@SpecialTransformations.Section4.rawRVSpace M sM 1) S => q.val) h))⟩

variable {B : Base (M := M)}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaOneAt (hBS : B.real ⊆ S) : GammaObjectAt B S 1 where
  object := @oneVolumeRVObject M N hN S
  real_contains := hBS
  domain_graph := gamma_rv_set_of_real
    (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N 0) B.real)
  volume_graph := gamma_rv_graph_of_global_formula
    (@constantOneVolumeMap M N hN S 0
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N 0) S))
    (@constantOneVolumeMap M N hN B.real 0
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N 0) B.real))
    (gamma_rv_set_of_real
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N 0) B.real))
    (fun _ => rfl)

def gammaPositiveAt (hBS : B.real ⊆ S) : GammaObjectAt B S 1 where
  object := @positiveVolumeRVObject M N S
  real_contains := hBS
  domain_graph := gamma_positiveRV
  volume_graph := gamma_rv_graph_of_global_formula
    (@selectRVTuple M N S 1 1 id (@positiveRV M N S))
    (@selectRVTuple M N B.real 1 1 id
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N 1) B.real))
    gamma_positiveRV (fun _ => rfl)

end IntegrationInACVF.Section6.FiniteRV
