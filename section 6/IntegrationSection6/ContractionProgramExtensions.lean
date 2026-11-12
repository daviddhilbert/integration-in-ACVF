import IntegrationSection5.RelativeSpecialExtension
import IntegrationSection5.StandardContractionGammaNormalization

/-! Actual head and standard contraction programs extend their internal
real presentation while retaining the original mathematical Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S R : Set M} {B : Base (M := M)}

theorem specialRelative_extendBase {n a b : ℕ} {U : DefSet (M := M) S n a} {V : DefSet (M := M) S n b}
    (f : Map U V) (hSR : S ⊆ R) {i : Fin n} (hf : SpecialRelative f i) :
    SpecialRelative (extendPointMap f hSR) i := by
  obtain ⟨hi,hT⟩ := hf
  refine ⟨fun a j hj => hi a j hj,?_⟩
  intro u
  obtain ⟨T,hT⟩ := hT u
  let hAug : coordinateFibreBase S i u ⊆ coordinateFibreBase R i u := Set.union_subset_union hSR (Set.Subset.refl _)
  refine ⟨T.extendBase hAug,?_⟩
  intro p
  apply Subtype.ext
  exact (T.chain.extendBase_apply hAug p).trans
    (congrArg (fun z : coordinateFibre V i u => z.val) (hT p))

def extendHeadPreparation {n a : ℕ} {U : DefSet (M := M) S (n+1) a}
    (T : HeadPreparation U) (hSR : S ⊆ R) : HeadPreparation (extendBase U hSR) where
  arity := T.arity
  target := extendBase T.target hSR
  map := extendPointMap T.map hSR
  special := specialRelative_extendBase T.map hSR T.special
  saturated := T.saturated

def extendContractionProgram {n a l : ℕ} {U : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S U V) (hSR : S ⊆ R) :
    OrderedContractionProgram R (extendBase U hSR) (extendBase V hSR) := by
  induction T with
  | zero U => exact .zero (extendBase U hSR)
  | step T tail ih => exact .step (extendHeadPreparation T hSR) ih

theorem gamma_extendContractionProgram {n a l : ℕ} {U : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S U V) (hSR : S ⊆ R) (hT : GammaProgramDefinable B T) :
    GammaProgramDefinable B (extendContractionProgram T hSR) := by
  induction T with
  | zero U => exact hT
  | step T tail ih => exact ⟨hT.1,hT.2.1,ih hT.2.2⟩

def extendStandardContraction {n a : ℕ} {U : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}
    (C : StandardContraction U σ) (hSR : S ⊆ R) : StandardContraction (extendBase U hSR) σ where
  arity := C.arity
  target := extendBase C.target hSR
  program := extendContractionProgram C.program hSR

end IntegrationInACVF.Section6
