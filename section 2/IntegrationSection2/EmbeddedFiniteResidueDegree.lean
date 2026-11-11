import IntegrationSection2.EmbeddedIntermediateHenselian
import IntegrationSection2.EmbeddedResidueCharacteristic
import IntegrationSection2.FiniteImmediateEmbedded
import IntegrationSection2.PrimitiveResidueDegree
import IntegrationSection2.ResidueGeneratedSurjectivity
import IntegrationSection2.ImmediateApproximationFromResidues

/-! The finite-extension degree equality needed by the Gauss graph
construction, for extensions actually embedded in the algebraically
closed valued ambient field. Henselianity, a primitive residue lift,
the immediate residual extension and its trace triviality are all
supplied by the checked preceding proofs. No finite-extension
reference or desired degree equality is a premise. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Classical IsLocalRing IntermediateField Module
open SpecialTransformations.Section9

namespace IntegrationInACVF.Section2.EmbeddedFiniteResidueDegree

variable {D K Γ : Type} [Field D] [Field K] [IsAlgClosed K] [CharZero K]
  [LinearOrderedCommGroupWithZero Γ]

theorem residue_degree (v : Valuation K Γ) (f : D →+* K) (F : Subfield D)
    [FiniteDimensional F D]
    [HenselianLocalRing ((v.comap f).comap F.subtype).valuationSubring]
    [CharZero (ResidueField v.valuationSubring)]
    (hSame : ∀ x : D, ∃ c : F, (v.comap f) (c:D) = (v.comap f) x) :
    letI := (residueFieldInclusion (v.comap f) F).toAlgebra
    Module.finrank F D =
      Module.finrank (ResidueField ((v.comap f).comap F.subtype).valuationSubring)
        (ResidueField (v.comap f).valuationSubring) := by
  classical
  let w := v.comap f
  letI : HenselianLocalRing w.valuationSubring :=
    EmbeddedAlgebraicHenselian.henselian v f F (fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic)
  letI : CharZero (ResidueField w.valuationSubring) := EmbeddedResidueCharacteristic.charZero v f
  letI := (residueFieldInclusion w F).toAlgebra
  obtain ⟨pb,u,P,hPm,hred,hres,hroot⟩ := PrimitiveResidueLift.exists_lift w F
  let A := (w.comap F.subtype).valuationSubring
  have hint : IsIntegral F (u:D) :=
    ⟨P.map A.subtype,hPm.map A.subtype,PrimitiveResidueDegree.field_root w F P u hroot⟩
  let M := F⟮(u:D)⟯
  letI : FiniteDimensional F M := adjoin.finiteDimensional hint
  letI : FiniteDimensional M D := FiniteDimensional.right F M D
  letI : FiniteDimensional M.toSubfield D :=
    FieldDegreeTransport.finite_left (F := M.toSubfield) (E := M)
      (RingEquiv.refl M) (RingEquiv.refl D) (fun _ _ => rfl)
  have hFM : F ≤ M.toSubfield := by
    intro x hx
    exact M.algebraMap_mem ⟨x,hx⟩
  have huM : (u:D) ∈ M.toSubfield := mem_adjoin_simple_self F (u:D)
  have hSurj : Function.Surjective (residueFieldInclusion w M.toSubfield) :=
    ResidueGeneratedSurjectivity.surjective w F M.toSubfield hFM u huM pb hres
  have hSameM (x : D) : ∃ c : M, w (c:D) = w x := by
    obtain ⟨c,hc⟩ := hSame x
    exact ⟨algebraMap F M c,hc⟩
  letI : HenselianLocalRing (w.comap M.toSubfield.subtype).valuationSubring :=
    EmbeddedIntermediateHenselian.henselian v f F M
  have hApprox (x : D) (hx : x ≠ 0) : ∃ c : M, v (f x-f (c:D)) < v (f x) := by
    obtain ⟨c,hc⟩ := ImmediateApproximationFromResidues.approximate w M.toSubfield hSameM hSurj x hx
    refine ⟨c,?_⟩
    change v (f (x-(c:D))) < v (f x) at hc
    simpa only [map_sub] using hc
  have hDegree := FiniteImmediateEmbedded.finrank_eq_one v f M.toSubfield hApprox
  have hDegreeM : Module.finrank M D = 1 := by
    have ht := FieldDegreeTransport.finrank (F := M) (E := M.toSubfield)
      (RingEquiv.refl M) (RingEquiv.refl D) (fun _ _ => rfl)
    exact ht.trans hDegree
  calc
    Module.finrank F D = Module.finrank F M * Module.finrank M D :=
      (Module.finrank_mul_finrank F M D).symm
    _ = Module.finrank F M := by rw [hDegreeM,mul_one]
    _ = _ := PrimitiveResidueDegree.generated_degree w F u P hPm hroot pb hres hred

end IntegrationInACVF.Section2.EmbeddedFiniteResidueDegree
