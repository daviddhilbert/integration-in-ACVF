import Integration7.ZeroAuxVolumeWitnesses
import IntegrationSection6.GammaSchemaRowAgreement

/-! Remove or add an empty exception-parameter block without changing
any raw domain, coordinate relation or bound. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k b : ℕ} {sp sq : Fin p → SortTag}

theorem appendEmptySort_eq (sp : Fin p → SortTag) (s0 : Fin 0 → SortTag) : Fin.append sp s0 = sp :=
  funext (Fin.append_left sp s0)

def finiteSchemaChangeParameterSort (h : sp = sq) (F : GammaFiniteRVSchema B p a d sp) :
    GammaFiniteRVSchema B p a d sq where
  domain := F.domain
  volume := F.volume
  domain_definable := h ▸ F.domain_definable
  volume_definable := h ▸ F.volume_definable
  bound := F.bound

def finiteSchemaWithEmptyParameters (F : GammaFiniteRVSchema B p a d sp) :
    GammaFiniteRVSchema B (p+0) a d (Fin.append sp (Fin.elim0 : Fin 0 → SortTag)) :=
  finiteSchemaChangeParameterSort (appendEmptySort_eq sp Fin.elim0).symm F

def GammaRVVolumeIsoCertificateSchema.zeroAuxiliaryException
    (H : GammaRVVolumeIsoCertificateSchema B p a b k sp) (h : H.extraArity = 0) :
    GammaFiniteRVSchema B p ((k+1)+1) H.exceptionDegree sp := by
  rcases H with ⟨F,G,H,hH,A,q,sq,j,hj,E⟩
  dsimp at h
  subst q
  exact finiteSchemaChangeParameterSort (appendEmptySort_eq sp sq) E

theorem GammaRVVolumeIsoCertificateSchema.zeroAuxiliaryException_rows
    (H : GammaRVVolumeIsoCertificateSchema B p a b k sp) (h : H.extraArity = 0)
    (z : Fin p → M) (y : Fin H.extraArity → M) :
    GammaSchemaRowAgreement (H.zeroAuxiliaryException h) z H.exception (Fin.append z y) := by
  rcases H with ⟨F,G,H,hH,A,q,sq,j,hj,E⟩
  dsimp at h
  subst q
  have he : Fin.append z y = z := funext (Fin.append_left z y)
  constructor
  · intro x
    change (Fin.append z x ∈ E.domain) ↔ Fin.append (Fin.append z y) x ∈ E.domain
    rw [he]
  · intro x ω
    change (Fin.append (Fin.append z x) ω ∈ E.volume) ↔
      Fin.append (Fin.append (Fin.append z y) x) ω ∈ E.volume
    rw [he]

theorem dropExtraVolumeParameters_zero (p d : ℕ) : dropExtraVolumeParameters p 0 d = id := by
  funext i
  refine Fin.addCases (m := p) (n := d) (fun i => ?_) (fun i => ?_) i <;>
    simp only [dropExtraVolumeParameters,Fin.addCases_left,Fin.addCases_right]
  · rfl
  · rfl

end IntegrationInACVF.Section7
