import Integration7.GammaVolumeIsoRecoding

/-! Finite volume blowup data recode over a new sorted parameter block.
All exact chain lengths and the absence of extra parameters are retained. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b k r : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def GammaVolumeParameterRecode.blowup (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaRVVolumeBlowupSchema F G) (h : H.NoAuxiliary) :
    GammaRVVolumeBlowupSchema (C.volumeObject F) (C.volumeObject G) where
  centerArity := H.centerArity
  remainderArity := H.remainderArity
  center := C.volumeObject H.center
  remainder := C.volumeObject H.remainder
  admissibilityBound := H.admissibilityBound
  sourceChart := C.certificate H.sourceChart h.1
  resultChart := C.certificate H.resultChart h.2

def GammaVolumeParameterRecode.chain (C : GammaVolumeParameterRecode B p q sp sq) :
    {a b : ℕ} → {F : GammaRVVolumeSchema B p a k sp} → {G : GammaRVVolumeSchema B p b k sp} →
      {r : ℕ} → (H : GammaVolumeChainSchema F G r) → H.NoAuxiliary →
        GammaVolumeChainSchema (C.volumeObject F) (C.volumeObject G) r
  | _,_,_,_,_,.iso chart,h => .iso (C.certificate chart h)
  | _,_,_,_,_,.step W head tail,h =>
      .step (C.volumeObject W) (C.blowup head h.1) (C.chain tail h.2)

def GammaVolumeParameterRecode.common (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaVolumeCommonSchema F G) (h : H.NoAuxiliary) :
    GammaVolumeCommonSchema (C.volumeObject F) (C.volumeObject G) where
  leftArity := H.leftArity
  rightArity := H.rightArity
  leftObject := C.volumeObject H.leftObject
  rightObject := C.volumeObject H.rightObject
  leftLength := H.leftLength
  rightLength := H.rightLength
  leftChain := C.chain H.leftChain h.1
  rightChain := C.chain H.rightChain h.2.1
  comparison := C.certificate H.comparison h.2.2

theorem GammaVolumeParameterRecode.blowup_noAuxiliary (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaRVVolumeBlowupSchema F G) (h : H.NoAuxiliary) : (C.blowup H h).NoAuxiliary := ⟨rfl,rfl⟩

theorem GammaVolumeParameterRecode.chain_noAuxiliary (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaVolumeChainSchema F G r) : ∀ h : H.NoAuxiliary, (C.chain H h).NoAuxiliary := by
  induction H with
  | iso chart => exact fun _ => rfl
  | step W head tail ih => exact fun h => ⟨C.blowup_noAuxiliary head h.1,ih h.2⟩

theorem GammaVolumeParameterRecode.common_noAuxiliary (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaVolumeCommonSchema F G) (h : H.NoAuxiliary) : (C.common H h).NoAuxiliary :=
  ⟨C.chain_noAuxiliary H.leftChain h.1,C.chain_noAuxiliary H.rightChain h.2.1,rfl⟩

end IntegrationInACVF.Section7
