import IntegrationSection6.FiniteSelectedContractionSlices
import IntegrationSection6.GammaPreparedSelectedSliceIsomorphisms

/-! Point values of the selected-slice lift charts. Membership transports
leave every underlying point unchanged; the contraction and prepared maps
therefore keep their explicit VF and old-label coordinate formulas. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m u w : ℕ}

theorem gammaIso_congr_value
    {A A' : Set (Point (M := M) n m)} {D D' : Set (Point (M := M) u w)}
    (e : GammaIso B A D) (hA : A = A') (hD : D = D') (a : A') :
    ((e.congr hA hD).equiv a).val =
      (e.equiv ⟨a.val,by rw [hA]; exact a.property⟩).val := by
  cases hA
  cases hD
  rfl

theorem gammaIsoNamedRVLabels_value {k : ℕ}
    {A : Set (Point (M := M) n m)} {D : Set (Point (M := M) u w)}
    (f : GammaIso B A D) (ρ : Fin k → Fin m) (τ : Fin k → Fin w)
    (hLabels : ∀ a : A, (f.equiv a).val.2 ∘ τ = a.val.2 ∘ ρ)
    (t : Fin k → RV (M := M)) (a : {p : Point (M := M) n m // p ∈ A ∧ p.2 ∘ ρ = t}) :
    ((gammaIsoNamedRVLabels f ρ τ hLabels t).equiv a).val =
      (f.equiv ⟨a.val,a.property.1⟩).val := rfl

theorem gammaIso_reflexive_value
    (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable B A) (a : A) :
    ((gammaIso_reflexive A hA).equiv a).val = a.val := by
  unfold gammaIso_reflexive
  rw [gammaIso_congr_value]
  rfl

theorem gammaSelectedSliceLiftIso_value {k : ℕ}
    (U : GammaRVObject B n) (ρ : Fin k → Fin (rvObjectArity U.object))
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin (rvObjectArity U.object) → RV (M := M) | (x,r) ∈ U.lift ∧ r ∘ ρ = t}.Finite)
    (t : Fin k → RV (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (rvValues t),B.gamma⟩
      (rvObjectArity U.object) n
      ((gammaVolumeSliceSchema (gammaPrependSelectedVolume U ρ hfin)).rowDomain (rvValues t))
      ((gammaVolumeSliceSchema (gammaPrependSelectedVolume U ρ hfin)).rowVolume (rvValues t)))
    (a : {p : Point (M := M) n (rvObjectArity U.object) // p ∈ U.lift ∧ p.2 ∘ ρ = t}) :
    ((gammaSelectedSliceLiftIso U ρ hfin t P).equiv a).val = a.val := by
  unfold gammaSelectedSliceLiftIso
  rw [gammaIso_congr_value]
  exact gammaIso_reflexive_value _ _ _

theorem gammaSelectedContractionSliceLiftIso_value {κ : Cardinal} {a k : ℕ}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n a} (hBS : B.real ⊆ S)
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin n)} (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
    (t : Fin k → RV (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (rvValues t),B.gamma⟩
      (n+T.arity) n
      ((gammaVolumeSliceSchema (FiniteRV.gammaPrependSelectedContraction hκ hs hreal hBS hA ρ hfin T hT)).rowDomain (rvValues t))
      ((gammaVolumeSliceSchema (FiniteRV.gammaPrependSelectedContraction hκ hs hreal hBS hA ρ hfin T hT)).rowVolume (rvValues t)))
    (a : {p : Point (M := M) n a // p ∈ carrier A ∧ p.2 ∘ ρ = t}) :
    ((FiniteRV.gammaSelectedContractionSliceLiftIso hκ hs hreal hBS hA ρ hfin T hT t P).equiv a).val =
      (T.normalizedNaturalLiftMap ⟨a.val,a.property.1⟩).val := by
  unfold FiniteRV.gammaSelectedContractionSliceLiftIso
  let W := T.gammaNormalizedObject hBS (gamma_program_final_set T.program hT)
  let τ := fun j => FiniteRV.contractionOldLabelIndex T (ρ j)
  change ((gammaSelectedSliceLiftIso W τ
    (FiniteRV.contraction_selected_lift_finite hκ hs hreal hBS hA ρ hfin T hT) t P).equiv _).val = _
  rw [gammaSelectedSliceLiftIso_value,gammaIsoNamedRVLabels_value]
  rfl

theorem gammaPreparedSelectedSliceLiftIso_value {p l a k : ℕ}
    {A : Set (Point (M := M) p 0)} (C : DefSet (M := M) S p l)
    (e : GammaIso B A (carrier C)) (hA : GammaSetDefinable B A) (hC : IsRVPullback (carrier C))
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B (p+l) a k (fun _ => .rv))
    (ρ : Fin k → Fin a)
    (hRows : ∀ c : C, GammaSchemaRowAgreement F (rawVFParameter (e.equiv.symm c).val) G (rawPreparedKey c.val))
    (BP : PreparedIndexPresentation B C)
    (hG : ∀ s ∈ preparedKeyDomain C, G.finiteRow (rvValues s))
    (hLabels : ∀ s ∈ preparedKeyDomain C, ∀ r y, G.rowVolume (rvValues s) r y ↔
      r ∈ G.rowDomain (rvValues s) ∧ r ∘ ρ = y)
    (P : G.IndexedPresentation BP) (t : Fin k → RV (M := M))
    (L : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (rvValues t),B.gamma⟩ ((p+l)+a) p
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks P.toGamma)).rowDomain (rvValues t))
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks P.toGamma)).rowVolume (rvValues t)))
    (u : {q : Point (M := M) p a // q ∈ vfSchemaSource A F ∧ q.2 ∘ ρ = t}) :
    ((gammaPreparedSelectedSliceLiftIso C e hA hC F G ρ hRows BP hG hLabels P t L).equiv u).val =
      ((gammaPreparedFamilyIso e hA F).equiv ⟨u.val,u.property.1⟩).val := by
  unfold gammaPreparedSelectedSliceLiftIso
  rw [gammaIso_congr_value]
  unfold gammaPreparedFamilyNamedLabels
  exact gammaIsoNamedRVLabels_value _ _ _ _ _ _

end IntegrationInACVF.Section7
