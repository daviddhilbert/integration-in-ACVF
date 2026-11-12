import IntegrationSection6.GammaIndexedFiniteObjects

/-! Set identities for restrictions of indexed domains. -/
namespace IntegrationInACVF.Section6
variable {Y : Type*} {p a : ℕ}

theorem indexedDomain_mono {T E : Set (Fin p → Y)} (hET : E ⊆ T)
    (D : (Fin p → Y) → Set (Fin a → Y)) : indexedDomain E D ⊆ indexedDomain T D :=
  fun _ h => ⟨hET h.1,h.2⟩

theorem indexedDomain_sdiff (T E : Set (Fin p → Y))
    (D : (Fin p → Y) → Set (Fin a → Y)) :
    indexedDomain T D \ indexedDomain E D = indexedDomain (T \ E) D := by
  apply Set.ext
  intro w
  change ((indexedLeft w ∈ T ∧ indexedRight w ∈ D (indexedLeft w)) ∧
    ¬ (indexedLeft w ∈ E ∧ indexedRight w ∈ D (indexedLeft w))) ↔ _
  change _ ↔ ((indexedLeft w ∈ T ∧ indexedLeft w ∉ E) ∧ indexedRight w ∈ D (indexedLeft w))
  tauto

end IntegrationInACVF.Section6
