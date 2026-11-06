namespace CertifiedSelmer

/-- Exact rational endpoints. This predicate says nothing about enclosure. -/
structure RationalInterval where
  loNum : Int
  loDen : Nat
  hiNum : Int
  hiDen : Nat

def RationalInterval.WellFormed (i : RationalInterval) : Prop :=
  0 < i.loDen ∧ 0 < i.hiDen ∧ 0 < i.loNum ∧
    i.loNum * (i.hiDen : Int) < i.hiNum * (i.loDen : Int)

instance (i : RationalInterval) : Decidable i.WellFormed :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Enclosure requires a value and a proved link to the endpoints. -/
def Encloses {V : Type} (le : V → V → Prop) (lo value hi : V) : Prop :=
  le lo value ∧ le value hi

/-- Generic exact-sequence consequence, with arithmetic instantiation still required. -/
theorem quotient_trivial_of_exact_and_surjective
    {M S T : Type} (kummer : M → S) (quotient : S → T) (zero : T)
    (exactAt : ∀ s, quotient s = zero ↔ ∃ m, kummer m = s)
    (kummerSurjective : ∀ s, ∃ m, kummer m = s)
    (quotientSurjective : ∀ t, ∃ s, quotient s = t) :
    ∀ t, t = zero := by
  intro t
  obtain ⟨s, hs⟩ := quotientSurjective t
  have hz := (exactAt s).2 (kummerSurjective s)
  exact hs.symm.trans hz

end CertifiedSelmer
