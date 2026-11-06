-- Generated receipt syntax facts. No enclosure or Selmer theorem.
import CertifiedSelmer.Predicates
namespace CertifiedSelmer.Receipt389
def reg : RationalInterval :=
  ⟨7623008897157181, 50000000000000000, 1905752224289297, 12500000000000000⟩
theorem reg_wellFormed : reg.WellFormed := by decide
def lead : RationalInterval :=
  ⟨7593165002884267, 10000000000000000, 1898291250721067, 2500000000000000⟩
theorem lead_wellFormed : lead.WellFormed := by decide
def assertedAnalyticRank : Nat := 2
def assertedSmithDiagonal : List Nat := [1, 1]
theorem assertedSmith_identity : assertedSmithDiagonal = [1, 1] := rfl
end CertifiedSelmer.Receipt389
