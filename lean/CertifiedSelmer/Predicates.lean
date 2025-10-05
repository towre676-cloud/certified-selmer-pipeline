--! auto-generated verified predicates from receipts.json
namespace CertifiedSelmer

def regLoV : Float := 0.15246017794314362
def leadLoV : Float := 0.7593165002884267
def smithDiagV : List Nat := [1,1]

def regPositiveV : Prop := regLoV > 0
def leadPositiveV : Prop := leadLoV > 0
def smithIdentityV : Prop := smithDiagV = [1,1]

end CertifiedSelmer
