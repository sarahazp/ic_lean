import IcLean.QuotBProperties
import Std.Data.HashMap

open Equivalence
open MvPolynomial
open Std

-- Examplo de um hashmap no lean
def exampleHashMap : HashMap Nat String :=
  let emptyMap := HashMap.empty
  let map1 := emptyMap.insert 5 "apple"
  let map2 := map1.insert 10 "banana"
  let map3 := map2.insert 20 "cherry"
  map3

#eval exampleHashMap[5]?
#eval exampleHashMap[10]?
#eval (exampleHashMap[30]? == none)
#eval exampleHashMap.size
#eval exampleHashMap.insert 30 "orange"

def initHashTable (h : HashMap String Nat): List String → HashMap String Nat
| [] => h
| s :: ss =>
  let var := s.splitOn "^"
  let size := h.size
  initHashTable (h.insert var[0]! size) ss

def G : List String := ["h^8", "a", "b^4"]
def h : HashMap String Nat := initHashTable (HashMap.empty) G
def n : Nat := h.size

noncomputable def handle_exponents : List String → MvPolynomial (Fin (n+1)) ℤ
| [] => C 1
| s::ss =>
  let vex := s.splitOn "^"
  let idx : Nat := (h[vex[0]!]!)
  if vex.length == 2 && (h[vex[0]!]? ≠ none) then
    if idx ≤ n then -- sempre verdade
      let exp : Nat := vex[1]!.toNat!
      let p1 : MvPolynomial (Fin (n+1)) ℤ := (X idx)
      (p1^exp) * (handle_exponents ss)
    else
      C 0 -- sinal de q algo deu errado (coloquei só pra testar)
  else
    let p1 : MvPolynomial (Fin (n+1)) ℤ := (X idx)
    (p1) * (handle_exponents ss)

noncomputable def handle_monomials : List String → MvPolynomial (Fin (n+1)) ℤ
| [] => 0
| s::ss =>
  let vars := s.splitOn "*"
  (handle_exponents vars) + (handle_monomials ss)


def split_terms : List String → List String
| [] => []
| s::ss =>
  s.splitOn "-" ++ split_terms ss

-- sem os símbolos de adição e subtração, temos uma lista de monômios.
-- resta saber como manipular as variáveis
noncomputable def str_to_poly (s : String) : MvPolynomial (Fin (n+1)) ℤ :=
  handle_monomials (split_terms (s.splitOn "+"))

noncomputable def reduce_poly (p : MvPolynomial (Fin (n+1)) ℤ)  : MvPolynomial (Fin (n+1)) ℤ ⧸ Ideal.span (B (n+1)) := Ideal.Quotient.mk (Ideal.span (B (n+1))) p
