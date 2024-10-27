import IcLean.QuotBProperties
import Std.Data.HashMap
-- Antes de ler arquivos: dada uma string com um polinômio, transformar ele para o tipo
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

/-
  Vamos precisar de um array de Strings para facilitar a busca por index
  Por mais que estejamos usando uma tabela hash, o cálculo do hash
  para a string não vai ser usado, porque precisamos indexar as variáveis
-/

def hash_table : HashMap String Nat := HashMap.empty

#eval hash_table.size

def initHashTable (h : HashMap String Nat): List String → HashMap String Nat
| [] => h
| s :: ss =>
  let var := s.splitOn "^"
  let size := h.size
  initHashTable (h.insert var[0]! size) ss

def G : List String := ["h^8", "a", "b^4"]
def h : HashMap String Nat := initHashTable (HashMap.empty) G
def n : Nat := h.size

noncomputable def handle_exponents (n : Nat) : List String → MvPolynomial (Fin (n+1)) ℤ
| [] => C 1
| s::ss =>
  let vex := s.splitOn "^"
  let idx : Nat := (h[vex[0]!]!)
  if vex.length == 2 then
    if idx ≤ n then
      let exp : Nat := vex[1]!.toNat!
      let p1 : MvPolynomial (Fin (n+1)) ℤ := (X idx)
      (p1^exp) * (handle_exponents n ss)
    else
      (handle_exponents n ss)
  else
    let p1 : MvPolynomial (Fin (n+1)) ℤ := (X idx)
    (p1) * (handle_exponents n ss)

noncomputable def handle_monomials : List String → MvPolynomial (Fin n) ℤ
| [] => 0
| s::ss =>
  let vars := s.splitOn "*"
  -- Em Lean, não tem problema se vc declara um Fin n com n maior que a quantidade de variáveis de fato.
  -- O problema é ser menor e dar colisões...
  sorry


def split_terms : List String → List String
| [] => []
| s::ss =>
  s.splitOn "-" ++ split_terms ss

-- sem os símbolos de adição e subtração, temos uma lista de monômios.
-- resta saber como manipular as variáveis
noncomputable def str_to_poly (s : String) : MvPolynomial (Fin n) ℤ :=
  handle_monomials (split_terms (s.splitOn "+"))

noncomputable def reduce_poly (p : MvPolynomial (Fin n) ℤ)  : MvPolynomial (Fin n) ℤ ⧸ Ideal.span (B n) := Ideal.Quotient.mk (Ideal.span (B n)) p
