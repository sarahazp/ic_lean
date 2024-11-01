import IcLean.QuotBProperties
import Std.Data.HashMap
-- Objetivo: Dada uma string, transformá-la em um polinômio
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

def G : List String := ["hsa^8", "asa", "bsa^4"]
def h : HashMap String Nat := initHashTable (HashMap.empty) G
#eval h["lls"]?
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


-- Define função de negação
noncomputable def f (z : String) : MvPolynomial (Fin (n+1)) ℤ :=
  if h[z]? = none then
    C 0
  else
    let idx : Nat := (h[z]!)
    if idx < n then
      let x : MvPolynomial (Fin (n+1)) ℤ := X idx
      C 1 - x
    else
      C 0


def split_terms : List String → List String
| [] => []
| s::ss =>
  s.splitOn "-" ++ split_terms ss

-- sem os símbolos de adição e subtração, temos uma lista de monômios.
-- resta saber como manipular as variáveis
noncomputable def str_to_poly (s : String) : MvPolynomial (Fin (n+1)) ℤ :=
  handle_monomials (split_terms (s.splitOn "+"))

noncomputable def reduce_poly (p : MvPolynomial (Fin (n+1)) ℤ)  : MvPolynomial (Fin (n+1)) ℤ ⧸ Ideal.span (B (n+1)) := Ideal.Quotient.mk (Ideal.span (B (n+1))) p

def isDigit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'

-- Função auxiliar para pegar o prefixo numérico de uma string
def takeWhileDigit (s : String) : String :=
  s.toList.takeWhile isDigit |>.asString

-- Função para processar o coeficiente numérico no início da string (se houver)
noncomputable def parseCoef (input : String) : (MvPolynomial (Fin (n+1)) ℤ  × String) :=
  let input := input.trim
  let (coefStr, restStr) :=
    -- Identifica onde termina o coeficiente e começam as variáveis
    if input.startsWith "-" then
      let numEnd := takeWhileDigit (input.drop 1)
      if numEnd.isEmpty then ("-1", input.drop 1)
      else ("-" ++ numEnd, input.drop (numEnd.length + 1))
    else if input.startsWith "+" then
      let numEnd := takeWhileDigit (input.drop 1)
      if numEnd.isEmpty then ("1", input.drop 1)
      else (numEnd, input.drop (numEnd.length + 1))
    else
      let numEnd := takeWhileDigit input
      if numEnd.isEmpty then ("1", input)
      else (numEnd, input.drop numEnd.length)

  (C coefStr.toInt!, restStr.trim)

noncomputable def parseExp : List String → MvPolynomial (Fin (n+1)) ℤ
| [] => 1
| v::vs =>
  let parts := v.splitOn "^"
  let varName := (parts.head!).trim
  let exp := if parts.length > 1 then parts[1]!.toNat! else 1
  let idx := varName.toList.findIdx? (fun c => c == 'f')  -- Achar o índice de 'f'
  match idx with
  | some i =>
    let aux := varName.drop (i + 1)
    let fz := f aux
    let rest := parseExp vs
    fz * rest
  | none   =>
    let idx : Nat := (h[varName]!)
    if idx < n then
      let monomial : MvPolynomial (Fin (n+1)) ℤ := (X idx)
      monomial^exp * (parseExp vs)
    else
      C 0
    -- Caso não encontre 'f', continua com a variável normal

-- Função principal para converter uma string como "-8*a*b" em um monômio
noncomputable def parseMonomial (input : String) : MvPolynomial (Fin (n+1)) ℤ :=
  let (coef, varsStr) := parseCoef (input).trim
  -- Limpar qualquer "*" inicial no varsStr
  let varsStr := if varsStr.startsWith "*" then varsStr.drop 1 else varsStr
  let varsList := varsStr.splitOn "*" |>.filter (fun v => v.trim ≠ "")
  -- Criar a lista de variáveis, assumindo expoente 1 para cada uma
  let vars : MvPolynomial (Fin (n+1)) ℤ  := parseExp varsList
  coef * vars

noncomputable def callParseMon : List String → MvPolynomial (Fin (n+1)) ℤ
| [] => C 0
| m::ms =>
  (parseMonomial m) + (callParseMon ms)

noncomputable def parsePolynomial (s : String) : MvPolynomial (Fin (n+1)) ℤ :=
  let rec aux (acc : String) (lst : List String) (remaining : List Char) : List String :=
    match remaining with
    | [] => if acc.isEmpty then lst else lst ++ [acc]  -- Adiciona o último termo, se houver
    | (c::cs) =>
      if c == '+' || c == '-' then
        if acc.isEmpty then aux (acc.push c) lst cs
        else aux (String.singleton c) (lst ++ [acc]) cs
      else aux (acc.push c) lst cs
  callParseMon (aux "" [] s.toList)
