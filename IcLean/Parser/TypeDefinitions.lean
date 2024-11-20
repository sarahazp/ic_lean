import Mathlib
namespace TypeDefinitions
-- Esse arquivo contém as definições necessárias para parsear os polinômios de uma forma computável
structure Elem where
  var : String
  exp : Nat

structure MyMonomial where
  coef : ℤ
  vars : List Elem

instance : Inhabited Elem where
  default := Elem.mk "" 0

instance : Inhabited MyMonomial where
  default := MyMonomial.mk 0 []

-- Definições úteis
def zero : List MyMonomial := [{coef := 0, vars := []}]
def const_one : MyMonomial := MyMonomial.mk 1 []

-- Função que verifica se duas listas de elementos são iguais (independe da ordem)
def vars_equality (P Q : List Elem): Bool :=
  -- Verifica se todos os elementos de Q têm correspondentes em P
  Q.all (fun e1 =>
    match P.find? (fun e2 => e1.var = e2.var ∧ e1.exp = e2.exp) with
    | some _ => true
    | none => false
  ) ∧
  -- Verifica se todos os elementos de P têm correspondentes em Q
  P.all (fun e1 =>
    match Q.find? (fun e2 => e1.var = e2.var ∧ e1.exp = e2.exp) with
    | some _ => true
    | none => false
  )

-- Função que ajuda a atualizar os coeficientes dos termos semelhantes da adição
def update_monomial (p : MyMonomial) : List MyMonomial → List MyMonomial
| [] => []
| q::qs =>
  if vars_equality p.vars q.vars then
    if p.coef + q.coef ≠ 0 then
      { coef := p.coef + q.coef, vars := q.vars } :: qs
    else qs
  else
    q::(update_monomial p qs)

-- Define a adição de polinômios:
def addition : List MyMonomial → List MyMonomial → List MyMonomial
| [], Q => Q
| p::ps, Q =>
    if Q.any (fun q => vars_equality q.vars p.vars) then
      addition ps (update_monomial p Q)
    else addition ps (p::Q)

-- Multiplicação de dois monômios
def monomial_multiply (m1 m2 : MyMonomial) : MyMonomial :=
  let new_coef := m1.coef * m2.coef
  let combined_vars :=
    m1.vars.map (fun e1 =>
      match m2.vars.find? (fun e2 => e1.var = e2.var) with
      | some e2 => { var := e1.var, exp := e1.exp + e2.exp }
      | none => e1
    ) ++ m2.vars.filter (fun e2 => m1.vars.all (fun e1 => e1.var ≠ e2.var)) -- adiciona as variáveis de m2 que não estão em m1
  { coef := new_coef, vars := combined_vars }

-- Multiplicação de um monômio por um polinômio
def mul_monomial_by_polynomial (m : MyMonomial) : List MyMonomial → List MyMonomial
| [] => []
 -- garante que um mesmo polinômio não vai ter mesmas variáveis e expoentes em mais de uma posição da lista:
| q::qs => addition [monomial_multiply m q] (mul_monomial_by_polynomial m qs)

-- Função de multiplicação de dois polinômios
def multiplication : List MyMonomial → List MyMonomial → List MyMonomial
| [], _ => []
| p::ps, Q =>
  let product_p := mul_monomial_by_polynomial p Q
  let rest_product := multiplication ps Q
  -- usa a função de adição para combinar os resultados
  addition product_p rest_product

-- Função que verifica se uma variável pertence ao conjunto de variáveis do polinômio
def isVar (v:String) (G: List MyMonomial) : Bool :=
  if  G.any (fun G' =>
    if G'.vars.any (fun g => g.var = v) then true
    else false) then true else false

-- Define função de negação
def f (z : String) : List MyMonomial := [MyMonomial.mk (-1) [Elem.mk z 1], const_one]

-- Estrutura auxiliar para as regras da prova
structure Rules where
  o : String -- operador  =, d, + ou *
  v : List MyMonomial -- polinômio 1
  w : List MyMonomial -- polinômio 2
  p : List MyMonomial -- resultado de se aplicar 'o' em 'v' e 'w'

-- ESSA PARTE É MAIS FOCADA EM PARSEAR OS POLINOMIOS DE ENTRADA:
-- Função para verificar se um caractere é um dígito
def isDigit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'

-- Função auxiliar para pegar o prefixo numérico de uma string
def takeWhileDigit (s : String) : String :=
  s.toList.takeWhile isDigit |>.asString

-- Função para processar o coeficiente numérico no início da string (se houver)
def parseCoef (input : String) : (MyMonomial × String) :=
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

  (MyMonomial.mk coefStr.toInt! [], restStr.trim)

def parseExp : List String → List MyMonomial
| [] => [const_one]
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
    multiplication fz rest
  | none   =>
    -- Caso não encontre 'f', continua com a variável normal
    let monomial := MyMonomial.mk 1 [Elem.mk varName exp]
    multiplication [monomial] (parseExp vs)

-- Função principal para converter uma string como "-8*a*b" em um monômio
def parseMonomial (input : String) : List MyMonomial :=
  let (coef, varsStr) := parseCoef (input).trim
  -- Limpar qualquer "*" inicial no varsStr
  let varsStr := if varsStr.startsWith "*" then varsStr.drop 1 else varsStr
  let varsList := varsStr.splitOn "*" |>.filter (fun v => v.trim ≠ "")
  -- Criar a lista de variáveis, assumindo expoente 1 para cada uma
  let vars : List MyMonomial := parseExp varsList
  multiplication [coef] vars

def callParseMon : List String → List MyMonomial
| [] => []
| m::ms =>
  addition (parseMonomial m) (callParseMon ms)

def parsePolynomial (s : String) : List MyMonomial :=
  let rec aux (acc : String) (lst : List String) (remaining : List Char) : List String :=
    match remaining with
    | [] => if acc.isEmpty then lst else lst ++ [acc]  -- Adiciona o último termo, se houver
    | (c::cs) =>
      if c == '+' || c == '-' then
        if acc.isEmpty then aux (acc.push c) lst cs
        else aux (String.singleton c) (lst ++ [acc]) cs
      else aux (acc.push c) lst cs
  callParseMon (aux "" [] s.toList)

def str_to_rule (line : String) : Rules :=
  let num := takeWhileDigit (line).trim
  let l := (line.drop num.length).trim
  if l.startsWith "d" then
    Rules.mk "d" [MyMonomial.mk num.toInt! []] [] []
  else if l.startsWith "=" then
    if l.contains ',' ∧ l.contains ';' then
      let aux := (l.drop 1).trim
      let polys := aux.splitOn ","
      let lastP := polys[1]!.trim.splitOn ";"
      Rules.mk "=" (parsePolynomial polys[0]!.trim) [] (parsePolynomial lastP[0]!.trim)
    else Rules.mk "error" [] [] []
  else if l.startsWith "+" then
    if l.contains ',' ∧ l.contains ';' then
      let aux := (l.drop 1).trim
      let polys := aux.splitOn ","
      let lastP := polys[2]!.trim.splitOn ";"
      Rules.mk "+" (parsePolynomial polys[0]!.trim) (parsePolynomial polys[1]!.trim) (parsePolynomial lastP[0]!.trim)
    else Rules.mk "error" [] [] []
  else if l.startsWith "*" then
    if l.contains ',' ∧ l.contains ';' then
      let aux := (l.drop 1).trim
      let polys := aux.splitOn ","
      let lastP := polys[2]!.trim.splitOn ";"
      Rules.mk "*" (parsePolynomial polys[0]!.trim) (parsePolynomial polys[1]!.trim) (parsePolynomial lastP[0]!.trim)
    else Rules.mk "error" [] [] []
  else
    Rules.mk "error" [] [] []

def rule_maker : List String → List Rules
| [] => []
| s::ss => str_to_rule s :: rule_maker ss

#reduce parsePolynomial "a+b"
end TypeDefinitions
