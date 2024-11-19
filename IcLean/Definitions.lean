import Mathlib
namespace Definitions
-- Esse arquivo contém as definições necessárias para
-- resolver o problema de uma forma computável
structure Elem where
  var : String
  exp : Nat

structure MyMonomial where
  coef : ℤ
  vars : List Elem

instance : Inhabited Elem where
  default := Elem.mk "" 0

-- Provide an Inhabited instance for MyMonomial
instance : Inhabited MyMonomial where
  default := MyMonomial.mk 0 []

-- Exemplo : 3a^2 -10a^3b^3
def a_poly : List MyMonomial := [MyMonomial.mk 3 [Elem.mk "a" 2], MyMonomial.mk (-10) [Elem.mk "a" 3, Elem.mk "b" 3]]

-- Definições úteis
def zero : List MyMonomial := [{coef := 0, vars := []}]
def const_one : MyMonomial := MyMonomial.mk 1 []

-- Ex.: B = {a^2 - a, b^2 - b, c^2 - c, ..., n^2 - n}
def B : List String → List (List MyMonomial)
| [] => []
| x::xs => [MyMonomial.mk 1 [Elem.mk x 2], MyMonomial.mk (-1) [Elem.mk x 1]]::(B xs)

-- Função auxiliar que encontra o maior expoente de um monômio
def greatest_ex (aux : Elem) : List Elem → Elem
| [] => aux
| p::ps =>
  if p.exp ≥ aux.exp then greatest_ex p ps
  else greatest_ex aux ps

-- Função que verifica se determinada entrada é um polinômio de grau zero
def zero_degree : List MyMonomial → Bool
| [] => true
| p::ps =>
    if p.vars.any (fun vp => vp.exp ≠ 0) then false
    else zero_degree ps

-- Função que verifica se duas listas de elementos são iguais (independe da ordem)
-- Pra melhorar a complexidade: ao invés de fazer isso, poderia ordenar os monômios com as variáveis por ordem alfabética ou algo do tipo?
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

-- Função que verifica se dois polinômios são iguais (independe da ordem)
-- também pode ser melhorada se os polinômios já estiverem ordenados
def Poly_eq (P Q : List MyMonomial): Bool :=
  Q.all (fun e1 =>
    match P.find? (fun e2 => e1.coef = e2.coef ∧ (vars_equality e1.vars e2.vars)) with
    | some _ => true
    | none => false
  ) ∧ P.all (fun e1 =>
    match Q.find? (fun e2 => e1.coef = e2.coef ∧ (vars_equality e1.vars e2.vars)) with
    | some _ => true
    | none => false)

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

-- Função auxiliar, que reduz cada monômio (mod <B>)
-- X^n = X(mod <B>) ∀ n ≥ 2
def reductionmon_mod_B (M : MyMonomial) : MyMonomial :=
  let reduced_vars := M.vars.map (fun ex =>
    if ex.exp ≥ 2 then
      -- Se o expoente for maior ou igual a 2, reduz para 1 (mod X^2 - X)
      { var := ex.var, exp := 1 }
    else
      -- Mantém o termo se o expoente for 1 ou 0
      ex
  )
  -- Retorna o monômio com coeficiente inalterado e variáveis reduzidas
  { coef := M.coef, vars := reduced_vars }

-- Reduz o polinômio (mod <B>)
def reductionpoly_mod_B : List MyMonomial → List MyMonomial
| [] => []
| p::ps =>
    let exp : Elem := greatest_ex (Elem.mk "0" 0) p.vars
    -- usa da adição para agrupar possíveis termos semelhantes:
    if exp.exp < 2 then addition [p] (reductionpoly_mod_B ps)
    else addition [reductionmon_mod_B p] (reductionpoly_mod_B ps)

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

-- Função auxiliar que pega a primeira variável do polinômio
def getVar : List Elem → String
| [] => "0"
| f::_=> f.var

-- Função que verifica se a regra de extensão foi devidamente aplicada
def check_extension : List MyMonomial →  Bool
| [] => true
| p::ps =>
  if (isVar (getVar p.vars) ps) then false
  else
    let p_red : List MyMonomial := reductionpoly_mod_B ps
    if Poly_eq p_red ps then true else false

-- Define função de negação
def f (z : String) : List MyMonomial := [MyMonomial.mk (-1) [Elem.mk z 1], const_one]

-- Estrutura auxiliar para as regras da prova
structure Rules where
  o : String -- operador  =, d, + ou *
  v : List MyMonomial -- polinômio 1
  w : List MyMonomial -- polinômio 2
  p : List MyMonomial -- resultado de se aplicar 'o' em 'v' e 'w'

-- Função de verificação de prova
-- Nesse caso, Array é melhor q list pq tem concatenação mais eficiente
def proof_ver : Array (List MyMonomial) → List Rules → List MyMonomial → String
| P, [], target =>
  if (Poly_eq target (P.get! (P.size - 1))) then "SUCCESSFULL"
  else "CORRECT-PROOF"
| P, r::rs, target =>
  match r.o with
  | "+" =>
    let index1 := (r.v.head!.coef.toNat) - 1
    let index2 := (r.w.head!.coef.toNat) - 1
    if (index1 < P.size) ∧ (index2 < P.size) then
      let poly1 := P.get! index1
      let poly2 := P.get! index2
      let p := reductionpoly_mod_B r.p
      if (Poly_eq (addition poly1 poly2) p) then
        proof_ver (P.push p) rs target
      else "INCORRECT-ADD"
    else "INVALID-INDEX-ADD"
  | "*" =>
    let index1 := (r.v.head!.coef.toNat) - 1
    if index1 < P.size then
      let poly1 := P.get! index1
      let poly2 := r.w
      let p := reductionpoly_mod_B r.p
      if Poly_eq (reductionpoly_mod_B (multiplication poly1 poly2)) p then
        proof_ver (P.push p) rs target
      else "INCORRECT-MUL"
    else "INVALID-INDEX-MUL"
  | "=" =>
    if Poly_eq r.v r.p then
      if check_extension r.p then
        let v : List MyMonomial := reductionpoly_mod_B (addition r.v (multiplication [MyMonomial.mk (-1) []] r.p))
        proof_ver (P.push v) rs target
      else
        "INCORRECT-EXT"
    else
      "INCORRECT-EQ"
  | "d" =>
    let index := (r.v.head!.coef.toNat) - 1
    if index < P.size then
      let P' := P.set! index [MyMonomial.mk 0 []]  -- Substitui pelo polinômio nulo
      proof_ver P' rs target
    else
      "INVALID-INDEX"
  | _ => "WRONG-INPUT"

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

end Definitions
