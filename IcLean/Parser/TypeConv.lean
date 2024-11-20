import IcLean.Theorems.QuotBProperties
import IcLean.Parser.TypeDefinitions
import Std.Data.HashMap

open MvPolynomial
open Std
open TypeDefinitions

def h : HashMap String Nat := HashMap.empty

noncomputable def conversion : List MyMonomial → MvPolynomial (Fin 100) ℤ
| [] => C 0
| p::ps => C 0 -- pensar mais nessa parte
