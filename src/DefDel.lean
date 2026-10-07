
import Lean

macro "∇" : term => do
  return Lean.mkIdent `«∇»

namespace SelfRec
open Lean Parser

@[command_parser] def defDel := leading_parser
  Command.declModifiers false >>
  "def∇" >> Command.declId >>
  ppIndent (many (ppSpace >> Term.bracketedBinder) >> Term.typeSpec) >>
  Term.matchAlts
end SelfRec

macro_rules
  | `(command| $mods:declModifiers def∇ $name:ident
      $binders:bracketedBinder* : $ty:term $alts:matchAlts) => do
      let del := Lean.mkIdent `«∇»
      `(command| $mods:declModifiers def $name
          $binders:bracketedBinder* : $ty := $del:ident
        where
          $del:ident : $ty
            $alts:matchAlts)

def∇ listLength (α : Type) : List α → Nat
  | [] => 0
  | _ :: xs => 1 + ∇ xs

#eval listLength Nat [1, 2, 3]
