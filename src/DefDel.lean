

import Lean

syntax (name := selfRef) "∇" : term

private partial def replaceSelf (call : Lean.Syntax) : Lean.Syntax → Lean.Syntax
  | .node info kind args =>
      if kind == `selfRef then call
      else .node info kind (args.map (replaceSelf call))
  | stx => stx

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
      let mut call ← `(term| $name:ident)

      for binder in binders do
        match binder with
        | `(bracketedBinder| ($arg:ident : $argType:term)) =>
            let _ := argType
            call ← `(term| $call:term $arg:ident)
        | `(bracketedBinder| {$arg:ident : $argType:term}) =>
            let _ := arg
            let _ := argType
            pure ()
        | _ =>
            Lean.Macro.throwError
              "def∇ supports single-name explicit and implicit binders"

      let alts' : Lean.TSyntax ``Lean.Parser.Term.matchAlts :=
        ⟨replaceSelf call alts.raw⟩
      `(command| $mods:declModifiers def $name
          $binders:bracketedBinder* : $ty $alts':matchAlts)
def∇ listLength (α : Type) : List α → Nat
  | [] => 0
  | _ :: xs => 1 + ∇ xs

#eval listLength Nat [1, 2, 3]
