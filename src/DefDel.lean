

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
        | `(bracketedBinder| [$instType:term]) =>
            let _ := instType
            pure ()
        | `(bracketedBinder| [$inst:ident : $instType:term]) =>
            let _ := inst
            let _ := instType
            pure ()
        | _ =>
            Lean.Macro.throwError
              "def∇ supports single-name explicit and implicit binders and instance binders"

      let alts' : Lean.TSyntax ``Lean.Parser.Term.matchAlts :=
        ⟨replaceSelf call alts.raw⟩
      `(command| $mods:declModifiers def $name
          $binders:bracketedBinder* : $ty $alts':matchAlts)


-- private partial def replaceSelf (call : Lean.Syntax) :
--     Lean.Syntax → Lean.Syntax
--   | .node info kind args =>
--       if kind == `selfRef then call
--       else .node info kind (args.map (replaceSelf call))
--   | stx => stx

namespace SelfRec
open Lean Parser

@[command_parser] def inductiveDel := leading_parser
  Command.declModifiers false >>
  "inductive∇" >> Command.declId >> ppIndent Command.optDeclSig >>
  optional (symbol " :=" <|> " where") >>
  many Command.ctor >>
  optional (ppDedent ppLine >> Command.computedFields) >>
  Command.optDeriving
end SelfRec

@[macro SelfRec.inductiveDel] def expandInductiveDel : Lean.Macro :=
  fun stx => do
    let declId := stx.getArg 2
    let name : Lean.TSyntax `ident := ⟨declId.getArg 0⟩
    let sig := stx.getArg 3
    let binders := (sig.getArg 0).getArgs

    let mut call ← `(term| $name:ident)
    for binder in binders do
      if binder.getKind == ``Lean.Parser.Term.explicitBinder then
        let ids := (binder.getArg 1).getArgs
        if ids.size != 1 then
          Lean.Macro.throwError
            "inductive∇ supports one name per explicit binder"
        let id : Lean.TSyntax `ident := ⟨ids[0]!⟩
        call ← `(term| $call:term $id:ident)
      else if binder.getKind != ``Lean.Parser.Term.implicitBinder then
        Lean.Macro.throwError "unsupported binder in inductive∇"

    let ctors := replaceSelf call (stx.getArg 5)
    let args := #[
      Lean.Syntax.atom .none "inductive",
      declId,
      sig,
      stx.getArg 4,
      ctors,
      stx.getArg 6,
      stx.getArg 7
    ]
    let ind := Lean.Syntax.node .none
      ``Lean.Parser.Command.inductive args
    return Lean.Syntax.node .none
      ``Lean.Parser.Command.declaration #[stx.getArg 0, ind]

inductive∇ CList (α : Type) where
| nil : ∇
| cons : α → ∇ → ∇
deriving Repr

def∇ listLength (α : Type) : CList α → Nat
| .nil => 0
| .cons _ xs => 1 + ∇ xs

#eval listLength Nat (.cons 1 (.cons 2 (.cons 3 .nil)))
