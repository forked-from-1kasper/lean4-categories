import Lean.Parser
open Lean.Parser.Term

syntax "Π" many1(binderIdent <|> bracketedBinder) ", " term : term
macro_rules | `(Π $xs*, $y) => `(∀ $xs*, $y)

macro "λ " xs:many1(funBinder) ", " f:term : term => `(fun $xs* => $f)

macro mods:declModifiers "lemma" n:declId sig:declSig val:declVal : command =>
  `($mods:declModifiers theorem $n $sig $val)

macro "begin " ts:sepBy1(tactic, ";", "; ", allowTrailingSep) i:"end" : term =>
  `(by { $[($ts:tactic)]* }%$i)