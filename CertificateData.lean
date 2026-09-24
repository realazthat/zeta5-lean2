import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Defs
import Lean

/-!
# Exact rational certificate data

These functions construct syntax containing rational literals. They do not prove
inequalities: the Boolean checkers in `LogCertificates` and `TrigCertificates`
and ordinary Lean kernel checking validate the generated data.

Logarithm chains use 80 fractional binary digits and upward square-root rounding.
Trigonometric boxes use 128 fractional binary digits and outward rounding.
-/

namespace Zeta5CertificateSyntax
open Lean

/-- Emit a normalized exact rational literal. -/
def rationalSyntax (q : _root_.Rat) : MacroM (TSyntax `term) := do
  let numerator := Syntax.mkNumLit (toString q.num.natAbs)
  let denominator := Syntax.mkNumLit (toString q.den)
  if q.num < 0 then
    `((- $numerator:num / $denominator:num : ℚ))
  else
    `(($numerator:num / $denominator:num : ℚ))

/-- Generate dyadic upper square roots; positivity is checked by the consumer. -/
def logRoots (numerator denominator steps : Nat) : MacroM (TSyntax `term) := do
  if denominator == 0 then Macro.throwError "certificate denominator must be positive"
  let scale := 2^80
  let mut q : _root_.Rat := numerator / denominator
  let mut roots : Array (TSyntax `term) := #[]
  for _ in [:steps] do
    let n := Nat.sqrt (q.num.toNat * scale^2 / q.den) + 1
    q := n / scale
    roots := roots.push (← rationalSyntax q)
  `([$roots,*])

/-- Expand a chain of dyadic upper square roots with 80 fractional bits. -/
macro "log_roots%(" numerator:num "/" denominator:num "," steps:num ")" : term =>
  logRoots numerator.getNat denominator.getNat steps.getNat

/-- Round toward negative infinity on the 128-bit dyadic grid. -/
def roundDown (q : _root_.Rat) : _root_.Rat :=
  ((q.num * (2^128 : Int)) / q.den : Int) / (2^128 : _root_.Rat)

/-- Round toward positive infinity on the same grid. -/
def roundUp (q : _root_.Rat) : _root_.Rat := -roundDown (-q)

/-- Rational lower and upper bounds for sine and cosine. -/
structure RationalBox where
  sinLower : _root_.Rat
  sinUpper : _root_.Rat
  cosLower : _root_.Rat
  cosUpper : _root_.Rat

/-- Initial small-angle bounds, using the checker's polynomial inequalities. -/
def initialBox (q : _root_.Rat) : RationalBox :=
  ⟨roundDown (q-q^3/6), roundUp q,
   roundDown (1-q^2/2), roundUp (1-2*(q/2-(q/2)^3/6)^2)⟩

/-- One outward-rounded double-angle step. -/
def doubleBox (b : RationalBox) : RationalBox :=
  ⟨roundDown (2*b.sinLower*b.cosLower), roundUp (2*b.sinUpper*b.cosUpper),
   roundDown (b.cosLower^2-b.sinUpper^2), roundUp (b.cosUpper^2-b.sinLower^2)⟩

/-- Emit a literal box for the trigonometric checker. -/
def boxSyntax (b : RationalBox) : MacroM (TSyntax `term) := do
  let sl ← rationalSyntax b.sinLower
  let sh ← rationalSyntax b.sinUpper
  let cl ← rationalSyntax b.cosLower
  let ch ← rationalSyntax b.cosUpper
  `(⟨$sl, $sh, $cl, $ch⟩)


/-- Emit the 28 double-angle steps used by the field certificates. -/
def trigListSyntax (q : _root_.Rat) : MacroM (TSyntax `term) := do
  let mut box := initialBox q
  let mut boxes : Array (TSyntax `term) := #[]
  for _ in [:28] do
    box := doubleBox box
    boxes := boxes.push (← boxSyntax box)
  `([$boxes,*])

end Zeta5CertificateSyntax
