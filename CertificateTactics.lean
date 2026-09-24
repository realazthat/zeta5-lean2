import CertificateData
import AppendixNumericConstants
import RealEnergy
import TrigCertificates
import AppendixCellBase

/-!
# Checked numerical certificate assembly

`potential_certificate` takes a point and sixteen component upper bounds, in
Table 1 order. `field_certificate` takes a point and four bounds: an arctangent
lower bound, an arctangent upper bound, a logarithm lower bound, and a logarithm
upper bound. `cell_certificate` combines two endpoint bounds and a field bound.

The tactics generate ordinary proof terms from the existing analytic lemmas.
Every numerical certificate is discharged by `decide +kernel`; there is no
compiler-trust fallback. See `NUMERICAL_CERTIFICATES.md` for the formulas.
-/

namespace Zeta5CertificateSyntax
open Lean

/-- Combine the two endpoint potential certificates and the cell's field bound. -/
macro "cell_certificate " left:term:max right:term:max field:term:max : tactic =>
  `(tactic|
    (norm_num [Zeta5AppendixNumerics.cellBound, Zeta5AppendixNumerics.lowerField]
     have endpointBounds := max_le_max $left $right
     norm_num at endpointBounds
     have potentialBound := max_le endpointBounds.1 endpointBounds.2
     have fieldBound := $field
     linarith only [potentialBound, fieldBound]))


private partial def rationalValue (s : TSyntax `term) : MacroM _root_.Rat := do
  match s with
  | `(($t:term)) => rationalValue t
  | `(-$t:term) => return -(← rationalValue t)
  | `($a:term / $b:term) =>
    let denominator ← rationalValue b
    if denominator == 0 then Macro.throwErrorAt b "zero certificate denominator"
    return (← rationalValue a) / denominator
  | `($n:num) => return n.getNat
  | _ => Macro.throwErrorAt s "expected an exact rational literal"

private def realSyntax (q : _root_.Rat) : MacroM (TSyntax `term) := do
  let numerator := Syntax.mkNumLit (toString q.num.natAbs)
  let denominator := Syntax.mkNumLit (toString q.den)
  if q.num < 0 then
    `((- $numerator:num / $denominator:num : ℝ))
  else
    `(($numerator:num / $denominator:num : ℝ))

private def componentProof (index : Nat) (point bound : _root_.Rat) :
    MacroM (TSyntax `term) := do
  let some row := Zeta5RealEnergy.arcsineData[index]?
    | Macro.throwError "component index outside the source table"
  let a := row.1
  let b := row.2.1
  let aR ← realSyntax a
  let bR ← realSyntax b
  let tR ← realSyntax point
  let boundR ← realSyntax bound
  if a ≤ point && point ≤ b then
    let support := mkIdent (.str (.str .anonymous "Zeta5AppendixNumerics")
      s!"support_log_upper_{index}")
    `(show Zeta5AppendixNumerics.componentPotential $aR $bR $tR ≤ $boundR from by
        have supportBound := $support
        convert supportBound using 1 <;>
          norm_num [Zeta5AppendixNumerics.componentPotential])
  else
    let difference := point - (a+b)/2
    let shift := if difference < 0 then -difference else difference
    let discriminant := (point-a)*(point-b)
    let scale := 10^20
    let root : _root_.Rat :=
      (Nat.sqrt (discriminant.num.toNat * scale^2 / discriminant.den)+1) / scale
    let logInput := (shift+root)/2
    let shiftR ← realSyntax shift
    let discriminantR ← realSyntax discriminant
    let rootR ← realSyntax root
    let inputQ ← rationalSyntax logInput
    let boundQ ← rationalSyntax bound
    let roots ← logRoots logInput.num.toNat logInput.den 34
    `(show Zeta5AppendixNumerics.componentPotential $aR $bR $tR ≤ $boundR from by
        have heq : Zeta5AppendixNumerics.componentPotential $aR $bR $tR =
            Real.log (($shiftR + Real.sqrt $discriminantR)/2) := by
          norm_num [Zeta5AppendixNumerics.componentPotential]
        rw [heq]
        apply Zeta5AppendixNumerics.log_sqrt_upper (u := $rootR)
        · norm_num
        · norm_num
        · norm_num
        · convert Zeta5LogCertificates.log_le_of_check $inputQ $boundQ $roots
            (by decide +kernel) using 1 <;> norm_num)

/-- Assemble the sixteen source-table components from explicit rational bounds.
Square-root witnesses and logarithm chains are generated exactly; every
inequality and the final weighted sum are checked by ordinary Lean proofs. -/
macro "potential_certificate " point:term:max " [" bounds:term,* "]" : tactic => do
  let pointValue ← rationalValue point
  let bounds := bounds.getElems
  if bounds.size != Zeta5RealEnergy.arcsineData.length then
    Macro.throwError "expected one bound for each of the sixteen components"
  let mut steps : Array (TSyntax `tactic) := #[]
  let mut total : Option (TSyntax `term) := none
  for index in [:bounds.size] do
    let bound ← rationalValue bounds[index]!
    let proof ← componentProof index pointValue bound
    let hypothesis := mkIdent (.str .anonymous s!"componentBound{index}")
    steps := steps.push (← `(tactic| have $hypothesis := $proof))
    let some row := Zeta5RealEnergy.arcsineData[index]?
      | Macro.throwError "component index outside the source table"
    let mass ← realSyntax row.2.2
    let weighted ← `(mul_le_mul_of_nonneg_left $hypothesis (by norm_num : (0 : ℝ) ≤ $mass))
    match total with
      | none => total := some weighted
      | some previous => total := some (← `(add_le_add $previous $weighted))
  let some result := total | Macro.throwError "empty component table"
  `(tactic|
    ($[$steps:tactic]*
     have weightedTotal := $result
     norm_num only [Zeta5AppendixNumerics.potential] at weightedTotal ⊢
     exact weightedTotal))

/-- Assemble a field lower bound from two arctangent and two logarithm bounds.
All auxiliary square roots and trigonometric tables are exact rational data. -/
macro "field_certificate " point:term:max " [" lowerAngle:term "," upperAngle:term
    "," lowerLog:term "," upperLog:term "]" : tactic => do
  let t ← rationalValue point
  if t ≤ 0 then Macro.throwErrorAt point "the field certificate requires a positive point"
  let a ← rationalValue lowerAngle
  let b ← rationalValue upperAngle
  let l ← rationalValue lowerLog
  let u ← rationalValue upperLog
  let scale := 10^20
  let rootFloor := Nat.sqrt (t.num.toNat * scale^2 / t.den)
  let rootLower : _root_.Rat := rootFloor / scale
  let rootUpper : _root_.Rat := (rootFloor+1) / scale
  let tR ← realSyntax t
  let aR ← realSyntax a
  let bR ← realSyntax b
  let lR ← realSyntax l
  let uR ← realSyntax u
  let rootLowerR ← realSyntax rootLower
  let rootUpperR ← realSyntax rootUpper
  let reciprocalUpper ← realSyntax (1/rootUpper)
  let scaledReciprocalLower ← realSyntax ((3/40)/rootLower)
  let aSmall := a / 2^28
  let bSmall := b / 2^28
  let aQ ← rationalSyntax aSmall
  let bQ ← rationalSyntax bSmall
  let aInitial ← boxSyntax (initialBox aSmall)
  let bInitial ← boxSyntax (initialBox bSmall)
  let aChain ← trigListSyntax aSmall
  let bChain ← trigListSyntax bSmall
  let firstLog := 1+t
  let secondLog := t+(3/40)^2
  let firstLogR ← realSyntax firstLog
  let secondLogR ← realSyntax secondLog
  let firstLogQ ← rationalSyntax firstLog
  let secondLogQ ← rationalSyntax secondLog
  let lQ ← rationalSyntax l
  let uQ ← rationalSyntax u
  let firstRoots ← logRoots firstLog.den firstLog.num.toNat 34
  let secondRoots ← logRoots secondLog.num.toNat secondLog.den 34
  let bracket := (314159265358979323846/10^20 : _root_.Rat)+a-6*b
  let bracketR ← realSyntax bracket
  let productBound := mkIdent (.str .anonymous "rootProductBound")
  let sqrtProduct ← if bracket ≤ 0 then
      `(tactic|
        (have hs : Real.sqrt $tR ≤ $rootUpperR :=
           Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
         have $productBound := mul_le_mul_of_nonpos_right hs
           (by norm_num : $bracketR ≤ (0 : ℝ))))
    else
      `(tactic|
        (have hs : $rootLowerR ≤ Real.sqrt $tR := Real.le_sqrt_of_sq_le (by norm_num)
         have $productBound := mul_le_mul_of_nonneg_right hs
           (by norm_num : (0 : ℝ) ≤ $bracketR)))
  `(tactic|
    (have hA : $aR ≤ Real.arctan ((1 : ℝ) / Real.sqrt $tR) := by
       apply Zeta5AppendixNumerics.arctan_div_sqrt_lower (u := $rootUpperR)
       · norm_num
       · norm_num
       · norm_num
       · norm_num
       · apply Zeta5AppendixNumerics.arctan_lower
         · linarith [Real.pi_gt_d20]
         · linarith [Real.pi_gt_d20]
         · norm_num only
           have ht := Zeta5TrigCertificates.bounds_of_check $aQ $aInitial $aChain
             (by decide +kernel)
           norm_num [Zeta5TrigCertificates.Bounds, Zeta5TrigCertificates.endpoint] at ht
           have hm := mul_le_mul_of_nonneg_left ht.2.2.1
             (by norm_num : (0 : ℝ) ≤ $reciprocalUpper)
           apply le_trans ht.2.1
           apply le_trans _ hm
           norm_num
     have hB : Real.arctan ((3/40 : ℝ) / Real.sqrt $tR) ≤ $bR := by
       apply Zeta5AppendixNumerics.arctan_div_sqrt_upper (u := $rootLowerR)
       · norm_num
       · norm_num
       · norm_num
       · apply Zeta5AppendixNumerics.arctan_upper
         · linarith [Real.pi_gt_d20]
         · linarith [Real.pi_gt_d20]
         · norm_num only
           have ht := Zeta5TrigCertificates.bounds_of_check $bQ $bInitial $bChain
             (by decide +kernel)
           norm_num [Zeta5TrigCertificates.Bounds, Zeta5TrigCertificates.endpoint] at ht
           have hm := mul_le_mul_of_nonneg_left ht.2.2.2
             (by norm_num : (0 : ℝ) ≤ $scaledReciprocalLower)
           apply hm.trans
           apply le_trans _ ht.1
           norm_num
     have hL : $lR ≤ Real.log $firstLogR := by
       convert Zeta5LogCertificates.le_log_of_check $firstLogQ $lQ $firstRoots
         (by decide +kernel) using 1 <;> norm_num
     have hU : Real.log $secondLogR ≤ $uR := by
       convert Zeta5LogCertificates.log_le_of_check $secondLogQ $uQ $secondRoots
         (by decide +kernel) using 1 <;> norm_num
     have hD : $bracketR ≤ Real.pi + Real.arctan (1/Real.sqrt $tR) -
         6*Real.arctan ((3/40 : ℝ)/Real.sqrt $tR) := by
       linarith [Real.pi_gt_d20]
     $sqrtProduct:tactic
     have hm2 := mul_le_mul_of_nonneg_left hD
       (show 0 ≤ Real.sqrt $tR from Real.sqrt_nonneg _)
     unfold Zeta5AppendixNumerics.field
     norm_num only at hL hU ⊢
     nlinarith only [hL, hU, $productBound, hm2]))

end Zeta5CertificateSyntax
