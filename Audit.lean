import OpenProblemFormalizations
import Lean

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let required : Array Name := #[
    `OpenProblemFormalizations.IdealSpectra.CohesiveIdeal.no_omega_omegaOne_ideal_representative,
    `OpenProblemFormalizations.IdealSpectra.CohesiveIdeal.noncofinalIdeal_union,
    `OpenProblemFormalizations.IdealSpectra.CohesiveIdeal.omegaOne_cofinal_fiber,
    `OpenProblemFormalizations.IdealSpectra.EnhancedTukeyOmega.cofinal_subsequence_unbounded,
    `OpenProblemFormalizations.IdealWebs.seqWeb_subset_level,
    `OpenProblemFormalizations.IdealWebs.seqWeb_image_of_pullback,
    `OpenProblemFormalizations.IdealWebs.seqSun_diff_finite]
  for name in required do
    unless env.contains name do
      throwError "Required declaration missing: {name}"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut declarations := 0
  let mut theorems := 0
  let mut used : Array Name := #[]
  for (name, info) in env.constants.toList do
    if (name.toString.splitOn ".").contains "OpenProblemFormalizations" then
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless permitted.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
        unless used.contains ax do used := used.push ax
  unless theorems > 0 do throwError "No project theorem declarations were audited"
  logInfo m!"Kernel audit passed: {declarations} declarations, {theorems} theorem constants; axioms: {used}"
