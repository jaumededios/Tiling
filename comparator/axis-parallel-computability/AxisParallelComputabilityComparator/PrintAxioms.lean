import AxisParallelComputabilityComparator.Solution

/-! Audit the exact independent computational statements and their executable witnesses. -/

run_cmd
  for name in #[``AxisParallelComputabilityComparator.oracleAlgorithm,
      ``Tiling.AxisParallel.Decidability.NumericalPrefix.decide,
      ``Tiling.AxisParallel.Decidability.AllInput.program,
      ``Tiling.AxisParallel.Decidability.OracleCoefficients.encodeQuery] do
    if Lean.isNoncomputable (← Lean.getEnv) name then
      throwError "Decision procedure {name} must be executable"

set_option linter.hashCommand false in
#print axioms AxisParallelComputabilityComparator.tiling_computable_relative
set_option linter.hashCommand false in
#print axioms AxisParallelComputabilityComparator.rational_tiling_computable
set_option linter.hashCommand false in
#print axioms AxisParallelComputabilityComparator.oracleAlgorithm
