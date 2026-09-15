/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibBenchmarks.Public.Sweep

open FloatLib.Floats
open FloatLib.Floats.ExecFloat.Backend
open FloatLib.Numerics

open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput

namespace FloatLibBenchmarks.Public.SelectionMatrix

public def printHeader : IO Unit :=
  IO.println <|
    "family,format,storageBits,maximumSignificandBits,operation,candidateCount,selected," ++
      "kernelClass,residentBytes,policy,expectedCalls,maxResidentBytes,warmCost,coldCost,score"

private def printCandidate
    (family formatName : String) (storageBits precision : Nat)
    (operation : Operation) (policy : Policy) (candidates : CandidateSet Candidate)
    (selected : Candidate) : IO Unit :=
  IO.println <|
      s!"{family},{formatName},{storageBits},{precision},{operationLabel operation}," ++
      s!"{candidates.alternatives.length + 1},{selected.name}," ++
      s!"{selected.kind.display},{selected.residentBytes}," ++
      s!"{policy.profileName},{policy.expectedCalls},{policy.maxResidentBytes}," ++
      s!"{selected.warmCost policy},{selected.coldCost policy},{selected.score policy}"
where
  operationLabel : Operation → String
    | .add => "add"
    | .sub => "sub"
    | .mul => "mul"
    | .div => "div"
    | .sqrt => "sqrt"
    | .fma => "fma"

private def printAdd (family formatName : String) (storageBits precision : Nat)
    (F : Type) [PolicyFor F] [EncodedFormat F] [ExecFloat.Add F] : IO Unit :=
  let policy := ExecFloat.Add.policy (F := F)
  let candidates := (ExecFloat.Add.candidates (F := F)).estimates
  printCandidate family formatName storageBits precision .add policy candidates
    (ExecFloat.Add.selectedCandidate (F := F))

public def printAddOnly (family formatName : String) (storageBits precision : Nat)
    (F : Type) [PolicyFor F] [EncodedFormat F] [ExecFloat.Add F] : IO Unit :=
  printAdd family formatName storageBits precision F

private def printSub (family formatName : String) (storageBits precision : Nat)
    (F : Type) [PolicyFor F] [EncodedFormat F] [ExecFloat.Sub F] : IO Unit :=
  let policy := ExecFloat.Sub.policy (F := F)
  let candidates := (ExecFloat.Sub.candidates (F := F)).estimates
  printCandidate family formatName storageBits precision .sub policy candidates
    (ExecFloat.Sub.selectedCandidate (F := F))

private def printMul (family formatName : String) (storageBits precision : Nat)
    (F : Type) [PolicyFor F] [EncodedFormat F] [ExecFloat.Mul F] : IO Unit :=
  let policy := ExecFloat.Mul.policy (F := F)
  let candidates := (ExecFloat.Mul.candidates (F := F)).estimates
  printCandidate family formatName storageBits precision .mul policy candidates
    (ExecFloat.Mul.selectedCandidate (F := F))

private def printDiv (family formatName : String) (storageBits precision : Nat)
    (F : Type) [PolicyFor F] [EncodedFormat F] [ExecFloat.Div F] : IO Unit :=
  let policy := ExecFloat.Div.policy (F := F)
  let candidates := (ExecFloat.Div.candidates (F := F)).estimates
  printCandidate family formatName storageBits precision .div policy candidates
    (ExecFloat.Div.selectedCandidate (F := F))

private def printSqrt (family formatName : String) (storageBits precision : Nat)
    (F : Type) [PolicyFor F] [EncodedFormat F] [ExecFloat.Sqrt F] : IO Unit :=
  let policy := ExecFloat.Sqrt.policy (F := F)
  let candidates := (ExecFloat.Sqrt.candidates (F := F)).estimates
  printCandidate family formatName storageBits precision .sqrt policy candidates
    (ExecFloat.Sqrt.selectedCandidate (F := F))

private def printFma (family formatName : String) (storageBits precision : Nat)
    (F : Type) [PolicyFor F] [EncodedFormat F] [ExecFloat.Fma F] : IO Unit :=
  let policy := ExecFloat.Fma.policy (F := F)
  let candidates := (ExecFloat.Fma.candidates (F := F)).estimates
  printCandidate family formatName storageBits precision .fma policy candidates
    (ExecFloat.Fma.selectedCandidate (F := F))

public def printFormat (family formatName : String) (storageBits precision : Nat)
    (F : Type) [PolicyFor F] [EncodedFormat F]
    [ExecFloat.Add F] [ExecFloat.Sub F]
    [ExecFloat.Mul F] [ExecFloat.Div F] [ExecFloat.Sqrt F] [ExecFloat.Fma F] :
    IO Unit := do
  printAdd family formatName storageBits precision F
  printSub family formatName storageBits precision F
  printMul family formatName storageBits precision F
  printDiv family formatName storageBits precision F
  printSqrt family formatName storageBits precision F
  printFma family formatName storageBits precision F

end FloatLibBenchmarks.Public.SelectionMatrix
