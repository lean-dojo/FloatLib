/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public meta import Lean.Meta.Instances
public import FloatLib

/-!
# Every capability reads the tagged candidates

A candidate tagged `@[compiler_optimize]` reaches a format only through a capability instance
whose arguments collect the tagged candidates of its reference operation: a
`Backend.Portfolio`, or the class `Backend.Collected` of the collection, by which
`Capability.ofStatic` chooses between a family's static kernel and the planner. A family with a
static form declares a `Capability.Static` and gets its capability from `ofStatic`. This check runs
at build time over every instance of `ExecFloat.Capability` that the public root of the library
declares, and fails on one that collects nothing: such an instance would fix its candidates
where it was written and ignore a candidate tagged later.

It also prints the registry of tagged compiled backends by role, so that the count of each kind
is part of the build log.
-/

public meta section

namespace FloatLibTests.Conformance.Execution.TaggedCapabilities

open Lean Meta Elab Command

/-- The capability instances of the environment whose type collects no tagged candidate. -/
def instancesWithoutPortfolio : MetaM (Array Name) := do
  let capability := ``FloatLib.Floats.ExecFloat.Capability
  let portfolio := ``FloatLib.Floats.ExecFloat.Backend.Portfolio
  let tagged := ``FloatLib.Floats.ExecFloat.Backend.Collected
  let mut missing := #[]
  for name in (instanceExtension.getState (← getEnv)).instanceNames.toList.map (·.1) do
    let type := (← getConstInfo name).type
    let isCapability ← forallTelescopeReducing type fun _ body => do
      let body ← whnfR body
      return body.getAppFn.isConstOf capability
    if isCapability &&
        !(type.find? fun sub => sub.isConstOf portfolio || sub.isConstOf tagged).isSome then
      missing := missing.push name
  return missing

/--
Fail unless every capability instance collects the tagged candidates, and report the tagged
compiled backends by role.
-/
elab "#check_tagged_capabilities" : command => do
  let missing ← liftTermElabM instancesWithoutPortfolio
  unless missing.isEmpty do
    throwError "capability instances that do not read the tagged candidates: {missing}"
  let backends ← liftCoreM FloatLib.Floats.ExecFloat.Backend.Tag.compilerBackends
  let count (role : FloatLib.Floats.ExecFloat.Backend.Tag.Role) :=
    (backends.filter fun backend => backend.role == role).size
  let rules ← liftCoreM FloatLib.Floats.ExecFloat.Backend.Tag.kernelRules
  logInfo m!"every capability instance collects the tagged candidates; tagged compiled \
    backends: \
    {count .alternative} alternatives, {count .direct} direct, {count .baseline} baselines, \
    {count .reference} shared references; \
    tagged kernel rules: {rules.size}"

#check_tagged_capabilities

end FloatLibTests.Conformance.Execution.TaggedCapabilities
