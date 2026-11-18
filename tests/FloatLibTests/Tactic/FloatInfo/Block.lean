/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.FloatInfo.Block

/-!
# Shared-scale inspection reports

Raw and configured shared-scale tensors expose their finite integer storage and contextual
rounding theorems. The report states the supplied-exponent policy premise, including for an
empty tensor. Other coded formats retain the general report.
-/

open FloatLib.Floats

/--
family: contextual shared-scale block
-/
#guard_msgs (substring := true) in
#float_info Formats.Block.Tensor (Formats.Block.sharedScale (Fin 32))

/--
positions: Fin 0
-/
#guard_msgs (substring := true) in
#float_info Formats.Block.Tensor (Formats.Block.sharedScale (Fin 0))

/--
applicability: conditional: the scale-selection policy is sharedExponent
-/
#guard_msgs (substring := true) in
#float_info! ExecFloat.Block (Formats.Block.sharedScale (Fin 32))

/--
family: contextual shared-scale block
-/
#guard_msgs (substring := true) in
#float_info ExecFloat.Block (Formats.Block.sharedScale Bool)

def unscaled : Formats.Block.CodedFormat Unit Unit where
  element := Formats.Block.Codec.int
  levels := []

/--
family: block-scaled tensor
-/
#guard_msgs (substring := true) in
#float_info Formats.Block.Tensor unscaled
