/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Block.Functions.Runtime
public meta import FloatLib.Tactic.P3109BlockFunctions

/-!
# Standard names for P3109 block elementary functions

The complete elementary-function list of P3109 interim report v4.1 §5.7 (unapproved draft)
is instantiated from the unary and two-argument schemas. Input decoders,
result scale, block length and destination precision remain independent.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.Block

open FloatLib.Numerics FloatLib.Floats.ExecFloat


block_function BlockLog := Functions.Unary.log
block_function BlockLog2 := Functions.Unary.log2
block_function BlockLogOnePlus := Functions.Unary.logOnePlus
block_function BlockExp := Functions.Unary.exp
block_function BlockExp2 := Functions.Unary.exp2
block_function BlockExpMinusOne := Functions.Unary.expMinusOne
block_function BlockSin := Functions.Unary.sin
block_function BlockCos := Functions.Unary.cos
block_function BlockTan := Functions.Unary.tan
block_function BlockArcSin := Functions.Unary.arcSin
block_function BlockArcCos := Functions.Unary.arcCos
block_function BlockArcTan := Functions.Unary.arcTan
block_function BlockSinh := Functions.Unary.sinh
block_function BlockCosh := Functions.Unary.cosh
block_function BlockTanh := Functions.Unary.tanh
block_function BlockArcSinh := Functions.Unary.arcSinh
block_function BlockArcCosh := Functions.Unary.arcCosh
block_function BlockArcTanh := Functions.Unary.arcTanh
block_function BlockSinPi := Functions.Unary.sinPi
block_function BlockCosPi := Functions.Unary.cosPi
block_function BlockTanPi := Functions.Unary.tanPi
block_function BlockArcSinPi := Functions.Unary.arcSinPi
block_function BlockArcCosPi := Functions.Unary.arcCosPi
block_function BlockArcTanPi := Functions.Unary.arcTanPi
block_function BlockSoftplus := Functions.Unary.softplus


block_angle BlockArcTan2 := false
block_angle BlockArcTan2Pi := true

end FloatLib.Floats.Formats.P3109.Block
