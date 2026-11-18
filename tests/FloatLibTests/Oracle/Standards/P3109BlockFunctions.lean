module

import FloatLibTests.Oracle.Standards.P3109FunctionSupport
import FloatLib.Floats.Formats.P3109.Arithmetic.ScaledFunctions

/-!
P3109 chapter 5 function observations. Three-lane blocks exhaust every element
word of each selected small descriptor. Scale and right-operand formats differ
from the element format. Exact function expressions are reused across policies.

P3109 interim report v4.1, §§5.6–5.8, specifies these operation families.
-/

open FloatLib.Numerics FloatLib.Floats
open Formats.P3109 P3109FunctionSupport

abbrev Scale := ExecFloat.P3109 Format.binary8p3se

def scales : Array Scale :=
  #[ExecFloat.P3109.zero, ExecFloat.P3109.ofRat 1, ExecFloat.P3109.ofRat (-2),
    ExecFloat.P3109.positiveInfinity, ExecFloat.P3109.negativeInfinity, ExecFloat.P3109.nan]

def resultScales : Array Scale := scales.push (ExecFloat.P3109.ofRat (1 / 2))

def publicBlockFunctions {source : Format} :
    Array ((target : Format) → Block Scale (ExecFloat.P3109 source) 3 →
      Scale → Block Scale (ExecFloat.P3109 target) 3) :=
  #[fun f x s => Block.BlockLog f {} x s,
    fun f x s => Block.BlockLog2 f {} x s,
    fun f x s => Block.BlockLogOnePlus f {} x s,
    fun f x s => Block.BlockExp f {} x s,
    fun f x s => Block.BlockExp2 f {} x s,
    fun f x s => Block.BlockExpMinusOne f {} x s,
    fun f x s => Block.BlockSin f {} x s,
    fun f x s => Block.BlockCos f {} x s,
    fun f x s => Block.BlockTan f {} x s,
    fun f x s => Block.BlockArcSin f {} x s,
    fun f x s => Block.BlockArcCos f {} x s,
    fun f x s => Block.BlockArcTan f {} x s,
    fun f x s => Block.BlockSinh f {} x s,
    fun f x s => Block.BlockCosh f {} x s,
    fun f x s => Block.BlockTanh f {} x s,
    fun f x s => Block.BlockArcSinh f {} x s,
    fun f x s => Block.BlockArcCosh f {} x s,
    fun f x s => Block.BlockArcTanh f {} x s,
    fun f x s => Block.BlockSinPi f {} x s,
    fun f x s => Block.BlockCosPi f {} x s,
    fun f x s => Block.BlockTanPi f {} x s,
    fun f x s => Block.BlockArcSinPi f {} x s,
    fun f x s => Block.BlockArcCosPi f {} x s,
    fun f x s => Block.BlockArcTanPi f {} x s,
    fun f x s => Block.BlockSoftplus f {} x s]

def publicScaledFunctions {source : Format} :
    Array ((target : Format) → Scale → ExecFloat.P3109 source → ExecFloat.P3109 target) :=
  #[fun f s x => Arithmetic.Mixed.ScaledLog f s x,
    fun f s x => Arithmetic.Mixed.ScaledLog2 f s x,
    fun f s x => Arithmetic.Mixed.ScaledLogOnePlus f s x,
    fun f s x => Arithmetic.Mixed.ScaledExp f s x,
    fun f s x => Arithmetic.Mixed.ScaledExp2 f s x,
    fun f s x => Arithmetic.Mixed.ScaledExpMinusOne f s x,
    fun f s x => Arithmetic.Mixed.ScaledSin f s x,
    fun f s x => Arithmetic.Mixed.ScaledCos f s x,
    fun f s x => Arithmetic.Mixed.ScaledTan f s x,
    fun f s x => Arithmetic.Mixed.ScaledArcSin f s x,
    fun f s x => Arithmetic.Mixed.ScaledArcCos f s x,
    fun f s x => Arithmetic.Mixed.ScaledArcTan f s x,
    fun f s x => Arithmetic.Mixed.ScaledSinh f s x,
    fun f s x => Arithmetic.Mixed.ScaledCosh f s x,
    fun f s x => Arithmetic.Mixed.ScaledTanh f s x,
    fun f s x => Arithmetic.Mixed.ScaledArcSinh f s x,
    fun f s x => Arithmetic.Mixed.ScaledArcCosh f s x,
    fun f s x => Arithmetic.Mixed.ScaledArcTanh f s x,
    fun f s x => Arithmetic.Mixed.ScaledSinPi f s x,
    fun f s x => Arithmetic.Mixed.ScaledCosPi f s x,
    fun f s x => Arithmetic.Mixed.ScaledTanPi f s x,
    fun f s x => Arithmetic.Mixed.ScaledArcSinPi f s x,
    fun f s x => Arithmetic.Mixed.ScaledArcCosPi f s x,
    fun f s x => Arithmetic.Mixed.ScaledArcTanPi f s x,
    fun f s x => Arithmetic.Mixed.ScaledSoftplus f s x]

def sourceFormat (profile : Nat) : Format :=
  match profile with
  | 0 => Format.signed 3 2 .finite
  | 1 => Format.signed 3 2 .extended
  | 2 => Format.unsigned 3 2 .extended
  | 3 => Format.signed 3 1 .extended
  | _ => Format.unsigned 3 3 .finite

/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main (arguments : List String) : IO Unit := do
  let source := sourceFormat (arguments[0]?.bind String.toNat? |>.getD 0)
  let stdout ← IO.getStdout
  for target in [source, Format.binary8p3se] do
    stdout.putStrLn s!"F,{descriptor source},{descriptor target}"
    for scale in scales do
      for word in [:source.modulus] do
        let values : Vector (ExecFloat.P3109 source) 3 := Vector.ofFn fun lane =>
          ExecFloat.P3109.ofNatBits (word + lane.val)
        let block : Block Scale (ExecFloat.P3109 source) 3 := ⟨scale, values⟩
        let exact := Block.decode block
        for (operation, (name, (blockCall, scaledCall))) in
            operations.zip (names.zip ((publicBlockFunctions (source := source)).zip
              (publicScaledFunctions (source := source)))) do
          let expressions := exact.map (Functions.unary operation)
          for resultScale in resultScales do
            let output := blockCall target block resultScale
            for lane in [:3] do
              if h : lane < 3 then
                let expression := FunctionBlock.normalize (Arithmetic.Mixed.decode resultScale)
                  expressions[lane]
                observe stdout target
                  s!"U,{name},{scale.toNatBits},{resultScale.toNatBits},{values[lane].toNatBits}"
                  expression output.values[lane].toNatBits
          for lane in [:3] do
            if h : lane < 3 then
              let output := scaledCall target scale values[lane]
              observe stdout target s!"S,{name},{scale.toNatBits},0,{values[lane].toNatBits}"
                (FunctionBlock.normalize (.finite 1) expressions[lane]) output.toNatBits
        for xWord in [0, 1, 64, 127, 128, 192, 255] do
          let rightValues : Vector Scale 3 := Vector.ofFn fun lane =>
            ExecFloat.P3109.ofNatBits (xWord + lane.val)
          let right : Block Rat Scale 3 := ⟨-2, rightValues⟩
          let rightExact := Block.decode right
          for piScaled in [false, true] do
            let name := if piScaled then "ArcTan2Pi" else "ArcTan2"
            let expressions := Vector.ofFn fun lane : Fin 3 =>
              Functions.arcTan2 piScaled exact[lane.val] rightExact[lane.val]
            for resultScale in resultScales do
              let output := if piScaled then Block.BlockArcTan2Pi target {} block right resultScale
                else Block.BlockArcTan2 target {} block right resultScale
              for lane in [:3] do
                if h : lane < 3 then
                  let expression := FunctionBlock.normalize (Arithmetic.Mixed.decode resultScale)
                    expressions[lane]
                  observe stdout target
                    s!"B,{name},{scale.toNatBits},{resultScale.toNatBits},{values[lane].toNatBits},\
                        {rightValues[lane].toNatBits}"
                    expression output.values[lane].toNatBits
            for lane in [:3] do
              if h : lane < 3 then
                let output := if piScaled then Arithmetic.Mixed.ScaledArcTan2Pi target
                    scale values[lane] (-2 : Rat) rightValues[lane]
                  else Arithmetic.Mixed.ScaledArcTan2 target
                    scale values[lane] (-2 : Rat) rightValues[lane]
                observe stdout target
                  s!"T,{name},{scale.toNatBits},0,{values[lane].toNatBits},\
                      {rightValues[lane].toNatBits}"
                  (FunctionBlock.normalize (.finite 1) expressions[lane]) output.toNatBits
