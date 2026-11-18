/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Lanes
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.KernelPath
public import FloatLib.Floats.Formats.OCP.FP8.E4M3
public import FloatLib.Floats.Formats.OCP.FP8.E5M2
public import FloatLib.Tactic.KernelTables

/-!
# Packed kernel tables of OCP FP8

The packed tables of nearest-even addition, subtraction and multiplication of E4M3 and E5M2 on
all 65,536 pairs of encodings, each one literal of 65,536 lanes of eight bits, and the tagged
rules that make `float_decide` look a sum, difference or product up in them
(`kernel_tables`). Each table is proved equal to the staged kernel operation, on all pairs, by
one run of that operation on all lanes.

Importing this module is what selects the tables: the rules have a lower declared cost than the
kernel operations.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath

kernel_tables E4M3 (size := 256) for E4M3.Family := StaticByte.Family.format E4M3.Family

kernel_tables E5M2 (size := 256) for E5M2.Family := StaticByte.Family.format E5M2.Family

end FloatLib.Floats
