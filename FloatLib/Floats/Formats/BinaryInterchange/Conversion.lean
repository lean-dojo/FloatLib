/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Runtime

/-!
# Conversion policies for binary-interchange models

Binary-interchange conversion uses a representation-independent runtime policy with a proof
contract. Carrier adapters are split into the `Runtime`, `Proof`, and `Instances` modules below
`Configured.Conversion` and `StaticByte.Conversion`.
-/
