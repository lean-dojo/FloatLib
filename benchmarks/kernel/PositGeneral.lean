/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

import FloatLib.Floats.Formats.Posit.KernelPath.Flat
import FloatLib.Tactic.KernelCost

/-!
Posit operations with exponent sizes other than two, in Lean's kernel.

The operations of `Posit.KernelPath.Core` take the number of exponent bits as a parameter and
compute on natural-number literals, so the kernel evaluates them as they are written. Each row is
one operation on fixed encodings of a format `(payload bits, exponent bits)`: 8 bits with no
exponent bit, 16 bits with one, 32 bits with three, and 32 bits with two for comparison.
-/

open FloatLib.Floats.Formats.Posit.KernelPath

#print "POSIT_GENERAL add p=7 es=0"
#kernel_cost add 7 0 0x35 0x6b
#print "POSIT_GENERAL mul p=7 es=0"
#kernel_cost mul 7 0 0x35 0x6b
#print "POSIT_GENERAL div p=7 es=0"
#kernel_cost div 7 0 0x35 0x6b
#print "POSIT_GENERAL sqrt p=7 es=0"
#kernel_cost sqrt 7 0 0x35
#print "POSIT_GENERAL fma p=7 es=0"
#kernel_cost fma 7 0 0x35 0x6b 0x55

#print "POSIT_GENERAL add p=15 es=1"
#kernel_cost add 15 1 0x3555 0x6aaa
#print "POSIT_GENERAL mul p=15 es=1"
#kernel_cost mul 15 1 0x3555 0x6aaa
#print "POSIT_GENERAL div p=15 es=1"
#kernel_cost div 15 1 0x3555 0x6aaa
#print "POSIT_GENERAL sqrt p=15 es=1"
#kernel_cost sqrt 15 1 0x3555
#print "POSIT_GENERAL fma p=15 es=1"
#kernel_cost fma 15 1 0x3555 0x6aaa 0x5555
#print "POSIT_GENERAL cast p=15 es=1 to p=31 es=2"
#kernel_cost cast 15 1 31 2 0x3555

#print "POSIT_GENERAL add p=31 es=3"
#kernel_cost add 31 3 0x35555555 0x6aaaaaaa
#print "POSIT_GENERAL mul p=31 es=3"
#kernel_cost mul 31 3 0x35555555 0x6aaaaaaa
#print "POSIT_GENERAL div p=31 es=3"
#kernel_cost div 31 3 0x35555555 0x6aaaaaaa
#print "POSIT_GENERAL sqrt p=31 es=3"
#kernel_cost sqrt 31 3 0x35555555
#print "POSIT_GENERAL fma p=31 es=3"
#kernel_cost fma 31 3 0x35555555 0x6aaaaaaa 0x55555555

#print "POSIT_GENERAL add p=31 es=2"
#kernel_cost add 31 2 0x35555555 0x6aaaaaaa
#print "POSIT_GENERAL mul p=31 es=2"
#kernel_cost mul 31 2 0x35555555 0x6aaaaaaa
#print "POSIT_GENERAL div p=31 es=2"
#kernel_cost div 31 2 0x35555555 0x6aaaaaaa
#print "POSIT_GENERAL sqrt p=31 es=2"
#kernel_cost sqrt 31 2 0x35555555
#print "POSIT_GENERAL fma p=31 es=2"
#kernel_cost fma 31 2 0x35555555 0x6aaaaaaa 0x55555555
