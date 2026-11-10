/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Literal
public import FloatLib.Numerics.Packed.Sos
public import FloatLib.Numerics.Packed.Window

/-!
# Packed rows

These checks run the packed-row programs in the kernel, first on the row `[1, -2, 3]` from the
`FloatLib.Numerics.Packed.Basic` documentation and then on rows of the size of a certificate.

## Main statements

* Unsigned rows: the lanes of `(signed := false)` rows, their range check, their lane sum by one
  remainder, and their product (`lanes_mul`).
* Two rows of 200 entries in `[-2 ^ 100, 2 ^ 100)`, `x` from `PackedRow.txt` and `y` written in
  this file, both drawn by Python's `random` with seed `20261107`. In lanes of 256 bits, two range
  checks and one Kronecker product give the 399 entries of the Cauchy product (`entries_mul`). One
  entry of the product, its `l1` norm, the sum of `x` and the middle entry of the autocorrelation of
  `x` are compared with values Python computed from the integers.
* Windows, rounding and symmetric rows on small rows: a window of `[1, -2, 3]`, `[13, -7, 4, -1]`
  rounded to multiples of `4` with its remainders and their sum, the cosine and sine rows of the
  half row `[5, 2, 1]`, the signs that turn one into the other, and the derivative weights.
* Sums of squares: `2 z⁻¹ + 5 + 2 z = |2 + z|²` passes `sosCheck` for two true bounds and fails for
  the false bound `≥ 3/2`.
* Negative controls that the kernel has to refuse: a range check fails on an entry one past its
  bound and on a lane beyond the row, a wrong product is not equal to the computed one, and lanes
  that are too narrow for a product no longer hold the Cauchy product. `packed_row` itself rejects
  an entry that does not fit its width or its sign.

## Implementation notes

On our machine the kernel checks `xy_check` in about a millisecond: two range checks, a product of
two 51,200-bit numbers and a comparison.

Every check runs under `set_option maxHeartbeats` at about three times the heartbeats it uses, so
the build fails if its kernel cost grows.

## References

* David Harvey, *Faster polynomial multiplication via multipoint Kronecker substitution*,
  J. Symbolic Comput. 44 (2009), 1502–1510, <https://doi.org/10.1016/j.jsc.2009.05.004>.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.Packed

open FloatLib.Numerics.Packed

/-! ## The worked example -/

/-- The row `[1, -2, 3]` in lanes of 8 bits. -/
packed_row small (width := 8) := [1, -2, 3]

/-- The row `[4, -5]` in lanes of 8 bits. -/
packed_row small' (width := 8) := [4, -5]

set_option maxHeartbeats 200 in
/-- The literal is `129 + 126 * 256 + 131 * 256 ^ 2`, and it stands for `196097`. -/
theorem small_eq : small = 8617601 ∧ toInt 8 3 small = 196097 := by decide +kernel

set_option maxHeartbeats 400 in
/-- `packed_row` and `pack` give the same row, and its entries come back. -/
theorem small_entries : pack 8 [1, -2, 3] = small ∧ entries 8 3 small = [1, -2, 3] := by
  decide +kernel

set_option maxHeartbeats 1000 in
/-- The sum, the `l1` norm, the reverse and the autocorrelation `[3, -8, 14, -8, 3]`, whose middle
entry is `1 + 4 + 9`. -/
theorem small_sums :
    sum 8 3 (toInt 8 3 small) = 2 ∧ absSum 8 3 (toInt 8 3 small) = 6 ∧
      entries 8 3 (rev 8 3 small) = [3, -2, 1] ∧
      entries 8 5 (ofInt 8 5 (autocorr 8 3 small)) = [3, -8, 14, -8, 3] := by
  decide +kernel

set_option maxHeartbeats 400 in
/-- The product of the integers of `[1, -2, 3]` and `[4, -5]` holds their Cauchy product. -/
theorem small_mul :
    entries 8 4 (ofInt 8 4 (toInt 8 3 small * toInt 8 2 small')) = [4, -13, 22, -15] := by
  decide +kernel

/-! ## Unsigned rows -/

/-- The row `[1, 200, 0]` of natural numbers in lanes of 8 bits. -/
packed_row count (width := 8) (signed := false) := [1, 200, 0]

set_option maxHeartbeats 400 in
/-- Its lanes, a range check that holds (`200 < 2 ^ 8`) and one that fails (`200 ≥ 2 ^ 7`), its lane
sum, and the unsigned packing of the same list. -/
theorem count_checks :
    lanes 8 3 count = [1, 200, 0] ∧ guard 8 8 3 count (signed := false) = true ∧
      guard 8 7 3 count (signed := false) = false ∧ laneSum 8 count = 201 ∧
      pack 8 [1, 200, 0] (signed := false) = count := by
  decide +kernel

set_option maxHeartbeats 1000 in
/-- `rev` reverses the lanes of an unsigned row, and unsigned `pack` keeps natural entries. -/
theorem count_rev_pack :
    lanes 8 3 (rev 8 3 count) = [0, 200, 1] ∧
      lanes 8 3 (pack 8 [1, 200, 0] (signed := false)) = [1, 200, 0] := by
  refine ⟨by rw [lanes_rev, count_checks.1]; rfl, ?_⟩
  exact lanes_pack (xs := [1, 200, 0]) (by decide)

/-- `[3, 5]` and `[7]` in lanes of 8 bits, both below `2 ^ 3`. -/
packed_row three (width := 8) (signed := false) := [3, 5]

/-- `[7]` in lanes of 8 bits. -/
packed_row seven (width := 8) (signed := false) := [7]

set_option maxHeartbeats 1000 in
/-- The product of two unsigned guarded rows holds their Cauchy product `[21, 35]`, because
`2 * 2 ^ 3 * (1 * 2 ^ 3) < 2 ^ 8`. -/
theorem lanes_three_seven :
    (lanes 8 2 (three * seven)).map (Nat.cast : Nat → Int) = conv [3, 5] [7] := by
  have h : (guard 8 3 2 three (signed := false) && guard 8 3 1 seven (signed := false)) = true := by
    decide +kernel
  simp only [Bool.and_eq_true] at h
  have e : lanes 8 2 three = [3, 5] ∧ lanes 8 1 seven = [7] := by decide +kernel
  have := lanes_mul h.1 h.2 (by decide) (by decide) (by decide)
  rw [e.1, e.2] at this
  simpa using this

/-! ## Rows of certificate size -/

/-- 200 entries in `[-2 ^ 100, 2 ^ 100)` from a file. -/
packed_row x (width := 256) from "PackedRow.txt"

/-- 200 entries in `[-2 ^ 100, 2 ^ 100)` in the source. -/
packed_row y (width := 256) := [
    746937020469138216921636019615, -150408108809332160171108719518,
    -169184908980893967098861031093, 1011294902037165571820749270428,
    -1235221701773622484802160318147, -885284567188981765893769600841,
    -164985009087781935856812922008, -247693937323592347274272875485,
    -70808308217794596875429902861, -628526870692512289937687161191,
    -313444036384554803711637392603, 680479037750443084374525743403,
    1142234417905895161160845498320, -365509960770124376129521191107,
    659048062849911131850523014032, 160508135261232823877000633485,
    1094237388618632678386234222921, 790453565490610711991456184094,
    964793313779105811975192442734, 148403393303060579155100371506,
    156826119094456667797367141072, -813414173764380345844019295419,
    -807144537968427233869457148397, 840330311372922454374218066112,
    918353036941199721399956676472, -973456662684939293443201788599,
    -1159046472997013695509242679458, 624205676586364431344680958570,
    -744197383061841288376963688951, 567658584984902412287801981357,
    -1266562276209673639677280616517, 175691504292176702209194135283,
    1205898511453345053887269821308, -1176507929009496212487425120306,
    -1164653103723880390939167055042, 780212383857604196514092589388,
    -844647411570345413926622899430, -713488547302128216891554037954,
    -662670195559369754784681419063, -143947733587165327958555841515,
    -11184596392712312727934997258, 472935606338421870405672459258,
    418106305233794385174304510994, -1140918603513123975714585643823,
    -734477480104369123177059378296, -718902349254459579744195479982,
    1160883812216043312252787055654, 481930823426286602757521287881,
    -1135149408300779360899187433917, 314598014593245059277709488363,
    1229852545090229321227291582993, 144126110279547642904466214530,
    975761486970695641117434156477, 556750663780604900017731828611,
    838231184776296629757110643084, -644701306457441268793435447033,
    -331041299568365509983319798003, -893202099269876914864966185842,
    774514281515912424587175263065, 796629654671519943023126639022,
    -1185187584015579616902934326898, 116519206312030352843695000877,
    885448987687783326688914359625, 1166561028201289528005219134288,
    1098538681211557835895494928070, -839837576244465470656481750448,
    787540371805001832014720095485, -1060332794783398015351524701349,
    -153261193474229336265009104831, 230908943480974515757406904923,
    233773330497362104812476190493, -1108724391019946998190211729186,
    -880326710692481481920674360768, -993513820114602192133767944974,
    835103207330739888855723495818, 1051717753162144957884346449963,
    -658991054418827752790516772088, 194114090396894115478471119600,
    545243197240217837475653123812, 737582050106252116117395510054,
    -1023398105840050790659385224777, 469956376136527336094127436865,
    770388611491211458065183552934, 327376729534050695323541235361,
    -179166611642054766031103402126, 1159646906755251441316130674954,
    -623859278084171417571629185562, -2872532120369845846460250451,
    463185456446345271157486342661, 264765000723339889190423837148,
    54056445964100014085348107506, -951552407465128964439274571097,
    973916563231206204306849934459, 1064134371137703504620417469104,
    -446252340662594293061232942064, 515280431572741736732210907138,
    -1210629081015598621142228836731, -178347868867074194757407249805,
    -59348634216867580727558758118, 855998845690652332528372618847,
    1022332716487544079706049303495, -1210140799759166026326968234278,
    -548617721208819636082302040345, 690366117245749121260041701514,
    763967556722072546350656574631, -629681656883333295267922176614,
    -367954492276747054994421498965, 617025729512692598351562961926,
    -635099775277591239807427460832, 542330050423704168184880427218,
    471176765439719235900515217744, 1130396952894690976875358955397,
    311669876541407829392753663577, -714107851364916370523025283877,
    -755004124778663416143258973434, 944884129276579488624019270330,
    1125517930137897768737473754858, -508840832745768068555621771456,
    -42454837004428651333983451581, 73123888415677487359276689005,
    182508429126902177566562776468, 353118884529737259591133734216,
    -1240804752658832844486983456451, 572155958504134469108644917159,
    946022433426196190675620027792, -1251923745064489501583273220314,
    -354042694286570896182189179464, 944553989952762019479756108831,
    -352776134666546385613598395822, -157728477549525225942166000455,
    -538585630996008099490607207193, -157117763536790860526180049100,
    -657104093287396059930224679409, -778741213133043358584237259545,
    -1052988669938271778422343442917, -733805168949164751490318045812,
    1053307270198909278848493016258, -1213612342606405954495317177636,
    -650970937000661405861370394815, 45048048892156416759411650392,
    1086264610581589536037488696443, -1179195593281736548638520627024,
    325918290999716387683144188654, 518869796744987085791957231955, 5887241462017589643574911993,
    -1207033170252648141089162549776, -877957481131525067078969364775,
    -261262675975231111494386751448, -521777750835163982838021827684,
    -1182087830292066950598517162004, 639655830997852475683457594474,
    -765000678285422497466429105924, 177489800720909116047642086958,
    760249351596458012305091086801, -342539376434910068032934267880,
    636314053686144111554394365478, -493460739682415814974114334683,
    1138279231044584745555001210336, 579653455256481854265467363315,
    674349328364476167344766542630, 241596261979673546599079510637,
    553814626612729147312869030902, -381340666704593922065348301713,
    -240697219501873113134371915438, -325913431594783429896528153744,
    207584383479998294643346830248, 207881272159584334199363988085,
    778572686790808349443276821417, 1217328494564875327819840873993,
    1135597382972164475364713564712, 1164595903404184900201615435965,
    -627227719929937764578860226045, 310438743561775461214427607328,
    -733440171712363956147371649190, 1092806045428179258042706315450,
    1126355298511315593060207721305, -1032329638083519375650423722161,
    728000356042769934506005121265, -970365357320197031493353512235,
    1023797847186879780785484203769, -200780572565744679360496855884,
    -1075749705412891515473454608433, -252541094475272791047641017715,
    -146755050058669077872183918732, 879920742565873408634473607290,
    1081573225950424911743146696637, -645275239925793609548876776946,
    168276479271252336641774423597, -604779994859025116745122108458,
    1198546511931513531956165034620, 1039421443037385378306827655685,
    -1205644790559156077205948223551, 554322922791765635666084787611,
    -829073760139695240332814102329, -766540052486334169067665063449,
    -258518649499665780235703420447, 812719321659558181923912947511,
    -1212468817281991504179694430800, -499162653745870249315230074857,
    49135456674118861867460260211]

set_option maxHeartbeats 2000 in
/-- Both range checks and the headroom inequality
`200 * 2 ^ 100 * (200 * 2 ^ 100) < 2 ^ (256 - 1)`. -/
theorem xy_check : (guard 256 100 200 x && guard 256 100 200 y &&
    Nat.blt (200 * 2 ^ 100 * (200 * 2 ^ 100)) (2 ^ (256 - 1))) = true := by
  decide +kernel

set_option maxHeartbeats 400 in
/-- The 399 entries of the product row are the Cauchy product of the entries of `x` and `y`. -/
theorem entries_xy :
    entries 256 399 (ofInt 256 399 (toInt 256 200 x * toInt 256 200 y)) =
      conv (entries 256 200 x) (entries 256 200 y) := by
  have h := xy_check
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact entries_mul h.1.1 h.1.2 h.2 (by decide) (by decide)

set_option maxHeartbeats 1000 in
/-- The middle entry and the `l1` norm of the product, the sum of `x`, and the middle entry of the
autocorrelation of `x`, against Python. -/
theorem xy_values :
    entry 256 199 (ofInt 256 399 (toInt 256 200 x * toInt 256 200 y)) =
        15879028483883134409353841326661464910939496462405927985740722 ∧
      absSum 256 399 (toInt 256 200 x * toInt 256 200 y) =
        1748424849571468223340438493641679564534629340385589024958575892 ∧
      sum 256 200 (toInt 256 200 x) = 3067330563433702641821458680154 ∧
      entry 256 199 (ofInt 256 399 (autocorr 256 200 x)) =
        104333462771139837493792845670301219086778922379709309132792226 := by
  decide +kernel

/-! ## Windows, rounding and symmetric rows -/

/-- `[13, -7, 4, -1]` in lanes of 16 bits. -/
packed_row fine (width := 16) := [13, -7, 4, -1]

set_option maxHeartbeats 1000 in
/-- Lanes `1` and `2` of `[1, -2, 3]` are `[-2, 3]`. Rounding `[13, -7, 4, -1]` down to multiples of
`4` gives `[3, -2, 1, -1]` and the remainders `[1, 1, 0, 3]`, whose sum `5` one remainder reads, and
`2 ^ 2 * [3, -2, 1, -1] + [1, 1, 0, 3]` is the row again. -/
theorem window_and_rounding :
    entries 8 2 (ofInt 8 2 (restrict 8 3 1 2 (toInt 8 3 small))) = [-2, 3] ∧
      entries 16 4 (ofInt 16 4 (shiftDown 16 4 2 (toInt 16 4 fine))) = [3, -2, 1, -1] ∧
      lanes 16 4 (low 16 4 2 (toInt 16 4 fine)) = [1, 1, 0, 3] ∧
      laneSum 16 (low 16 4 2 (toInt 16 4 fine)) = 5 ∧
      2 ^ 2 * shiftDown 16 4 2 (toInt 16 4 fine) + low 16 4 2 (toInt 16 4 fine) =
        toInt 16 4 fine := by
  decide +kernel

/-- The half row `[5, 2, 1]`, which stands for `5 + 2 cos u + cos 2u`. -/
packed_row half (width := 8) := [5, 2, 1]

set_option maxHeartbeats 1000 in
/-- `unfold` writes the cosine row `[1, 2, 10, 2, 1]` and the sine row `[-1, -2, 0, 2, 1]`, `signs`
takes the first to the second, and `ramp` multiplies entry `k` by `k`. -/
theorem symmetric_rows :
    entries 8 5 (ofInt 8 5 (unfold 8 3 half)) = [1, 2, 10, 2, 1] ∧
      entries 8 5 (ofInt 8 5 (unfold 8 3 half (odd := true))) = [-1, -2, 0, 2, 1] ∧
      entries 8 5 (ofInt 8 5 (signs 8 3 (unfold 8 3 half))) = [-1, -2, 0, 2, 1] ∧
      entries 8 3 (ofInt 8 3 (ramp 8 3 half)) = [0, 2, 2] := by
  decide +kernel

set_option maxHeartbeats 4000 in
/-- The rounding theorems on `[13, -7, 4, -1]`: the row is `4` times its rounding plus the
remainders, and one remainder reads the `l1` norm of the remainders. -/
theorem rounding_spec :
    eval (2 ^ 16) [13, -7, 4, -1] = 2 ^ 2 * shiftDown 16 4 2 (eval (2 ^ 16) [13, -7, 4, -1]) +
        low 16 4 2 (eval (2 ^ 16) [13, -7, 4, -1]) ∧
      laneSum 16 (low 16 4 2 (eval (2 ^ 16) [13, -7, 4, -1])) =
        l1 ([13, -7, 4, -1].map (· % 2 ^ 2)) := by
  have hx : ∀ x ∈ [13, -7, 4, -1], Fits 16 x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    unfold Fits
    rcases hx with rfl | rfl | rfl | rfl <;> decide
  exact ⟨eval_shiftDown_add_low (by decide) (by decide) hx,
    laneSum_low (by decide) (by decide) hx (by decide)⟩

set_option maxHeartbeats 400 in
/-- `signs` on the cosine row of `[5, 2, 1]` is the sign row of its entries. -/
theorem signs_spec :
    signs 8 3 (unfold 8 3 half) = eval (2 ^ 8) (signRow 2 [1, 2, 10, 2, 1]) := by
  rw [signs_eq (by decide), symmetric_rows.1]

set_option maxHeartbeats 1000 in
/-- `pack` gives the biased row of the value of any list whose entries fit, so the entries come
back out. -/
theorem pack_spec : entries 8 3 (pack 8 [1, -2, 3]) = [1, -2, 3] := by
  have hx : ∀ x ∈ ([1, -2, 3] : List Int), Fits 8 x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    unfold Fits
    rcases hx with rfl | rfl | rfl <;> decide
  rw [pack_eq_ofInt (by decide) hx]
  exact entries_ofInt_eval (n := 3) (by decide) (Nat.le_refl _) hx

set_option maxHeartbeats 1000 in
/-- The autocorrelation of `[13, -7, 4, -1]` reads back as the Cauchy product of the row with its
reverse, because `4 * 2 ^ 4 * (4 * 2 ^ 4) < 2 ^ 15`, and its sum is the square of the sum of the
row, `9 ^ 2`. -/
theorem fine_autocorr :
    entries 16 7 (ofInt 16 7 (autocorr 16 4 fine)) =
        conv (entries 16 4 fine) (entries 16 4 fine).reverse ∧
      sum 16 4 (toInt 16 4 fine) = 9 ∧ sum 16 7 (autocorr 16 4 fine) = 81 := by
  have hg : guard 16 4 4 fine = true := by decide +kernel
  refine ⟨entries_autocorr hg (by decide) (by decide), ?_, by decide +kernel⟩
  rw [sum_toInt hg (by decide)]
  decide +kernel

/-! ## Sums of squares -/

/-- `2 z⁻¹ + 5 + 2 z`, which is `|2 + z|²` on the circle. -/
packed_row square (width := 16) := [2, 5, 2]

/-- Its spectral factor `[2, 1]`. -/
packed_row root (width := 16) := [2, 1]

set_option maxHeartbeats 200 in
/-- The check passes for `T ≥ 0`, with `T - |h|² = 0`, and for `T ≥ -1`. It refuses `T ≥ 3/2`,
which is false at `z = -1`, where `T = 1`: the row `2 T - 3 - 2 |h|²` has centre `-3`. -/
theorem small_squares :
    sosCheck 16 3 2 2 2 0 1 0 1 square (ofInt 16 3 0) root 0 = true ∧
      sosCheck 16 3 2 2 2 0 1 1 1 square (ofInt 16 3 0) root 0 = true ∧
      sosCheck 16 3 2 2 2 0 2 (-3) 2 square (ofInt 16 3 0) root 0 = false := by
  decide +kernel

/-! ## Negative controls -/

/-- `2 ^ 20` is one past the range `[-2 ^ 20, 2 ^ 20)`; `-2 ^ 20` is inside it. -/
packed_row edge (width := 64) := [5, -1048576, 1048576]

set_option maxHeartbeats 400 in
/-- The range check refuses the entry `2 ^ 20` and accepts the first two lanes alone. Read as a row
of two lanes, the whole literal is refused for its third lane, even with a range that holds the
first two entries. -/
theorem guard_refuses :
    guard 64 20 3 edge = false ∧ guard 64 20 2 (edge % 2 ^ 128) = true ∧
      guard 64 21 2 edge = false := by
  decide +kernel

set_option maxHeartbeats 400 in
/-- A product row that differs from the computed one in its last entry is refused. -/
theorem wrong_product :
    Nat.beq (ofInt 8 4 (toInt 8 3 small * toInt 8 2 small')) (pack 8 [4, -13, 22, -14]) =
      false := by
  decide +kernel

set_option maxHeartbeats 400 in
/-- In lanes of 8 bits, `[100, 100] * [100]` overflows: the Cauchy product `[10000, 10000]` does not
fit, and the lanes of the product row hold something else. This is why `entries_mul` asks for
headroom. -/
theorem overflow_breaks_lanes :
    entries 8 2 (ofInt 8 2 (toInt 8 2 (pack 8 [100, 100]) * toInt 8 1 (pack 8 [100]))) ≠
      conv [100, 100] [100] := by
  decide +kernel

set_option maxHeartbeats 2000 in
/-- The kernel refuses a wrong value for every program: a lane sum, an `l1` norm, a sum, a reversal,
a window, a rounding, a remainder row, a cosine row, a sign row and a derivative row. -/
theorem wrong_values :
    laneSum 8 count ≠ 202 ∧ absSum 8 3 (toInt 8 3 small) ≠ 7 ∧ sum 8 3 (toInt 8 3 small) ≠ 3 ∧
      entries 8 3 (rev 8 3 small) ≠ [1, -2, 3] ∧
      entries 8 2 (ofInt 8 2 (restrict 8 3 1 2 (toInt 8 3 small))) ≠ [1, -2] ∧
      entries 16 4 (ofInt 16 4 (shiftDown 16 4 2 (toInt 16 4 fine))) ≠ [3, -1, 1, 0] ∧
      lanes 16 4 (low 16 4 2 (toInt 16 4 fine)) ≠ [1, 3, 0, 3] ∧
      entries 8 5 (ofInt 8 5 (unfold 8 3 half)) ≠ [1, 2, 5, 2, 1] ∧
      entries 8 5 (ofInt 8 5 (signs 8 3 (unfold 8 3 half))) ≠ [1, 2, 0, 2, 1] ∧
      entries 8 3 (ofInt 8 3 (ramp 8 3 half)) ≠ [0, 2, 1] := by
  decide +kernel

set_option maxHeartbeats 200 in
/-- Without headroom the remainder is not the sum: the lanes of `[100, 100, 100]` add up to `300`,
more than `2 ^ 8 - 1`, and `absSum` returns `45`. This is why `absSum_eval` asks for
`l1 < 2 ^ (w - 1)`. -/
theorem absSum_overflows : absSum 8 3 (toInt 8 3 (pack 8 [100, 100, 100])) = 45 := by
  decide +kernel

set_option maxHeartbeats 400 in
/-- `linked` accepts `[2, -5/2]` at the denominator `2` for the row `[4, -5]`, and refuses
`[2, -2]`. -/
theorem linked_checks :
    linked 8 2 small' 0 [2, -5 / 2] = true ∧ linked 8 2 small' 0 [2, -2] = false := by
  decide +kernel

/-- error: entry 1 is 128, which does not fit a signed lane of width 8 -/
#guard_msgs (error) in
packed_row tooWide (width := 8) := [1, 128]

/-- error: entry 0 is -1, which does not fit an unsigned lane of width 8 -/
#guard_msgs (error) in
packed_row negative (width := 8) (signed := false) := [-1]

/-- error: entry 0 is 256, which does not fit an unsigned lane of width 8 -/
#guard_msgs (error) in
packed_row tooWideUnsigned (width := 8) (signed := false) := [256]

/-! Rows files hold plain decimal integers. Digit separators, signs other than a leading `-`, and
other characters are errors, also in tokens long enough to be read in blocks. -/

#guard (parseEntries "12, -3  # comment\n7").toOption == some #[12, -3, 7]
#guard (parseEntries "123456789012345678901234567890 -42").toOption ==
  some #[123456789012345678901234567890, -42]
#guard (parseEntries "1_000").toOption == none
#guard (parseEntries "10000000000000_0000000000").toOption == none
#guard (parseEntries "+5").toOption == none
#guard (parseEntries "éééééééééé").toOption == none

end FloatLibTests.Conformance.Numerics.Packed
