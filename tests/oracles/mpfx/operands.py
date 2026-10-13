"""Operand lists for FloatLib-versus-MPFX checks, one line of encoded operands per case.

Sets: `random` (uniform encodings, so every special value appears), `unit` (finite values of
magnitude at most one, spread over every binade), and `tiny` (operands whose results land near the
format's least positive value, where MPFX's container can underflow).

    python3 -I operands.py EXPONENT_BITS FRACTION_BITS OP SET COUNT SEED
"""
import random, sys
W, F, op, kind, n, seed = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4], int(sys.argv[5]), int(sys.argv[6])
random.seed(seed); BIAS = (1 << (W - 1)) - 1; EMAX = (1 << W) - 2
arity = 1 if op == 'sqrt' else 3 if op == 'fma' else 2
def enc(sign, ef, frac): return (sign << (W + F)) | (ef << F) | frac
def word_random(): return random.getrandbits(1 + W + F)
def word_unit():  # finite values with magnitude at most 1, spread over all binades
    ef = random.randint(0, BIAS); frac = random.getrandbits(F) if ef < BIAS else 0
    return enc(random.getrandbits(1), ef, frac)
def word_exp(e, sign=None):  # a value 1.f * 2^e, subnormal if e is below the normal range
    s = random.getrandbits(1) if sign is None else sign
    if e >= 1 - BIAS: return enc(s, min(e + BIAS, EMAX), random.getrandbits(F))
    shift = (1 - BIAS) - e
    if shift > F: return enc(s, 0, 1 + random.getrandbits(1))
    return enc(s, 0, (1 << (F - shift)) | random.getrandbits(F - shift))
bottom = 1 - BIAS - F  # exponent of the least positive value
def tiny():
    t = random.randint(bottom - 2, 1 - BIAS + 4)  # target exponent of the result
    if op == 'sqrt':
        return [word_exp(random.randint(bottom, 1 - BIAS + 8), 0)]
    if op in ('add', 'sub'):
        return [word_exp(t), word_exp(t - random.randint(0, F + 2))]
    if op == 'mul':
        a = random.randint(max(bottom, t - (EMAX - BIAS)), min(EMAX - BIAS, t - bottom))
        return [word_exp(a), word_exp(t - a)]
    if op == 'div':
        b = random.randint(max(bottom, -(EMAX - BIAS)), min(EMAX - BIAS, (EMAX - BIAS) - t))
        return [word_exp(t + b), word_exp(b)]
    a = random.randint(max(bottom, t - (EMAX - BIAS)), min(EMAX - BIAS, t - bottom))
    return [word_exp(a), word_exp(t - a), word_exp(t + random.randint(-3, 3))]
out = sys.stdout
for _ in range(n):
    if kind == 'random': ws = [word_random() for _ in range(arity)]
    elif kind == 'unit': ws = [word_unit() for _ in range(arity)]
    else: ws = tiny()
    if op == 'sqrt' and kind == 'unit': ws = [ws[0] & ~(1 << (W + F))]
    out.write(' '.join(map(str, ws)) + '\n')
