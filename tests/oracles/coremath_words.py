"""Encode the distinct entries of a CORE-MATH worst-case list (`.wc`) as binary64 words.

The lists name inputs as hexadecimal floats or as +/-nan, +/-snan, +/-inf, and +/-0. The output
has one decimal word per line, sorted, for `execFloatCertifiedExpLog FN 64 WORDS`.

    python3 -I coremath_words.py expm1.wc expm1-words.txt
"""
import struct, sys
special = {'+snan': 0x7ff0000000000001, '-snan': 0xfff0000000000001, 'snan': 0x7ff0000000000001,
           '+nan': 0x7ff8000000000000, '-nan': 0xfff8000000000000, 'nan': 0x7ff8000000000000,
           '+inf': 0x7ff0000000000000, '-inf': 0xfff0000000000000, 'inf': 0x7ff0000000000000}
words = set()
for line in open(sys.argv[1]):
    s = line.split('#')[0].strip()
    if not s: continue
    words.add(special[s] if s in special else struct.unpack('<Q', struct.pack('<d', float.fromhex(s)))[0])
open(sys.argv[2], 'w').write('\n'.join(map(str, sorted(words))) + '\n')
print(sys.argv[1], len(words))
