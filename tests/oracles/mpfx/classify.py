"""Group FloatLib/MPFX differences in a run.sh work directory.

The classes are: an exact zero under roundTowardNegative returned as +0 (IEEE 754 6.3 requires -0),
sqrt(-inf) without the invalid flag, a lost overflow flag when the container's own result
overflows. Remaining EFT differences are grouped as `eft_difference`; this identifies the engine,
not the cause. In particular, a mismatch alone does not establish error-term underflow. Other
unexplained differences are reported as `other`.

    python3 -I classify.py WORK
"""
import collections, glob, os, re, subprocess, sys

work = sys.argv[1]
binary = os.path.join(work, 'mpfx_list')
pattern = re.compile(r'MISMATCH (\w+) (\S+) (\S+) (\S+): mpfx (\S+) flags (\w+), floatlib (\S+) flags (\w+)')
counts = collections.Counter()
examples = {}
for inputs in sorted(glob.glob(os.path.join(work, 'cases', '*.in'))):
    base = os.path.basename(inputs)[:-3]
    fmt, op, _ = base.split('.')
    width, fraction = map(int, re.match(r'e(\d+)m(\d+)', fmt).groups())
    containers = ['double'] + (['float'] if width <= 8 and fraction <= 21 else [])
    for mode in ['near_even', 'minMag', 'min', 'max']:
        floatlib = os.path.join(work, 'out', f'{base}.{mode}.floatlib')
        for container in containers:
            for engine in ['hw', 'eft']:
                output = subprocess.run(
                    [binary, fmt, container, engine, op, mode, inputs, floatlib],
                    env=dict(os.environ, MPFX_ALL='1'), capture_output=True, text=True, check=True).stdout
                for line in output.splitlines():
                    match = pattern.match(line)
                    if not match:
                        continue
                    _, a, _, _, mpfx_value, mpfx_flags, floatlib_value, floatlib_flags = match.groups()
                    mpfx_flags, floatlib_flags = int(mpfx_flags, 16), int(floatlib_flags, 16)
                    if mpfx_value == '0x0p+0' and floatlib_value == '-0x0p+0' and mode == 'min':
                        kind = 'zero_sign_rtn'
                    elif op == 'sqrt' and a == '-inf':
                        kind = 'sqrt_neg_inf_invalid'
                    elif (mpfx_value == floatlib_value and floatlib_flags & 4 and not mpfx_flags & 4
                          and mpfx_flags | 4 == floatlib_flags):
                        kind = 'overflow_flag_lost'
                    else:
                        kind = 'eft_difference' if engine == 'eft' else 'other'
                    counts[(kind, fmt, container, engine)] += 1
                    examples.setdefault((kind, engine), line)
print('class,format,container,engine,results')
for key in sorted(counts):
    print(','.join(map(str, key + (counts[key],))))
for key, line in sorted(examples.items()):
    print('# example', *key, line, file=sys.stderr)
