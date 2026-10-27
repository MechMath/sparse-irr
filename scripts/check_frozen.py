#!/usr/bin/env python3
"""Compare frozen declaration headers (up to ':=') between a git revision and the working tree."""
import re, subprocess, sys
rev = sys.argv[1] if len(sys.argv) > 1 else 'HEAD'
files = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', rev, 'SparseIrred'], text=True).split()
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|inductive|structure|instance)\s+([^\s(:{\[]+)', re.M)
def headers(text):
    out = {}
    ms = list(decl.finditer(text))
    for i, m in enumerate(ms):
        end = ms[i+1].start() if i+1 < len(ms) else len(text)
        body = text[m.start():end]
        kind = m.group(1)
        if kind in ('theorem', 'lemma'):
            j = body.find(':=')
            body = body[:j] if j >= 0 else body
        else:
            j = body.find('\n\n')
            body = body[:j] if j >= 0 else body
        out[m.group(2)] = ' '.join(body.split())
    return out
bad = 0
for f in files:
    old = subprocess.check_output(['git', 'show', f'{rev}:{f}'], text=True)
    try: new = open(f).read()
    except FileNotFoundError: print('MISSING', f); bad += 1; continue
    ho, hn = headers(old), headers(new)
    for name, h in ho.items():
        if name not in hn: print(f'REMOVED {f}: {name}'); bad += 1
        elif hn[name] != h:
            # allow ':= by sorry' -> term proof difference only (already stripped); report others
            print(f'CHANGED {f}: {name}\n  old: {h[:300]}\n  new: {hn[name][:300]}'); bad += 1
print('frozen-check:', 'OK' if bad == 0 else f'{bad} problems')
sys.exit(1 if bad else 0)
