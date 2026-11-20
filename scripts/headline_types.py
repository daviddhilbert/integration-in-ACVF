#!/usr/bin/env python3
"""Compare full headline statements with the committed, reviewed baseline.

Adapted from ACVF-QE scripts/verify.py (headline statement baseline). Each
section verifier passes the declarations it already audits. This module
writes one `#check @name` per declaration, elaborates it with fixed printing
options, and compares the output with verification/headline-types/<label>.txt.
A changed statement therefore fails even when its axioms stay clean.

Set UPDATE_HEADLINE_BASELINE=1 only after reviewing an intended statement
change; the run then rewrites the baseline instead of comparing.
"""

import difflib
import hashlib
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
BASELINE_DIR = ROOT / 'verification' / 'headline-types'
OPTIONS = ('set_option pp.fullNames true\n'
           'set_option format.width 120\n')
MAX_DIFF_LINES = 200


def check(label, imports, names, out_dir, lean=('lake', 'env', 'lean'), env=None):
    """Elaborate `#check @name` for every name and compare with the baseline.

    Returns a small record for the caller's receipt; raises RuntimeError on
    any elaboration error, missing declaration or statement difference.
    """
    if len(names) != len(set(names)):
        raise RuntimeError(f'{label}: duplicate headline names')
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    source = out_dir / 'HeadlineTypes.lean'
    source.write_text(''.join(f'import {module}\n' for module in imports) + OPTIONS
                      + ''.join(f'#check @{name}\n' for name in names), encoding='utf-8')
    result = subprocess.run([*lean, str(source)], cwd=ROOT, env=env, capture_output=True,
                            text=True, encoding='utf-8', errors='replace')
    output = result.stdout + result.stderr
    (out_dir / 'HeadlineTypes.log').write_text(output, encoding='utf-8')
    if result.returncode or re.search(r'HeadlineTypes\.lean:\d+:\d+: error', output):
        raise RuntimeError(f'{label}: headline type elaboration failed; see {out_dir / "HeadlineTypes.log"}')
    current = re.sub(r'^\S*HeadlineTypes\.lean:\d+:\d+: (?:info: )?', '', output, flags=re.M)
    # Every message starts in column 0 with the (optionally @-prefixed) name;
    # continuation lines of a statement are indented by the pretty printer.
    printed = re.findall(r'(?m)^@?(\S+?)(?:\.\{[^}\n]*\})? :', current)
    missing = sorted(set(names) - set(printed))
    if missing or len(printed) != len(names):
        raise RuntimeError(f'{label}: {len(printed)} statements printed for {len(names)} names; '
                           f'missing {missing[:10]}')
    baseline = BASELINE_DIR / f'{label}.txt'
    record = {'baseline': str(baseline.relative_to(ROOT)), 'declarations': len(names),
              'sha256': hashlib.sha256(current.encode('utf-8')).hexdigest()}
    if os.environ.get('UPDATE_HEADLINE_BASELINE') == '1':
        BASELINE_DIR.mkdir(parents=True, exist_ok=True)
        baseline.write_text(current, encoding='utf-8')
        print(f'{label}: updated {record["baseline"]} ({len(names)} declarations)')
        return record
    old = baseline.read_text(encoding='utf-8') if baseline.exists() else None
    if old != current:
        diff = list(difflib.unified_diff(
            (old or '').splitlines(), current.splitlines(),
            record['baseline'], 'current', lineterm=''))
        (out_dir / 'HeadlineTypes.diff').write_text('\n'.join(diff) + '\n', encoding='utf-8')
        print('\n'.join(diff[:MAX_DIFF_LINES]))
        if len(diff) > MAX_DIFF_LINES:
            print(f'... {len(diff) - MAX_DIFF_LINES} more lines in {out_dir / "HeadlineTypes.diff"}')
        raise RuntimeError(f'{label}: headline statements differ from the reviewed baseline '
                           f'{record["baseline"]}' + ('' if old is not None else ' (missing)'))
    print(f'{label}: headline statements match the reviewed baseline ({len(names)} declarations)')
    return record
