#!/usr/bin/env python3
"""Check that dependency checkouts match the committed Lake manifest."""

import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent


def main():
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
    packages = manifest['packages']
    names = {p['name'] for p in packages}
    required = {'special_transformations', 'acvf_qe', 'mathlib'}
    if not required <= names:
        raise RuntimeError(f'Missing required dependencies: {sorted(required - names)}')
    records = []
    for package in packages:
        if package['type'] != 'git':
            raise RuntimeError(f"Unpinned dependency: {package['name']}")
        directory = ROOT / manifest['packagesDir'] / package['name']
        revision = subprocess.check_output(
            ['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
        if revision != package['rev']:
            raise RuntimeError(f"Dependency revision mismatch: {package['name']}")
        records.append({'name': package['name'], 'revision': revision})
    out = ROOT / '.scratch' / 'ci-verified'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'dependencies.json').write_text(
        json.dumps(records, indent=2) + '\n', encoding='utf-8')
    print(f'PASS: {len(records)} pinned dependency checkouts.')


if __name__ == '__main__':
    main()
