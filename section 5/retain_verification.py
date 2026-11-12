#!/usr/bin/env python3
"""Retain the complete checked receipt losslessly without a GitHub-size blob."""
from pathlib import Path
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parent.parent
CHECKED = ROOT / '.scratch' / 'section5-verified'
DEST = ROOT / 'section 5'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    if (CHECKED / 'status.txt').read_text().strip() != 'PASS':
        raise RuntimeError('A passed Section 5 verification receipt is required')
    raw = (CHECKED / 'receipt.json').read_bytes()
    receipt = json.loads(raw)
    for name, expected in receipt['source_sha256'].items():
        if digest((ROOT / name).read_bytes()) != expected:
            raise RuntimeError('Checked source changed: ' + name)
    for key, file_name in [('audit_source_sha256', 'HeadlineAudit.lean'),
                           ('audit_log_sha256', 'HeadlineAudit.log')]:
        if digest((CHECKED / file_name).read_bytes()) != receipt[key]:
            raise RuntimeError('Retained audit identity changed: ' + file_name)
    for section in ('section 4', 'section 5'):
        directory = ROOT / section / ('IntegrationSection' + section.split()[-1])
        current = {str(p.relative_to(ROOT)) for p in directory.glob('*.lean')}
        checked = {name for name in receipt['source_sha256']
                   if name.startswith(section + '/IntegrationSection')}
        if current != checked:
            raise RuntimeError('Checked Lean source inventory changed: ' + section)
    types = receipt['complete_types']
    if set(types) != {r['name'] for r in receipt['headline_audits']}:
        raise RuntimeError('Type/axiom inventory mismatch')
    compressed = gzip.compress(raw, compresslevel=9, mtime=0)
    if gzip.decompress(compressed) != raw:
        raise RuntimeError('Receipt compression failed its exact round-trip')
    index = {k: v for k, v in receipt.items() if k != 'complete_types'}
    index['complete_type_sha256'] = {
        name: digest(value.encode('utf-8')) for name, value in types.items()
    }
    index['full_receipt'] = {
        'path': 'VERIFICATION.json.gz',
        'format': 'gzip of the unmodified UTF-8 receipt.json',
        'uncompressed_sha256': digest(raw),
        'gzip_sha256': digest(compressed),
        'headline_count': len(types),
    }
    (DEST / 'VERIFICATION.json.gz').write_bytes(compressed)
    (DEST / 'VERIFICATION.json').write_text(json.dumps(index, indent=2) + '\n')
    print(f'Retained {len(types)} complete types and axiom records: '
          f'{len(raw)} bytes losslessly compressed to {len(compressed)} bytes.')


if __name__ == '__main__':
    main()
