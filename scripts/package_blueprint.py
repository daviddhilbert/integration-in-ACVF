#!/usr/bin/env python3
"""Package checked blueprint outputs; omit caches, logs and raw audit dumps."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def package(output):
    subprocess.run([sys.executable, str(ROOT / 'scripts/check_blueprint.py'), '--rendered'], check=True)
    pdf = ROOT / 'blueprint/print/print.pdf'
    assert pdf.is_file() and pdf.stat().st_size > 1000, 'Build the PDF first'
    output.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(pdf, output / 'integration-in-ACVF-blueprint.pdf')
    shutil.copyfile(ROOT / 'blueprint/PALOMAR-HANDOFF.md', output / 'PALOMAR-HANDOFF.md')
    shutil.copyfile(ROOT / 'verification/project-integrity-2026-11-16.json', output / 'project-integrity.json')
    web = ROOT / 'blueprint/web'
    with zipfile.ZipFile(output / 'integration-in-ACVF-blueprint-web.zip', 'w', zipfile.ZIP_DEFLATED) as z:
        for p in sorted(web.rglob('*')):
            if p.is_file():
                z.write(p, Path('integration-in-ACVF-blueprint-web') / p.relative_to(web))
    with zipfile.ZipFile(output / 'integration-in-ACVF-blueprint-source.zip', 'w', zipfile.ZIP_DEFLATED) as z:
        bp = ROOT / 'blueprint'
        files = [p for p in bp.iterdir() if p.is_file() and not p.name.startswith('.')]
        files += [p for p in (bp / 'src').iterdir() if p.is_file() and (p.suffix in ('.tex', '.py', '.cfg', '.tsv') or p.name == 'latexmkrc')]
        files += [ROOT / 'scripts/check_blueprint.py', ROOT / 'scripts/package_blueprint.py', ROOT / 'verification/project-integrity-2026-11-16.json']
        for p in sorted(files):
            z.write(p, Path('integration-in-ACVF-blueprint-source') / p.relative_to(ROOT))
    names = ['integration-in-ACVF-blueprint.pdf', 'integration-in-ACVF-blueprint-web.zip', 'integration-in-ACVF-blueprint-source.zip', 'PALOMAR-HANDOFF.md', 'project-integrity.json']
    (output / 'SHA256SUMS').write_text(''.join(hashlib.sha256((output / n).read_bytes()).hexdigest() + '  ' + n + '\n' for n in names))
    print(json.dumps({'status': 'PASS', 'output': str(output), 'files': names + ['SHA256SUMS']}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    package(parser.parse_args().output.resolve())
