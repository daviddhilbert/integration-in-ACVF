#!/usr/bin/env python3
"""Validate blueprint fingerprints, declaration anchors, graph and rendered links.

Adapted from daviddhilbert/ACVF-QE and special-transformations (MIT).
This documentation check does not replace the project's Lean verification.
"""
from pathlib import Path
from urllib.parse import quote, unquote, urlsplit
import argparse
import hashlib
import html
import json
import re
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
BP = ROOT / 'blueprint'


def check(rendered=False):
    manifest = json.loads((BP / 'proof-source-manifest.json').read_text())
    for name, digest in manifest['sha256'].items():
        path = ROOT / name
        assert path.is_file(), f'Missing proof input: {name}'
        assert hashlib.sha256(path.read_bytes()).hexdigest() == digest, f'Proof input changed: {name}'
    sources = {str(p.relative_to(ROOT)) for root in manifest['source_roots'] for p in (ROOT / root).rglob('*.lean')}
    assert sources == {p for p in manifest['sha256'] if p.endswith('.lean')}, 'Lean source inventory changed'
    nodes = json.loads((BP / 'nodes.json').read_text())
    ids = {n['id'] for n in nodes}
    assert len(ids) == len(nodes), 'Duplicate graph labels'
    by_id = {n['id']: n for n in nodes}
    declarations = {}
    for n in nodes:
        assert set(n['dependencies']) <= ids, f'Unknown dependency: {n["id"]}'
        for d in n['declarations']:
            line = (ROOT / d['file']).read_text().splitlines()[d['line'] - 1]
            short = re.escape(d['name'].split('.')[-1])
            assert re.match(r'^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure)\s+' + short + r'\b', line), f'Stale declaration anchor: {d}'
            declarations[d['name']] = quote(d['file'], safe='/') + '#L' + str(d['line'])
    visiting, visited = set(), set()

    def visit(id):
        assert id not in visiting, f'Cyclic mathematical dependencies: {id}'
        if id in visited:
            return
        visiting.add(id)
        for dep in by_id[id]['dependencies']:
            visit(dep)
        visiting.remove(id)
        visited.add(id)
    for id in ids:
        visit(id)
    links = dict(line.split('\t') for line in (BP / 'src/source-links.tsv').read_text().splitlines())
    assert links == declarations, 'Source-link registry differs from declarations'
    content = (BP / 'src/content.tex').read_text()
    blocks = re.split(r'(?=\\begin\{(?:definition|lemma|theorem|corollary|proposition|remark)\}\[)', content)[1:]
    assert len(blocks) == len(nodes), 'TeX node count differs from graph registry'
    assert set(re.findall(r'\\label\{([^}]+)\}', content)) == ids, 'TeX labels differ'
    for block in blocks:
        id = re.search(r'\\label\{([^}]+)\}', block).group(1)
        deps = {x.strip() for group in re.findall(r'\\uses\{([^}]+)\}', block) for x in group.split(',')}
        decls = {x.strip() for group in re.findall(r'\\lean\{([^}]+)\}', block) for x in group.split(',')}
        assert deps == set(by_id[id]['dependencies']), f'TeX dependency mismatch: {id}'
        assert decls == {d['name'] for d in by_id[id]['declarations']}, f'TeX declaration mismatch: {id}'
    if rendered:
        web = BP / 'web'
        assert (web / 'index.html').is_file(), 'Missing web entry point'
        pages = list(web.glob('*.html'))
        all_html = html.unescape('\n'.join(p.read_text() for p in pages))
        base = manifest['repository'] + '/blob/' + manifest['proof_revision'] + '/'
        for name, loc in links.items():
            assert base + loc in all_html, f'Missing rendered Lean link: {name}'
        svg = ET.parse(web / 'dependency-graph.svg').getroot()
        graph_nodes = [e for e in svg.iter() if e.tag.endswith('}g') and e.attrib.get('class') == 'node']
        assert len(graph_nodes) == len(nodes), 'Rendered graph node count differs'
        for n in graph_nodes:
            anchors = [a for a in n.iter() if a.tag.endswith('}a')]
            assert anchors, 'Unlinked SVG node'
            for a in anchors:
                href = a.attrib.get('{http://www.w3.org/1999/xlink}href', a.attrib.get('href', ''))
                u = urlsplit(href)
                assert not u.scheme, f'Unexpected external statement link: {href}'
                target = web / unquote(u.path)
                assert target.is_file(), f'Missing graph target: {href}'
                if u.fragment:
                    assert re.search(r'(?:id|name)=[\"\']' + re.escape(unquote(u.fragment)) + r'[\"\']', target.read_text()), f'Missing statement anchor: {href}'
    print(json.dumps({'nodes': len(nodes), 'declarations': len(declarations), 'proof_inputs': len(manifest['sha256']), 'rendered': rendered, 'status': 'PASS'}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--rendered', action='store_true')
    check(parser.parse_args().rendered)
