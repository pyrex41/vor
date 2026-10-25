#!/usr/bin/env python3
"""Render the exact ps-captured ShenCheck mapper as inert Rocq datum.

The generated term is consumed by a reviewed decoder; this script never
interprets or executes the captured body.
"""
import hashlib
from pathlib import Path
from render_certificates import Symbol, decode, same, nat

def render(path):
    packet = decode(Path(path).read_bytes())
    if not same(packet[:2], [Symbol('vor-shencheck-mapper'), 0]) or len(packet) != 3:
        raise ValueError('mapper capture envelope')
    definition = packet[2]
    if not isinstance(definition, list) or len(definition) != 4 or definition[:2] != [Symbol('defun'), Symbol('shencheck.mapper')]:
        raise ValueError('mapper definition identity')
    params = definition[2]
    if not isinstance(params, list) or len(params) != 1 or not all(isinstance(p, Symbol) for p in params):
        raise ValueError('mapper parameter shape')
    # Keep the same primitive IDs as NativeLookup and freeze every mapper
    # constructor. Only the one fresh source parameter may be additional.
    fixed_names = ['defun', 'shencheck.mapper', 'cond', 'and', 'cons?', '=', 'cons',
             'hd', 'tl', 'effect', 'applied', 'not-applied', 'unknown',
             'possibilities', 'rejected', 'malformed-observation',
             'sc-observation']
    reserved = set(fixed_names)
    if params[0].name in reserved:
        raise ValueError('mapper parameter aliases reserved symbol')
    names = fixed_names + [params[0].name]
    observed = {x.name for x in walk(definition) if isinstance(x, Symbol)}
    allowed = set(names)
    unknown = observed - allowed
    if unknown:
        raise ValueError('unsupported mapper symbol: ' + ','.join(sorted(unknown)))
    if params[0].name not in observed:
        raise ValueError('mapper parameter is missing or aliased')
    ids = {name: n for n, name in enumerate(names)}
    def raw(x):
        if isinstance(x, list):
            out = 'Nil'
            for a in reversed(x): out = f'(Cell {raw(a)} {out})'
            return out
        if isinstance(x, Symbol):
            if x.name not in ids: raise ValueError(f'unsupported symbol {x.name}')
            return f'(Sym {ids[x.name]})'
        if type(x) is bool: return f'(Boolean {str(x).lower()})'
        if type(x) is int: return f'(Num {nat(x)})'
        raise ValueError('unsupported scalar')
    captured = raw(definition)
    digest = hashlib.sha256(captured.encode()).hexdigest()
    return digest, captured

def walk(x):
    yield x
    if isinstance(x, list):
        for y in x:
            yield from walk(y)

if __name__ == '__main__':
    import sys
    digest, captured = render(sys.argv[1])
    output = Path(sys.argv[2])
    old = output.read_text() if output.exists() else ''
    marker = '(* MAPPER_PROOF_BEGIN *)'
    suffix = old[old.index(marker):] if marker in old else ''
    output.write_text(
        'From Coq Require Import List.\n'
        'From VorAudit Require Import NativeLookup.\n'
        'Import ListNotations.\n'
        f'(* Exact ps capture digest: {digest} *)\n'
        'Definition actual_shencheck_mapper_kl : datum := ' + captured + '.\n'
        + (suffix if suffix else ''))
