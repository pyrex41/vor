#!/usr/bin/env python3
"""Serialize captured raw KL data; name-to-slot decoding happens in Rocq."""
import hashlib
import json
from pathlib import Path
from render_certificates import decode, same, Symbol, nat
RESERVED = ['defun','vor.fol-at','cond','and','cons?','=','cons','hd','tl','>','-','found','missing']

def render(data):
    packet = decode(data)
    if not same(packet[:2], [Symbol('vor-native-lookup'), 0]) or len(packet) != 3:
        raise ValueError('native capture envelope')
    definition = packet[2]
    if not isinstance(definition,list) or len(definition)!=4 or definition[:2] != [Symbol('defun'), Symbol('vor.fol-at')]:
        raise ValueError('native definition identity')
    params = definition[2]
    if not isinstance(params,list) or len(params)!=2 or not all(isinstance(p,Symbol) for p in params):
        raise ValueError('native parameters')
    names = RESERVED + [p.name for p in params]
    if len(set(names))!=len(names): raise ValueError('aliased symbol encoding')
    ids = {name:n for n,name in enumerate(names)}
    def raw(x):
        if isinstance(x,list):
            result='Nil'
            for a in reversed(x): result=f'(Cell {raw(a)} {result})'
            return result
        if isinstance(x,Symbol):
            if x.name not in ids: raise ValueError('unsupported native symbol')
            return f'(Sym {ids[x.name]})'
        if type(x) is bool: return '(Boolean '+str(x).lower()+')'
        if type(x) is int: return '(Num '+nat(x)+')'
        raise ValueError('unsupported native scalar')
    captured=raw(definition)
    digest=hashlib.sha256(captured.encode()).hexdigest()
    lines=['From Coq Require Import List.', 'From VorAudit Require Import NativeLookup.', 'Import ListNotations.',
           f'(* Injectively encoded capture, modulo fresh parameter names: {digest} *)',
           'Definition actual_lookup_kl : datum := '+captured+'.',
           'Lemma actual_lookup_decoded : decode_definition actual_lookup_kl = Some lookup_body.',
           'Proof. vm_compute. reflexivity. Qed.',
           'Theorem actual_lookup_total : forall body xs n,',
           '  decode_definition actual_lookup_kl = Some body ->',
           '  eval body [encode_list xs; Num n] body (lookup_result xs n).',
           'Proof. intros. rewrite actual_lookup_decoded in H. inversion H; subst. apply native_lookup_total. Qed.',
           'Theorem actual_lookup_all_outcomes : forall body xs n v,',
           '  decode_definition actual_lookup_kl = Some body ->',
           '  eval body [encode_list xs; Num n] body v -> v=lookup_result xs n.',
           'Proof. intros. rewrite actual_lookup_decoded in H. inversion H; subst. eapply native_lookup_all_outcomes; eauto. Qed.']
    return '\n'.join(lines)+'\n'
if __name__=='__main__':
    import sys
    Path(sys.argv[2]).write_text(render(Path(sys.argv[1]).read_bytes()))
