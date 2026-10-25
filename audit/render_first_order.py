#!/usr/bin/env python3
"""Raw quoted data only. Rocq, not Python, parses formulas/signatures/proofs."""
from pathlib import Path
from render_certificates import Symbol, decode, same, nat
RESERVED = ['vor.tree','vor.leaf','vor.node','fol-signature','v','app','top','bottom',
            'pred','equal','and','or','imp','forall','exists','hyp','pair','fst','snd','intro',
            'apply','inl','inr','cases','exfalso','gen','inst','witness','unpack','refl','sym',
            'trans','subst','tree-induct']

def render(data):
    packet=decode(data)
    if not same(packet[:2],[Symbol('vor-first-order-audit'),0]) or len(packet)!=4:
        raise ValueError('first-order envelope')
    symbols=set(RESERVED); texts=set(); numbers=set()
    def inspect(q):
        if not isinstance(q,list) or not q: raise ValueError('unquoted datum')
        if q==[Symbol('nil')]: return
        if len(q)==2 and q[0]==Symbol('boolean') and type(q[1]) is bool: return
        if len(q)==2 and q[0]==Symbol('natural'): nat(q[1]); return
        if len(q)==2 and q[0] in [Symbol('symbol'),Symbol('text'),Symbol('bad-number')]:
            if type(q[1]) is not str: raise ValueError('nontext atom')
            {Symbol('symbol'):symbols,Symbol('text'):texts,Symbol('bad-number'):numbers}[q[0]].add(q[1]); return
        if len(q)==3 and q[0]==Symbol('cell'): inspect(q[1]); inspect(q[2]); return
        raise ValueError('unsupported quoted datum')
    inspect(packet[2])
    for record in packet[3]:
        if len(record)!=6 or record[0]!=Symbol('case'): raise ValueError('case shape')
        for q in record[1:5]: inspect(q)
        for budget,accepted in record[5]:
            nat(budget)
            if type(accepted) is not bool: raise ValueError('nonnative result flag')
    symbol_ids={name:n for n,name in enumerate(RESERVED + sorted(symbols-set(RESERVED)))}
    text_ids={name:n for n,name in enumerate(sorted(texts))}
    number_ids={name:n for n,name in enumerate(sorted(numbers))}
    def raw(q):
        if q==[Symbol('nil')]: return 'NV.Nil'
        if q[0]==Symbol('cell'): return f'(NV.Cell {raw(q[1])} {raw(q[2])})'
        if q[0]==Symbol('boolean'): return f'(NV.Boolean {str(q[1]).lower()})'
        if q[0]==Symbol('natural'): return f'(NV.Num {nat(q[1])})'
        if q[0]==Symbol('symbol'): return f'(NV.Sym {symbol_ids[q[1]]})'
        if q[0]==Symbol('text'): return f'(NV.Text {text_ids[q[1]]})'
        if q[0]==Symbol('bad-number'): return f'(NV.BadNumber {number_ids[q[1]]})'
        raise ValueError('invalid quoted datum')
    lines=['From Coq Require Import List.', 'From VorAudit Require Import FirstOrderEncoding.',
           'Import ListNotations.', 'Module NV := NativeLookup.',
           'Definition actual_signature : NV.datum := '+raw(packet[2])+'.']
    comparisons=positive=0
    for n,record in enumerate(packet[3]):
        for role,q in zip(['vars','context','target','proof'],record[1:5]):
            lines.append(f'Definition case_{n}_{role} : NV.datum := {raw(q)}.')
        for budget,accepted in record[5]:
            lines.extend([f'Example case_{n}_budget_{budget} : raw_check actual_signature case_{n}_vars case_{n}_context case_{n}_target case_{n}_proof {budget} = {str(accepted).lower()}.',
                          'Proof. vm_compute. reflexivity. Qed.'])
            comparisons+=1; positive+=accepted
    if not comparisons or not positive: raise ValueError('empty/vacuous corpus')
    lines.append(f'(* {comparisons} actual Shen/model acceptance comparisons, {positive} accepted. Nonacceptance includes rejection and unknown. *)')
    return '\n'.join(lines)+'\n',comparisons,positive
if __name__=='__main__':
    import sys
    text,n,p=render(Path(sys.argv[1]).read_bytes()); Path(sys.argv[2]).write_text(text)
    print(f'First-order: {n} raw Shen/model comparisons ({p} accepted).')
