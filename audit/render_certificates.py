#!/usr/bin/env python3
"""Reify *symbolic bodies/code*, not sampled inputs, into kernel-checked lemmas.
This serializer is an explicit, source-locked bridge assumption, not a theorem.
"""
from dataclasses import dataclass
from pathlib import Path
import hashlib

@dataclass(frozen=True)
class Symbol:
    name: str


def decode(data):
    at = 0
    def read(depth=0):
        nonlocal at
        if depth > 256 or at >= len(data): raise ValueError("truncated/deep data")
        tag = data[at]; at += 1
        if tag == 0: return []
        if tag == 1: return False
        if tag == 2: return True
        if at + 2 > len(data): raise ValueError("truncated length")
        n = int.from_bytes(data[at:at+2], "big"); at += 2
        if tag == 3: return n
        if tag in (4, 5):
            if at + n > len(data): raise ValueError("truncated text")
            s = data[at:at+n].decode("ascii"); at += n
            return Symbol(s) if tag == 4 else s
        if tag == 6 and n: return [read(depth+1) for _ in range(n)]
        raise ValueError("invalid tag")
    value = read()
    if at != len(data): raise ValueError("trailing bytes")
    return value


def same(a, b):
    if type(a) is not type(b): return False
    if isinstance(a, list): return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    return a == b


def nat(x):
    if type(x) is not int or not 0 <= x <= 65535: raise ValueError("invalid natural index/arity")
    return str(x)


def render(data):
    packet = decode(data)
    if not same(packet[:2], [Symbol("vor-audit-fixtures"), 0]): raise ValueError("fixture identity")
    program, artifact = packet[2:]
    if not same(artifact[:3], [Symbol("vor-compiled"), 0, program]): raise ValueError("program substitution")
    if not same(program[:2], [Symbol("vor-program"), 0]): raise ValueError("program version")
    atoms = set()
    def scalar_key(x):
        if isinstance(x, Symbol): return ("symbol", x.name)
        if isinstance(x, bool): return ("bool", str(x))
        if isinstance(x, int): return ("number", str(x))
        if isinstance(x, str): return ("string", x)
        raise ValueError("not scalar")
    def collect(x):
        if isinstance(x, list):
            for v in x: collect(v)
        else: atoms.add(scalar_key(x))
    collect(packet)
    ids = {atom: n for n, atom in enumerate(sorted(atoms))}
    def ident(x): return str(ids[scalar_key(x)])
    def value(x):
        if isinstance(x, list):
            out = "Nil"
            for v in reversed(x): out = f"(Cons {value(v)} {out})"
            return out
        return f"(Atom {ident(x)})"
    def expr(x):
        if len(x) == 2 and x[0] == Symbol("literal"): return f"(Literal {value(x[1])})"
        if len(x) == 2 and x[0] == Symbol("local"): return f"(Local {nat(x[1])})"
        if len(x) == 3 and x[:2] == [Symbol("primitive"), Symbol("cons")] and len(x[2]) == 2:
            return f"(MakeCons {expr(x[2][0])} {expr(x[2][1])})"
        if len(x) == 3 and x[0] == Symbol("bind"): return f"(LetIn {expr(x[1])} {expr(x[2])})"
        if len(x) == 3 and x[0] == Symbol("invoke"):
            args = "NoArgs"
            for e in reversed(x[2]): args = f"(Arg {expr(e)} {args})"
            return f"(Invoke {ident(x[1])} {args})"
        raise ValueError("unsupported expression")
    def instruction(x):
        if len(x) == 2 and x[0] == Symbol("push"): return f"(Push {value(x[1])})"
        if len(x) == 2 and x[0] == Symbol("get"): return f"(Get {nat(x[1])})"
        if x == [Symbol("join")]: return "Join"
        if x == [Symbol("enter")]: return "Enter"
        if x == [Symbol("leave")]: return "Leave"
        if len(x) == 3 and x[0] == Symbol("call"): return f"(Call {ident(x[1])} {nat(x[2])})"
        raise ValueError("invalid instruction")
    lines = ["From Coq Require Import List.",
             "From VorAudit Require Import Compiler Validation.",
             "Import ListNotations.",
             f"(* Exact fixture bytes SHA-256: {hashlib.sha256(data).hexdigest()} *)",
             "(* Distinct scalar classes/names map injectively to opaque atoms. *)"]
    count = 0
    if len(program[3]) != len(artifact[3]): raise ValueError("definition omission")
    for fno, (source, compiled) in enumerate(zip(program[3], artifact[3])):
        if not same(source[:3], compiled[:3]) or source[0] != Symbol("function"):
            raise ValueError("function identity")
        if len(source[3]) != len(compiled[3]): raise ValueError("clause omission")
        for cno, (s, c) in enumerate(zip(source[3], compiled[3])):
            if not same(s[:3], c[:3]) or s[0] != Symbol("clause") or not same(s[2], [Symbol("literal"), True]):
                raise ValueError("clause/guard identity")
            name = f"body_{fno}_{cno}"
            body, code = expr(s[3]), "[" + "; ".join(map(instruction, c[3])) + "]"
            lines.extend([
                f"Definition {name} : expr := {body}.", f"Definition {name}_code : list instruction := {code}.",
                f"Lemma {name}_certificate : validate {name} {name}_code = Some [].",
                "Proof. vm_compute. reflexivity. Qed.",
                f"Theorem {name}_preserves : forall call env v, evaluates call env {name} v ->",
                f"  run call {name}_code (env, [], []) = Some (env, [v], []).",
                f"Proof. intros. eapply checked_compilation_preserves; [exact {name}_certificate | eassumption]. Qed."])
            count += 1
    if count == 0: raise ValueError("empty certificate corpus")
    lines.append(f"(* {count} symbolic-body certificates; each theorem quantifies over all environments and call interpretations. *)")
    return "\n".join(lines) + "\n", count

if __name__ == "__main__":
    import sys
    text, count = render(Path(sys.argv[1]).read_bytes())
    Path(sys.argv[2]).write_text(text)
    print(f"{count} symbolic-body preservation certificates generated")
