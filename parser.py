import re
from structure import Var, Const, Function, Relation


def parse_terms(s):
    if len(s) == 1:
        return [Var(s[0])] if s[0].isdigit() else [Const(s[0])]


    terms = []


    while len(s)>0:
        #print("parsing", s)
        fst = s[0]

        if fst == ")":
            return terms, s[1:]
        elif fst.isdigit():
            terms.append(Var(fst))
            s = s[1:]
        elif fst.isalpha() and len(s)>1 and  s[1] == "(":
            inner, s = parse_terms(s[2:])

            #print("inner", fst, inner, s)
            terms.append(Function(fst, inner))
        else:
            terms.append(Const(fst))
            s = s[1:]

    return terms




def parse_line(l):
    terms = re.findall("!?[A-Z][^A-Z^!]*", l)

    terms = map(lambda s: re.findall("!|\d+|[A-Z][a-z]*|[a-z]+|[()]", s), terms)

    parsed = []

    for t in terms:
        if t[0] == "!":
            parsed.append(Relation(t[1], parse_terms(t[3:-1]), neg=True))
        else:
            parsed.append(Relation(t[0], parse_terms(t[2:-1])))

    return parsed

def parse(lines):
    return [*map(parse_line, lines)]

