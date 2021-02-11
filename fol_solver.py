import argparse
from itertools import chain, combinations
from copy import deepcopy
import functools
import sys

from parser import *
from structure import *
from unification import *


class Clause:
    def __init__(self, rels):
        self.relations = frozenset(rels)

    def apply(self, subst):
        self.relations = frozenset(rel.apply(subst) for rel in self.relations)

    def getvars(self):
        vs = [*map(lambda x: x.getvars(), self.relations)]
        if len(vs)>0:
            return set.union(*vs)
        return set()

    def difference(self, other):
        unfrozen = set(self.relations)
        self.relations = frozenset(unfrozen.difference(other.relations))

    def union(self, other):
        unfrozen = set(self.relations)
        self.relations = frozenset(unfrozen.union(other.relations))

    def __eq__(self, other):
        return self.getvars() == other.getvars()

    def __str__(self):
        return ", ".join(map(str, self.relations))

    def tex(self):
        return ", ".join(map(lambda x: x.tex(), self.relations))


def powerset(iterable, ml=0):
    s = list(iterable)
    return chain.from_iterable(
    combinations(
        s, r) for r in range(
            ml, len(s) + 1))


def rename(vs, forbidden, start=1):
    renaming = dict()

    i = start
    for v in vs:
        while Var(str(i)) in forbidden:
            i += 1

        renaming[v] = Var(str(i))

    return Subst(subs=renaming)


def check_unifiable(R1, R2):
    if R1[0].neg:
        if not all(r.neg for r in R1) or any(r.neg for r in R2):
            return False
    else:
        if any(r.neg for r in R1) or not all(r.neg for r in R2):
            return False

    return True


# (bool, int)
@functools.total_ordering
class Resolution:
    def __init__(
    self,
    resolvent: Clause,
    p1=None,
    p2=None,
    rels1=None,
    rels2=None,
    subst=None,
     renaming=None):

        self.resolvent = resolvent  # resolvent :: Clause
        self.parents = (p1, p2)  # p1 :: Resolution
        self.rels=(rels1, rels2)
        self.subst = subst
        self.renaming = renaming


    def proof(self, other):
        resolutions = []
        renaming = None
        k1 = None
        k2 = None
        r1 = None
        r2 = None
        p1 = None
        p2 = None

        ps1 = powerset(self.resolvent.relations, ml=1)
        ps2 = powerset(other.resolvent.relations, ml=1)

        for rels1 in ps1:
            for rels2 in ps2:
                if check_unifiable(rels1, rels2):
                        rset = set()

                        if rels1[0].neg:
                            r1 = deepcopy(rels2)
                            r2 = deepcopy(rels1)

                            k2 = deepcopy(self.resolvent)
                            k1 = deepcopy(other.resolvent)
                            p2 = self
                            p1 = other
                        else:
                            r1 = deepcopy(rels1)
                            r2 = deepcopy(rels2)

                            k2 = deepcopy(other.resolvent)
                            k1 = deepcopy(self.resolvent)
                            p1 = self
                            p2 = other

                        k1vars = k1.getvars()
                        k2vars = k2.getvars()

                        wrong = k1vars & k2vars
                        forbidden = k1vars | k2vars

                        renaming = rename(wrong, forbidden)

                        r2neg = set()
                        for ri in r2:
                            ri = deepcopy(ri)
                            ri.neg = False
                            ri.apply(renaming)

                            r2neg.add(ri)

                        mgu = unify(deepcopy(set(r1).union(r2neg)))

                        r1 = Clause(r1)
                        r2 = Clause(r2)

                        r1c = deepcopy(r1)
                        r2c = deepcopy(r2)

                        # print(rels1, rels2, mgu, renaming, k1, k2, r1,r2)
                        if bool(mgu):
                            k1.apply(mgu)
                            r1.apply(mgu)
                            k1.difference(r1)

                            k2.apply(renaming)
                            k2.apply(mgu)
                            r2.apply(renaming)
                            r2.apply(mgu)
                            k2.difference(r2)

                            k1.union(k2)

                            found = False
                            if len(k1.relations) == 0:
                                found = True

                            resolutions.append((found, Resolution(k1, p1=p1, p2=p2, rels1=r1c, rels2=r2c, subst=mgu, renaming=renaming)))

        return resolutions

    
    def dept(self):
        if not self.parents[0]:
            return 0

        return 1 + max(self.parents[0].dept(), self.parents[1].dept())


    def deep_parents(self):
        s = set()

        if not self.parents[0]:
            return {hash(self.resolvent.relations)}

        s.update(*map(lambda x: x.deep_parents(), self.parents))
       
        return s 
    

    def __lt__(self, other):
        return len(self.resolvent.relations) < len(other.resolvent.relations)
    
    
    def __eq__(self, other):
        return self.resolvent == other.resolvent
    

    def __hash__(self):
        return hash(tuple([self.resolvent.relations, self.subst, self.renaming]) + self.parents)


    def __str__(self):
        if self.parents[0]:
            return "res:{} \nP1: {} \nP2: {} \nMit Renaming {} \nund Substitution {}".format(self.resolvent, self.parents[0], self.parents[1], self.renaming, self.subst)
        else:
            return "res:{}".format(self.resolvent)


class Pretty_Proof:
    def __init__(self):
        self.num = 1
        self.m     = dict()
      
    def pretty(self, proof):
        if not proof.parents[0]:
            print("{}.\t{}\t\t\tpremise".format(self.num, proof.resolvent))
            self.m[proof] = self.num
            self.num += 1
        else:
            if not proof.parents[0] in self.m and not proof.parents[1] in self.m:
                if proof.parents[0].dept() >= proof.parents[1].dept():
                    self.pretty(proof.parents[0])
                    self.pretty(proof.parents[1])
                else:
                    self.pretty(proof.parents[1])
                    self.pretty(proof.parents[0])
            else:
                if not proof.parents[0] in self.m:
                    yyself.pretty(proof.parents[0])
                if not proof.parents[1] in self.m:
                    self.pretty(proof.parents[1])

            res = "{}"
            if len(proof.resolvent.relations) != 0:
                res = proof.resolvent


            p1id = self.m[proof.parents[0]]
            p2id = self.m[proof.parents[1]]

            p1str = str(proof.rels[0])
            p2str = str(proof.rels[1])

            print("{}.\t{}\t\t\t(Res) from {} and {} with {{{}}} and {{{}}}, renaming {}, and mgu {}".format(
                                        self.num, res, p1id, p2id, p1str, p2str, proof.renaming, proof.subst))
            self.m[proof] = self.num
            self.num += 1


    def tex(self, proof):
        print("\\begin{array}{lll}")
        self._tex(proof)
        print("\\end{array}")
    

    def _tex(self, proof):
        if not proof.parents[0]:
            print ("\t{}. & \\{{ {}\\}}& \\text{{premise}} \\\\".format(self.num, proof.resolvent.tex()))
            self.m[proof] = self.num
            self.num += 1
        else:
            if not proof.parents[0] in self.m and not proof.parents[1] in self.m:
                if proof.parents[0].dept() >= proof.parents[1].dept():
                    self._tex(proof.parents[0])
                    self._tex(proof.parents[1])
                else:
                    self._tex(proof.parents[1])
                    self._tex(proof.parents[0])
            else:
                if not proof.parents[0] in self.m:
                    yyself._tex(proof.parents[0])
                if not proof.parents[1] in self.m:
                    self._tex(proof.parents[1])
            
            res = ""
            if len(proof.resolvent.relations) != 0:
                res = proof.resolvent.tex()


            p1id = self.m[proof.parents[0]]
            p2id = self.m[proof.parents[1]]

            p1str = proof.rels[0].tex()
            p2str = proof.rels[1].tex()

            print("\t{}. & \\{{ {}\\}} & \\text{{(Res) from {} and {} with $\\{{ {} \\}}$ and $\\{{ {} \\}}$}}\\\\ \n&&\\text{{ renaming ${}$, and mgu ${}$}} \\\\".format(self.num, res, p1id, p2id, p1str, p2str, proof.renaming.tex(), proof.subst.tex()))
            self.m[proof] = self.num
            self.num += 1


parser = argparse.ArgumentParser(description='FOL Solver')
parser.add_argument('file', metavar='f', type=str)
parser.add_argument('--all', action="store_true")

args = parser.parse_args()


clauses = parse(open(args.file).readlines())
printall = args.all

print(clauses)

clauses = map(Clause, clauses)
resolutions = set(map(Resolution, clauses))

old_resolutions = set()

solutions = set()

while resolutions != old_resolutions:
    old_resolutions = deepcopy(resolutions)
    for (r1, r2) in combinations(sorted(old_resolutions), 2):
        par1 = r1.deep_parents()
        par2 = r2.deep_parents()
        
        if  bool(par1.intersection(par2)) and bool(par1) and bool(par2):
            continue
       
        
        for found, res in r1.proof(r2):
            if found and res:
                solutions.add(res)
                if not printall:
                    pretty = Pretty_Proof()
                    pretty.tex(res)
                    pretty = Pretty_Proof()
                    pretty.pretty(res)
                    sys.exit()
                continue
            resolutions.add(res)


if solutions:
    for solution in solutions:
        pretty = Pretty_Proof()
        pretty.tex(solution)
        pretty = Pretty_Proof()
        pretty.pretty(solution)
else:
    for res in resolutions:
        print(res)

