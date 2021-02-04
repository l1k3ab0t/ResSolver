import argparse
from itertools import combinations
from copy import deepcopy
import functools
import sys


class Clause:
    def __init__(self, variables):
        self.vars = frozenset(variables)
    
    def __eq__(self, other):
        return self.vars == other.vars
    
    def __str__(self):
        return ", ".join(map(lambda x: "X"+str(x[1])  if x[0] else "!X"+str(x[1]), self.vars))

    def tex(self):
        return ", ".join(map(lambda x: "X_{"+str(x[1])+"}"  if x[0] else "\\neg X_{"+str(x[1])+"}", self.vars))



# (bool, int)
@functools.total_ordering
class Resolution:
    def __init__(self, resolvent : Clause, removed=None , k1=None, k2=None):
      
        self.resolvent = resolvent # resolvent :: Clause
        self.parents = (k1,k2) # k1 :: Resolution
        self.removed = removed

    def proof(self, other):
        resolutions = []
        for v in self.resolvent.vars:
            if (not v[0], v[1]) in other.resolvent.vars:                  
                
                s1 = set(self.resolvent.vars)
                s1.remove(v)
                s2 = set(other.resolvent.vars)
                s2.remove((not v[0], v[1]))
                
                
                resolvent = Clause(s1.union(s2))
                
                if len(resolvent.vars) == 0:
                    resolutions.append((True, Resolution(resolvent, v[1], self, other)))
                
                
                resolutions.append((False,Resolution(resolvent, v[1], self, other)))
        
        return resolutions
    

    def deep_parents(self):
        s = set()

        if not self.parents[0]:
            return {hash(self.resolvent.vars)}

        s.update(*map(lambda x: x.deep_parents(), self.parents))
       
        return s 
    

    def __lt__(self, other):
        return len(self.resolvent.vars) < len(other.resolvent.vars)
    
    
    def __eq__(self, other):
        return self.resolvent == other.resolvent
    

    def __hash__(self):
        return hash(self.resolvent.vars)


    def __str__(self):
        if self.parents[0]:
            return "res:{} \nP1: {} \nP2: {}".format(self.resolvent, self.parents[0], self.parents[1])
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
            if not proof.parents[0] in self.m:
                self.pretty(proof.parents[0])
            if not proof.parents[1] in self.m:
                self.pretty(proof.parents[1])

            res = "{}"
            if len(proof.resolvent.vars) != 0:
                res = proof.resolvent


            p1id = self.m[proof.parents[0]]
            p2id = self.m[proof.parents[1]]
            print("{}.\t{}\t\t\t(res) with X{} from {} and {}".format(self.num, res, proof.removed, p1id, p2id))
            self.m[proof] = self.num
            self.num += 1


    def tex(self, proof):
        print("\\begin{array}{lll}")
        self._tex(proof)
        print("\\end{array}")
    

    def _tex(self, proof):
        if not proof.parents[0]:
            print ("{}. & \\{{ {}\\}}& \\text{{premise}} \\\\".format(self.num, proof.resolvent.tex()))
            self.m[proof] = self.num
            self.num += 1
        else:
            if not proof.parents[0] in self.m:
                self._tex(proof.parents[0])
            if not proof.parents[1] in self.m:
                self._tex(proof.parents[1])

            res = ""
            if len(proof.resolvent.vars) != 0:
                res = proof.resolvent.tex()

            p1id = self.m[proof.parents[0]]
            p2id = self.m[proof.parents[1]]
            print("{}. & \\{{ {}\\}} & \\text{{(res) with $X_{}$ from {} and {} }} \\\\".format(self.num, res, proof.removed, p1id, p2id))
            self.m[proof] = self.num
            self.num += 1


parser = argparse.ArgumentParser(description='PL Solver')
parser.add_argument('file', metavar='f', type=str)

args = parser.parse_args()


clauses = [Clause(map(lambda x: (False, int(x[1:])) if x[0] == "!" else (True, int(x)), l.strip().split(" "))) for l in open(args.file)]      # !3 4 --> not X3 OR X4

resolutions = set(map(Resolution, clauses))
old_resolutions = set()

while resolutions != old_resolutions:
    old_resolutions = deepcopy(resolutions)
    for (r1, r2) in combinations(sorted(old_resolutions), 2):
        par1 = r1.deep_parents()
        par2 = r2.deep_parents()
        
        if  bool(par1.intersection(par2)) and bool(par1) and bool(par2):
            continue
       
        
        for found, res in r1.proof(r2):
            if found:
                pretty = Pretty_Proof()
                pretty.tex(res)
                pretty = Pretty_Proof()
                pretty.pretty(res)
                sys.exit()
            resolutions.add(res)
           
for res in resolutions:
    print(res)
