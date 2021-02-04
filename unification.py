from copy import deepcopy
from itertools import combinations


from structure import *


# finds a mgu for a set of Literals
def unify(m):
    sigma = Subst()
    n = set(deepcopy(m))

    while len(n) > 1:
        nset = set()
        alpha = None
        for l1, l2 in combinations(n, 2):
           alpha = find_ds(l1, l2)
           if bool(alpha):
               for x, t in alpha.subs.items():
                   if x in t.getvars():
                       return None
               break

        if alpha is None:
            return None

        sigma.compose(alpha)

        for L in n:
            nset.add(L.apply(sigma))

        n = deepcopy(nset)
    
    return sigma



def find_ds(l1, l2):
    if l1.label == l2.label and len(l1.childs) == len(l2.childs):
        for t1, t2 in zip(l1.childs, l2.childs):
            alpha = ds(t1, t2)
            
            if bool(alpha):
                return alpha
   
    return None



def ds(t1, t2):
    if isinstance(t1, Var) or isinstance(t2, Var):
        if t1!=t2 and bool(t1) and bool(t2):
            if isinstance(t1, Var):
                return Subst(var=t1, term=t2)
            else:
                return Subst(var=t2, term=t1)
        else:
            return None
    
    if isinstance(t1, Function) and isinstance(t2, Function):
        if t1.label == t2.label and len(t1.childs) == len(t2.childs):
            for pair in zip(t1.childs, t2.childs):
                dset = ds(*pair)

                if bool(dset):
                    return dset
        

    return None
