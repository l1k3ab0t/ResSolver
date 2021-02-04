from abc import ABC
from copy import deepcopy


class Subst:
    def __init__(self, var=None, term=None, subs=None):

        self.subs = dict()

        if subs:
            self.subs = subs

        if var:
            self.subs[var] = term

    def compose(self, other):
        for k, v in self.subs.items():
            self.subs[k] = v.apply(other)
        otherrest = deepcopy(other)
        otherrest.restrictTo(self.subs.keys())
        

        self.subs = self.subs | otherrest.subs


    def restrictTo(self, vs):
        for v in vs:
            if v in self.subs:
                del(self.subs[v])

    def tex(self):
        return "\\{"+ ", ".join(k.tex() +"\\to "+ v.tex() for k,v in self.subs.items()) + " \\}"


    def __str__(self):
        return "{" +",".join(str(k)+"->"+str(v) for k,v in self.subs.items()) + "}"



class Term(ABC):
  
    def apply(self, subst: Subst):
        pass

    def getvars(self):
        pass

    def isvar(self):
        pass

    def tex(self):
        pass



class Relation:
    def __init__(self, label, childs, neg=False):
        self.label = label
        self.childs = childs
        self.neg = neg

    
    def apply(self, subst: Subst):
        self.childs = [*map(lambda x: x.apply(subst), self.childs)]
        return self
    

    def getvars(self):
        return set.union(*map(lambda t: t.getvars(), self.childs))


    def isvar(self):
        return False


    def __eq__(self, other):
        if not isinstance(other, Relation):
            return False
        return self.label == other.label and self.childs == other.childs and self.neg == other.neg


    def __hash__(self):
        return hash((self.neg, self.label) + tuple(hash(c) for c in self.childs))


    def __str__(self):
        s = self.label + "(" + ", ".join(map(lambda x: str(x), self.childs)) + ")"
        if self.neg:
            return "!" + s

        return s

    def __repr__(self):
        return str(self)


    def tex(self):
        s = self.label + "(" + ", ".join(map(lambda x: str(x), self.childs)) + ")"
        if self.neg:
            return "\\neg " + s

        return s



class Function(Term):
    def __init__(self, label, childs):
        self.label = label
        self.childs = childs

    def apply(self, subst: Subst):
        self.childs = [*map(lambda x: x.apply(subst), self.childs)]
        return self


    def getvars(self):
        return set.union(*map(lambda t: t.getvars(), self.childs))


    def isvar(self):
        return False

    def __eq__(self, other):
        if not isinstance(other,Function):
            return False
        return self.label == other.label and self.childs == other.childs
        
    def __hash__(self):
        return hash(tuple(self.label) + tuple(hash(c) for c in self.childs))

    def __repr__(self):
        return str(self)

    def __str__(self):
        return  self.label + "(" + ", ".join(map(lambda x: str(x), self.childs)) + ")"

    def tex(self):
        return  self.label + "(" + ", ".join(map(lambda x: x.tex(), self.childs)) + ")"




class Var(Term):
    def __init__(self, label):
        self.label = label

    #TBD------------------------------------------
    def apply(self, subst: Subst):
        if self in subst.subs:
            return subst.subs[self]
        
        return self

    def getvars(self):
        return {self}

    def isvar(self):
        return False

    def __eq__(self, other):
        if not isinstance(other, Var):
            return False
        return self.label == other.label

    def __hash__(self):
        return hash(self.label)

    def __repr__(self):
        return str(self)

    def __str__(self):
        return "X"+self.label

    def tex(self):
        return "X_{"+str(self.label)+"}"



class Const(Term):
    def __init__(self, label):
        self.label = label
    
    def apply(self, subst: Subst):
        return self

    def getvars(self):
        return set()

    def isvar(self):
        return False

    def __repr__(self):
        return str(self)

    def __str__(self):
        return self.label

    def __hash__(self):
        return hash(self.label)
    
    def __eq__(self, other):
        if not isinstance(other,Const):
            return False
        return self.label == other.label


    def tex(self):
        return self.label





