from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom


def dissect(self, indices, wrt=None, simplify=True, evaluate=False):    
    if len(self.limits) > 1:
        if wrt is None:
            x, *ab = self.limits[-1]
            if len(ab) == 2: 
                a, b = ab   
                universe = Interval(a, b, right_open=x.is_integer, integer=x.is_integer)
                if x.is_integer:
                    if isinstance(indices, slice): 
                        mid = Symbol.process_slice(indices, a, b)
                        assert mid >= a, "mid >= a => %s" % (mid >= a)        
                        assert mid <= b, "mid <= b => %s" % (mid <= b)
                        
                        if mid is None:
                            return self
                        if isinstance(mid, tuple):
                            ...
                            assert False                        
                        return self.func.operator(self.func(self.function, *self.limits[:-1], (x, a, mid - 1)).simplify(), self.func(self.function, *self.limits[:-1], (x, mid, b)).simplify(), evaluate=evaluate)
                    elif isinstance(indices, (set, Set)): 
                        intersection = universe & indices
                        if intersection: 
                            return self.func.operator(self.func(self.function, *self.limits[:-1], (x, intersection)).simplify(),
                                                      self.func(self.function, *self.limits[:-1], (x, universe // indices)).simplify(), evaluate=evaluate)
                
            return self
        
        for i, limit in enumerate(self.limits):
            x, *ab = limit 
            if x != wrt:
                continue
            if len(ab) == 2:
                universe = Interval(*ab, right_open=True, integer=x.is_integer)
            else:
                universe, *_ = ab
                
            limits1 = [*self.limits]
            limits1[i] = (x, universe & indices)
            
            limits2 = [*self.limits]
            limits2[i] = (x, universe // indices)

            return self.func.operator(self.func(self.function, *limits1).simplify(), self.func(self.function, *limits2), evaluate=evaluate)
        return self

    (x, *ab), *_ = self.limits
    if x.is_Slice:
        x, z = x.bisect(indices, allow_empty=True).args
        if not ab:
            return self.func(self.func(self.function, (x,)).simplify(), (z,))

    if not isinstance(indices, slice): 
        if len(ab) == 1:
            universe = ab[0]
            if universe.is_boolean:
                universe = x.domain_conditioned(universe)
        elif len(ab) == 2:
            a, b = ab
            if b.is_set:
                universe = conditionset(x, a, b)
            else:
                universe = Interval(*ab, right_open=x.is_integer, integer=x.is_integer)
        else:
            universe = x.domain
            
        if not isinstance(indices, set) and indices.is_boolean:
            indices = x.domain_conditioned(indices)
        intersection = universe & indices
        if intersection:
            first = self.func(self.function, (x, intersection))
            second = self.func(self.function, (x, universe // indices))
            
            if simplify:
                first = first.simplify()
                second = second.simplify()
            return self.func.operator(first, second, evaluate=evaluate)
        return self

    if len(ab) == 2:
        a, b = ab
        if x.is_integer:
            mid = Symbol.process_slice(indices, a, b)
            assert mid >= a, "mid >= a => %s" % (mid >= a)        
            assert mid <= b, "mid <= b => %s" % (mid <= b)

            if mid is None:
                return self
            if isinstance(mid, tuple):
                ...
                assert False                        
                
            lhs = self.func(self.function, (x, a, mid))                
            rhs = self.func(self.function, (x, mid, b))
            return self.func.operator(lhs.simplify(), rhs.simplify(), evaluate=evaluate)

    return self


@apply
def apply(self, indices, wrt=None, evaluate=False):
    assert self.is_Sum
    return Equal(self, dissect(self, indices, wrt=wrt), evaluate=evaluate)

 
@prove
def prove(Eq): 
    x = Symbol.x(integer=True)
    f = Function.f(real=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Sum[x:A](f(x)), B)
    
    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.bool)
    
    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.bool)
    
    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.bool)
    
    Eq << Eq[-1].this.rhs.apply(algebra.add.to.sum)
    
    Eq << Eq[-1].this.rhs.function.apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Contains).apply(sets.contains.to.ou.dissect, B)
    
    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.add)


if __name__ == '__main__':
    prove()

