from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets
from sympy.concrete.limits import limits_dictionary, limits_update
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


def difference_of_domain_defined(domain_defined, _domain_defined, limitsDict):
    keys = domain_defined.keys()
    diff_set = {}
    for key in keys:
        domain = domain_defined[key]
        _domain = _domain_defined[key]
        domain_limited = limitsDict[key]
        if _domain != domain:
            if domain in _domain:
                if domain_limited != domain:
                    diff_set[key] = domain & domain_limited
                else:
                    diff_set[key] = domain
            
    return diff_set

        
@apply
def apply(self, simplify=True):
    assert self.is_Sum
    args = []
    domain_defined = self.function.domain_defined_for_limits(self.limits)
    
    limitsDict = limits_dictionary(self.limits)
    for arg in axiom.is_Add(self.function):
        arg_domain_defined = arg.domain_defined_for_limits(self.limits)
        diff_set = difference_of_domain_defined(domain_defined, arg_domain_defined, limitsDict)
        if diff_set:
            limits = limits_update(self.limits, diff_set)
        else:
            limits = self.limits
        arg = self.func(arg, *limits)
        
        if simplify:
            arg = arg.simplify()
        args.append(arg)
        
    return Equal(self, Add(*args, evaluate=False))


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True, given=False)
    
    C = Symbol.C(etype=dtype.integer, given=True)
    
    f = Function.f(real=True)
    h = Function.h(real=True)
    x = Symbol.x(shape=(n,), real=True)
    y = Symbol.y(shape=(n, n), real=True)
    
#     Eq << apply(Sum[i:C, j](f(i) + x[i] + h(j) + x[j] + y[i, j]))
    Eq << apply(Sum[i:n](f(i) + h(i)))
    
    Eq << Eq[0].subs(n, 1)
    
    Eq.induct = Eq[0].subs(n, n + 1)
    
    Eq << Eq.induct.this.lhs.apply(algebra.sum.to.add.dissect, {n})
    
    Eq << Eq[-1].this.lhs.apply(algebra.add.flatten)
    
    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add.dissect, {n})
    
    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.to.add.dissect, {n})
    
    Eq << Eq[0].induct(reverse=True)
    
    Eq << algebra.sufficient.imply.eq.induction.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    prove()

from . import push_front, push_back
from . import doit
