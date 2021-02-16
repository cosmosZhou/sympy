
from axiom.utility import prove, apply

from sympy import *
from sympy.sets.conditionset import conditionset
from axiom import sets, algebre


@apply(given=True)
def apply(imply):
    assert imply.function.is_And
    
    limits_dict = imply.limits_dict
    for i, eq in enumerate(imply.function.args):
        if eq.is_Equality:
            if eq.lhs in limits_dict:
                old, new = eq.args
            elif eq.rhs in limits_dict:
                new, old = eq.args
            else:
                continue
            
            limits = imply.limits_delete(old)
            if any(limit._has(old) for limit in limits):
                continue
            
            eqs = [*imply.function.args] 
            del eqs[i]
            eqs = [eq._subs(old, new) for eq in eqs]
            
            domain = limits_dict[old]
            if isinstance(domain, list):
                limit = (old,)
            else:
                limit = (old, domain)
            eq = imply.func(eq, limit).simplify()                    
            eqs.append(eq)
             
            return Exists(And(*eqs), *limits)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)    
    
    i = Symbol.i(integer=True)
    k = Symbol.k(integer=True)
    j = Symbol.j(domain=Interval(0, k - 1, integer=True))
    
    x = Symbol.x(real=True, shape=(oo,))
    
    f = Function.f(nargs=(n,), shape=(), integer=True)
    f_quote = Function("f'", shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    h = Function.h(shape=(), integer=True)

    Eq << apply(Exists[x[:n]:f(x[:n]) > 0, i:k]((g(i) > f_quote(j, x[:n])) & Equal(i, j)))

    Eq << Eq[-1].this.function.apply(algebre.condition.imply.exists_et, wrt=j)
    
    Eq << Eq[-1].this.function.apply(algebre.equal.condition.imply.et, delta=False, simplify=None)
    
    Eq << Eq[0].this.function.apply(algebre.et.given.et.where.equal, delta=False, simplify=None, split=False)
    
    


if __name__ == '__main__':
    prove(__file__)

