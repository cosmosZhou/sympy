from sympy import *
from axiom.utility import prove, apply
from sympy.matrices.expressions.matexpr import Swap
from axiom import algebra, sets


@apply
def apply(given, m=None, b=None):
    assert given.is_ForAll
    S = given.rhs
    x = given.variable
    
    w, i, j = given.function.lhs.args[1].args
    
    assert w[i, j].is_Swap or w[i, j].definition.is_Swap
    
    if m is None:
        m = Symbol.m(integer=True, nonnegative=True)
        
    if b is None:
        b = Symbol.b(integer=True, shape=(oo,))
        
    return ForAll[x:S](Contains(x @ MatProduct[i:m](w[i, b[i]]), S))


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    m = Symbol.m(integer=True, nonnegative=True, given=False)
    S = Symbol.S(etype=dtype.integer * n, given=True)    
    
    x = Symbol.x(shape=(n,), integer=True)
    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)    
    
    w = Symbol.w(LAMBDA[j, i](Swap(n, i, j)))
    
    given = ForAll[x[:n]:S](Contains(x[:n] @ w[i, j], S))
    
    Eq.w_definition, Eq.swap, Eq.hypothesis = apply(given, m=m)
    
    i, _, m = Eq.hypothesis.function.lhs.args[1].limits[0]
    
    b = Eq.hypothesis.function.lhs.args[1].function.indices[1].base
        
    Eq.induction = Eq.hypothesis.subs(m, m + 1)
    
    Eq << Eq.induction.function.lhs.args[1].this.bisect(Slice[-1:])
    
    Eq << x @ Eq[-1]
    
    Eq << Eq.swap.subs(i, m).subs(j, b[m])
    
    Eq << algebra.forall.imply.ou.subs.apply(Eq[-1], x, Eq[1].rhs.func(*Eq[1].rhs.args[:2]))
    
    Eq << Eq[-1].apply(algebra.cond.imply.forall.restrict, (x, S))
    
    Eq <<= Eq[-1] & Eq.hypothesis
    
    Eq << algebra.forall_et.imply.forall.apply(Eq[-1])
    
    Eq << Eq[-1].subs(Eq[1].reversed)
    
    Eq << Eq.induction.induct()
    
    Eq << algebra.sufficient.imply.cond.induction.apply(Eq[-1], n=m)

    
if __name__ == '__main__':
    prove()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
