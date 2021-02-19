from sympy import *
from axiom.utility import prove, apply
from sympy.matrices.expressions.matexpr import Swap
from axiom.discrete.combinatorics.permutation.adjacent import swap2
from axiom import sets, algebre, discrete


@apply
def apply(given):
    assert given.is_ForAll and len(given.limits) == 1
    x, S = given.limits[0]
    
    contains = given.function
    assert contains.is_Contains
    
    w = contains.lhs.args[0].base
    _, j = contains.lhs.args[0].indices
    i = Symbol.i(integer=True)
    
    return ForAll[x:S](Contains(w[i, j] @ x, S))


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    S = Symbol.S(etype=dtype.integer * n)    
    
    x = Symbol.x(**S.element_symbol().type.dict)
    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)    
    
    w = Symbol.w(definition=LAMBDA[j, i](Swap(n, i, j)))
    
    Eq << apply(ForAll[x:S](Contains(w[0, j] @ x, S)))
    
    j_ = j.copy(domain=Interval(0, n - 1, integer=True))
    Eq.given = Eq[1].subs(j, j_)
    
    i_ = i.copy(domain=Interval(0, n - 1, integer=True))
    Eq.given_i = Eq.given.subs(j_, i_)    
    
    Eq << Eq.given.subs(x, Eq.given_i.function.lhs)
    
    Eq << (Eq.given_i & Eq[-1]).split()[-1]
    
    Eq << Eq.given_i.subs(x, Eq[-1].function.lhs)
    
    Eq << (Eq[-2] & Eq[-1]).split()[0]
    
    Eq.final_statement = algebre.condition.imply.forall.minify.apply(Eq[-1], (i_,), (j_,))
    
    Eq << swap2.equal.apply(n, w)
    
    Eq << Eq[-1] @ x
    
    Eq << algebre.condition.imply.forall.minify.apply(Eq[-1], (Eq[-1].limits[0].args[1].args[1].arg,))
    
    Eq.i_complement = Eq.final_statement.subs(Eq[-1])
    
    Eq.plausible = ForAll(Contains(w[i, j] @ x, S), (x, S), (j, Interval(1, n - 1, integer=True)), plausible=True)    
    
    Eq << Eq.plausible.bisect(i.set, wrt=j)
    
    Eq << Eq[-1].split()
    
    Eq << sets.imply.equal.intersection.apply(i, Interval(1, n - 1, integer=True))
    
    Eq << Eq[-2].this.limits[1].subs(Eq[-1])
    
    Eq << Eq[-1].subs(w[i, i].equality_defined())
    
    Eq << discrete.matrix.elementary.swap.transpose.apply(w).subs(j, 0)
    
    Eq.given_i = algebre.condition.imply.forall.minify.apply(Eq.given_i, (i_,))
    
    Eq << Eq.given_i.subs(Eq[-1].reversed)
    
    Eq <<= Eq[-1] & Eq.plausible

    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
