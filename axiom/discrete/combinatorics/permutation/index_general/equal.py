from axiom.utility import prove, apply
from sympy import *

from axiom import sets, algebre
import axiom


def index_function(n):    
    k = Symbol.k(integer=True)
    
    def index(x, a, *indices):
        (j,), *_ = indices
        return LAMBDA[k:n](KroneckerDelta(x[k], a[j])) @ LAMBDA[k:n](k)

    f = Function.index(nargs=(2,), shape=(), integer=True)
    f.eval = index
    return f


@apply(imply=True)
def apply(*given, j=None):
    a_size, xa_equality = given
    a_set_comprehension_abs, n = axiom.is_Equal(a_size)
    a_set_comprehension = axiom.is_Abs(a_set_comprehension_abs)
    x_set_comprehension, _a_set_comprehension = axiom.is_Equal(xa_equality)
    
    assert a_set_comprehension == _a_set_comprehension

    assert len(x_set_comprehension.limits) == 1
    k, a, b = x_set_comprehension.limits[0]
    assert n == b - a
        
    assert len(a_set_comprehension.limits) == 1
    k, a, b = a_set_comprehension.limits[0]
    assert n == b - a

    x = LAMBDA(x_set_comprehension.function.arg, *x_set_comprehension.limits).simplify()    
    a = LAMBDA(a_set_comprehension.function.arg, *a_set_comprehension.limits).simplify()
    
    if j is None:
        j = Symbol.j(domain=Interval(0, n - 1, integer=True), given=True)
    
    assert j >= 0 and j < n
        
    index = index_function(n)
    index_j = index[j](x[:n], a[:n], evaluate=False)
    return Contains(index_j, Interval(0, n - 1, integer=True)), \
        Equality(x[index_j], a[j])


@prove
def prove(Eq):     
    n = Symbol.n(domain=Interval(2, oo, integer=True), given=True)
    
    x = Symbol.x(shape=(n,), integer=True)
    
    a = Symbol.a(shape=(n,), integer=True)
    
    k = Symbol.k(integer=True)
    
    j = Symbol.j(domain=Interval(0, n - 1, integer=True), given=True)
    
    Eq << apply(Equality(abs(a.set_comprehension(k)), n),
                Equality(x[:n].set_comprehension(k), a.set_comprehension(k)),
                j=j)
    
    Eq << Eq[2].lhs.this.definition
    
    Eq <<= Eq[-3].subs(Eq[-1]), Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1].lhs.indices[0].this.expand()    
    
    Eq << Eq[-1].rhs.function.args[1].this.astype(Piecewise)
    
    Eq << Eq[-2].this.rhs.subs(Eq[-1])
    
    sj = Symbol.s_j(definition=conditionset.conditionset(k, Equal(a[j], x[k]), Interval(0, n - 1, integer=True)))
    
    Eq.sj_definition = sj.this.definition
    
    Eq << Sum[k:sj](k).this.limits[0][1].definition
    
    Eq.crossproduct = algebre.equal.equal.imply.equal.transit.apply(Eq[-2], Eq[-1])
    
    Eq.sj_definition_reversed = Eq.sj_definition.this.rhs.limits[0][1].reversed.reversed

    Eq << Eq[1].apply(sets.equal.imply.equal.intersect, {a[j]})
    
    Eq << Piecewise((x[k].set, Equality(x[k], a[j])), (x[k].emptySet, True)).this.simplify()
    
    Eq << sets.equal.imply.equal.union_comprehension.apply(Eq[-1].reversed, (k, 0, n))
    
    Eq.distribute = Eq[-1].subs(Eq[-3]).reversed
    
    Eq << Eq.distribute.this.lhs.function.subs(Eq.distribute.lhs.limits[0][1].args[1][1])
    
    Eq << Eq[-1].subs(Eq.sj_definition_reversed)
    
    Eq.sj_greater_than_1 = sets.is_nonemptyset.imply.greater_than.apply(Eq[-1])
    
    Eq.distribute = Eq.distribute.subs(Eq.sj_definition_reversed)
    
    Eq << sets.imply.ou.unequal.apply(Eq.sj_greater_than_1.lhs.arg)
    
    Eq.sj_less_than_1, Eq.inequality_ab = Eq[-1].split()
    
    (a, *_), (b, *_) = Eq.inequality_ab.limits
    
    Eq << Eq[1].apply(algebre.equal.imply.equal.abs)
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[-1], Eq[0])
    
    Eq << sets.equal.imply.forall_equal.nonoverlapping.apply(Eq[-1], excludes=Eq.inequality_ab.variables_set)
    
    Eq << Eq[-1].subs(k, a)
    
    Eq << Eq[-1].subs(Eq[-1].variable, b)
    
    Eq <<= Eq.inequality_ab & Eq[-1]
    
    Eq.distribute_ab = Eq[-1].this.function.astype(Or)

    Eq.j_equality = sets.imply.forall.conditionset.apply(sj)
        
    Eq << Eq.j_equality.limits_subs(k, a)
    Eq << Eq.distribute_ab.subs(Eq.j_equality.reversed)
    Eq << Eq.j_equality.limits_subs(a, b)
    
    Eq << Eq[-1].subs(Eq.j_equality)
    
    Eq <<= Eq.sj_less_than_1 & Eq.sj_greater_than_1
    
    Eq << sets.equal.imply.contains.apply(Eq[-1], var=k)
    
    Eq.index_domain = Eq[-1].subs(Eq.crossproduct.reversed)
    
    Eq << Eq.j_equality.subs(Eq.j_equality.variable, Eq.index_domain.lhs).split()
    
    Eq <<= Eq[-2] & Eq.index_domain
    
    Eq << Eq[-1].reversed
    
    Eq << Subset(sj, Eq[2].rhs, plausible=True)
    
    Eq <<= Eq[-1] & Eq.index_domain


if __name__ == '__main__':
    prove(__file__)
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
