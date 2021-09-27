from util import *


@apply
def apply(all_x, all_p, equality):

    (x_set_comprehension, e), (x, S) = all_x.of(All[Equal])
    (((__x, (_p, _k)), (k, z, n)), __S), (_x, _S), (p, P) = all_p.of(All[Element[Lamda[Indexed[Indexed]]]])

    assert x_set_comprehension == x.set_comprehension()
    assert S == _S == __S
    assert z == 0
    assert n == x.shape[0]
    assert __x == _x == x
    assert _p == p
    assert _k == k

    if P.is_set:
        P = P.condition_set().condition

    assert p.shape[0] == n

    lhs, rhs = P.args
    assert rhs == Range(0, n)
    assert lhs == p.set_comprehension()

    _e, _n = equality.of(Equal[Card])
    assert _n == n
    assert _e == e

    return Equal(Card(S), factorial(n))


@prove(proved=False)
def prove(Eq):
    from axiom import sets, algebra, discrete

    n = Symbol(domain=Range(2, oo))
    S = Symbol(etype=dtype.integer * n)
    x = Symbol(**S.element_symbol().type.dict)
    i, j, k = Symbol(integer=True)
    e = Symbol(etype=dtype.integer, given=True)
    p = Symbol(shape=(n,), integer=True, nonnegative=True)
    P = Symbol(conditionset(p[:n], Equal(p[:n].set_comprehension(), Range(0, n))))
    Eq << apply(All[x:S](Equal(x.set_comprehension(), e)),
                All[x:S, p[:n]:P](Element(Lamda[k:n](x[p[k]]), S)),
                Equal(Card(e), n))

    Eq << sets.eq.imply.any_eq.condset.all.apply(Eq[2])

    Eq << algebra.all.any.imply.any_all_et.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(algebra.eq.eq.imply.eq.transit)

    a, cond = Eq[-1].limits[0]
    from axiom.discrete.eq.imply.et.index import index_function
    index = index_function(n)
    #p= Lamda[j:n](index[j](x, a))
    #x[index[j](x, a)] = a[j]
    Eq << Any[a:cond](All[p:P](Element(Lamda[k:n](a[p[k]]), S)))

    Eq << Any[a:cond](All[p:P](Equal(p, Lamda[j:n](index[j](Lamda[k:n](a[p[k]]), a)))))

    Eq << Any[a:cond](All[x:S](Element(Lamda[j:n](index[j](x, a)), P)))

    Eq << Any[a:cond](All[x:S](Equal(x, Lamda[k:n](a[Lamda[j:n](index[j](x, a))[k]]))))


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
