from util import *



def index_function(n):
    k = Symbol.k(integer=True)

    def index(x, a, *indices):
        (j,), *_ = indices
        return Lamda[k:n](KroneckerDelta(x[k], a[j])) @ Lamda[k:n](k)

    f = Function.index(nargs=(2,), shape=(), integer=True)
    f.eval = index
    return f


@apply
def apply(*given):
    all_x, all_p, equality = given
    assert all_x.is_ForAll and all_p.is_ForAll

    assert len(all_x.limits) == 1
    x, S = all_x.limits[0]

    assert all_x.function.is_Equal
    x_set_comprehension, e = all_x.function.args
    assert x_set_comprehension == x.set_comprehension()

    assert len(all_p.limits) == 2
    (_x, _S), (p, P) = all_p.limits
    assert x == _x and S == _S
    assert all_p.function.is_Contains

    lamda, _S = all_p.function.args
    assert S == _S
    assert lamda.is_Lamda

    n = x.shape[0]
    k = lamda.variable
    assert lamda == Lamda[k:n](x[p[k]])

    if P.is_set:
        P = P.condition_set().condition

    assert p.shape[0] == n

    lhs, rhs = P.args
    assert rhs == Range(0, n)
    assert lhs == p.set_comprehension()

    assert equality.is_Equal

    assert equality.rhs == n
    assert equality.lhs.is_Abs
    assert equality.lhs.arg == e

    return Equal(abs(S), factorial(n))


@prove(surmountable=False)
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(domain=Range(2, oo))
    S = Symbol.S(etype=dtype.integer * n)

    x = Symbol.x(**S.element_symbol().type.dict)

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    k = Symbol.k(integer=True)

    e = Symbol.e(etype=dtype.integer, given=True)

    p = Symbol.p(shape=(n,), integer=True, nonnegative=True)

    P = Symbol.P(conditionset(p[:n], Equal(p[:n].set_comprehension(), Range(0, n))))

    Eq << apply(ForAll[x:S](Equal(x.set_comprehension(), e)),
                ForAll[x:S, p[:n]:P](Contains(Lamda[k:n](x[p[k]]), S)),
                Equal(abs(e), n))

    Eq << sets.eq.imply.any_eq.apply(Eq[3])

    Eq << algebra.all.any.imply.any_all_et.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.function.function.apply(algebra.eq.eq.imply.eq.transit)

    a, cond = Eq[-1].limits[0]
    index = index_function(n)

#     p= Lamda[j:n](index[j](x, a))

#     x[index[j](x, a)] = a[j]
    Eq << Exists[a:cond](ForAll[p:P](Contains(Lamda[k:n](a[p[k]]),
                                              S)))

    Eq << Exists[a:cond](ForAll[p:P](Equal(p, Lamda[j:n](index[j](Lamda[k:n](a[p[k]]),
                                                                      a)))))

    Eq << Exists[a:cond](ForAll[x:S](Contains(Lamda[j:n](index[j](x,
                                                                   a)), P)))

    Eq << Exists[a:cond](ForAll[x:S](Equal(x,
                                              Lamda[k:n](a[Lamda[j:n](index[j](x, a))[k]]))))


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
