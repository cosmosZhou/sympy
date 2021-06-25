from util import *


@apply
def apply(given, m=None, b=None):
    ((x, (w, i, j)), S), (_x, _S) = given.of(All[Contains[MatMul[Indexed]]])
    assert S == _S and x == _x

    assert w[i, j].is_Swap or w[i, j].definition.is_Swap

    if m is None:
        m = Symbol.m(integer=True, nonnegative=True)

    if b is None:
        b = Symbol.b(integer=True, shape=(oo,))

    return All[x:S](Contains(x @ MatProduct[i:m](w[i, b[i]]), S))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(domain=Range(2, oo))
    m = Symbol.m(integer=True, nonnegative=True, given=False)
    S = Symbol.S(etype=dtype.integer * n, given=True)

    x = Symbol.x(shape=(n,), integer=True)

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    w = Symbol.w(Lamda[j, i](Swap(n, i, j)))

    given = All[x[:n]:S](Contains(x[:n] @ w[i, j], S))

    Eq.w_definition, Eq.swap, Eq.hypothesis = apply(given, m=m)

    i, _, m = Eq.hypothesis.function.lhs.args[1].limits[0]

    b = Eq.hypothesis.function.lhs.args[1].function.indices[1].base

    Eq.induct = Eq.hypothesis.subs(m, m + 1)

    Eq << Eq.induct.function.lhs.args[1].this.split(Slice[-1:])

    Eq << x @ Eq[-1]

    Eq << Eq.swap.subs(i, m).subs(j, b[m])

    Eq << algebra.all.imply.ou.subs.apply(Eq[-1], x, Eq[1].rhs.func(*Eq[1].rhs.args[:2]))

    Eq << Eq[-1].apply(algebra.cond.imply.all.restrict, (x, S))

    Eq <<= Eq[-1] & Eq.hypothesis

    Eq << algebra.all_et.imply.all.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[1].reversed)

    Eq << Eq.induct.induct()

    Eq << algebra.suffice.imply.cond.induct.apply(Eq[-1], n=m)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
