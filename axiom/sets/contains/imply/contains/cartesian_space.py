from util import *
import axiom



@apply
def apply(given, *limits):
    e, S = given.of(Contains)

    shape = []
    for limit in limits:
        x, a, b = limit
        assert a == 0
        assert x.is_integer
        assert e._has(x)
        shape.append(b)
    shape.reverse()
    return Contains(Lamda(e, *limits).simplify(), CartesianSpace(S, *shape))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True, shape=(oo,))
    S = Symbol.S(etype=dtype.integer)
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)

    Eq << apply(Contains(x[i], S), (i, 0, n))

    Eq << Eq[1].simplify()

    Eq << algebra.cond.imply.all.restrict.apply(Eq[0], (i, 0, n))


if __name__ == '__main__':
    run()

