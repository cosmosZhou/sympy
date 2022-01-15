from util import *



@apply
def apply(given, *limits):
    e, S = given.of(Element)

    shape = []
    for limit in limits:
        x, a, b = limit
        assert a == 0
        assert x.is_integer
        assert e._has(x)
        shape.append(b)
    shape.reverse()
    return Element(Lamda(e, *limits).simplify(), CartesianSpace(S, *shape))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(integer=True, shape=(oo,))
    S = Symbol(etype=dtype.integer)
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    Eq << apply(Element(x[i], S), (i, 0, n))

    Eq << Eq[1].simplify()

    Eq << algebra.cond.imply.all.restrict.apply(Eq[0], (i, 0, n))


if __name__ == '__main__':
    run()

# created on 2021-03-03
