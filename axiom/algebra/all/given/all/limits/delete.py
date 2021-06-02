from util import *


@apply
def apply(given, index=-1):
    function, *limits = given.of(ForAll)

    assert len(limits) > 1
    del limits[index]

    return ForAll(function, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)

    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    f = Function.f(integer=True)

    Eq << apply(ForAll[x:A, y:B](f(x, y) > 0))

    Eq << ~Eq[0]

    Eq << algebra.all.any.imply.any_et.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()

