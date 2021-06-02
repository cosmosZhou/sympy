from util import *


@apply
def apply(given, simplify=True):
    et, *limits = given.of(ForAll[And])
    eqs = []
    for eq in et:
        forall = ForAll(eq, *limits)
        if simplify:
            forall = forall.simplify()
        eqs.append(forall)
    return And(*eqs)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)

    A = Symbol.A(etype=dtype.real * k)
    y = Symbol.y(real=True, shape=(k,), given=True)

    f = Function.f(real=True)
    g = Function.g(real=True)
    b = Symbol.b(shape=(k,), real=True)

    Eq << apply(ForAll[x:A](And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b))))

    Eq << algebra.et.imply.conds.apply(Eq[1])

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq << algebra.all_et.given.all.apply(Eq[0])

    Eq << algebra.all_et.given.all.apply(Eq[-1])


if __name__ == '__main__':
    run()

