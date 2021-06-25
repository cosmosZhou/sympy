from util import *


@apply
def apply(imply, index=-1):
    [*eqs], *limits = imply.of(Any[And])
    cond = eqs[index]
    del eqs[index]

    return And(cond, Any(And(*eqs), *limits))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)

    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Any[x:A]((g(x) > 0) & (f(x) > 0)))

    Eq << Eq[-1].apply(algebra.cond.any.imply.any_et)


if __name__ == '__main__':
    run()

