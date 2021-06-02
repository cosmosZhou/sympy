from util import *


@apply
def apply(imply):
    from axiom.algebra.ou.imply.any import ou_to_any
    return ou_to_any(imply)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real, given=True)
    B = Symbol.B(etype=dtype.real, given=True)

    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Or(Exists[x:A]((f(x) > 0)), Exists[x:B](f(x) > 0)))

    Eq << ~Eq[0]

    Eq << Eq[-1].apply(algebra.all.all.imply.all.limits_union)

    Eq <<= Eq[1] & Eq[-1]


if __name__ == '__main__':
    run()

