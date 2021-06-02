from util import *
import axiom



@apply
def apply(*given):
    exists, ou = given
    if not exists.is_Exists:
        exists, ou = ou, exists

    fx, *limits_x = exists.of(Exists)
    cond = fx.invert()
    [*eqs] = ou.of(Or)
    for i, eq in enumerate(eqs):
        if eq == cond:
            del eqs[i]
            return Or(*eqs)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    A = Symbol.A(etype=dtype.real)

    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(Exists[x:A](f(x, y) > 0), (g(y, x) > 0) | (f(x, y) <= 0))

    Eq <<= Eq[0] & Eq[1]

    Eq << algebra.et.imply.ou.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.args[0].apply(algebra.cond.any.imply.any_et)

    Eq << algebra.et.imply.cond.apply(Eq[-1], index=0)


if __name__ == '__main__':
    run()

