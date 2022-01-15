from util import *


@apply
def apply(limited_f, limited_g):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    fx, (x, x0, dir) = of_limited(limited_f, real=True)

    gx, (_x, _x0, _dir) = of_limited(limited_g, real=True)
    assert dir == _dir

    assert x == _x
    assert x0 == _x0

    return Equal(Limit[x:x0:dir](fx * gx), limited_f.lhs * limited_g.lhs)


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    dir = S.One
    Eq << apply(Element(Limit[x:x0:dir](f(x)), Reals), Element(Limit[x:x0:dir](g(x)), Reals))

    is_zero = And(Equal(Eq[0].lhs, 0), Eq[1])
    Eq << Infer(is_zero, is_zero, plausible=True)

    Eq.is_zero = Eq[-1].this.rhs.apply(calculus.is_zero.is_limited.imply.eq.algebraic_limit_theorem.mul)

    Eq << Eq[-1].this.rhs.args[1].apply(sets.el.imply.any_eq, var='B', simplify=None)

    Eq << Eq[-1].this.rhs.apply(algebra.cond.any.imply.any_et, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.eq.eq.imply.eq.mul)

    Eq << algebra.infer.infer.imply.infer.et.apply(Eq.is_zero, Eq[-1])

    Eq.mul_is_zero = Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.transit, reverse=True)

    is_nonzero = And(Element(Eq[0].lhs, Reals - {0}), Eq[1])
    Eq << Infer(is_nonzero, is_nonzero, plausible=True)

    Eq << Eq[-1].this.rhs.apply(calculus.is_limited.is_limited.imply.eq.algebraic_limit_theorem.mul.nonzero)

    Eq << algebra.infer.infer.imply.infer.ou.apply(Eq.mul_is_zero, Eq[-1])

    Eq << Eq[-1].this.lhs.args[0].args[0].apply(sets.eq.given.el)

    Eq <<= Eq[0] & Eq[1]

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties

from . import nonzero
from . import st
# created on 2020-04-17
