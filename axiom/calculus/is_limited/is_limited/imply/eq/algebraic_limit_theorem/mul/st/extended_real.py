from util import *


@apply
def apply(limited_f, limited_g):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    fx, (x, x0, dir) = of_limited(limited_f, extended_real=True)

    gx, (_x, _x0, _dir) = of_limited(limited_g, extended_real=True)
    assert dir == _dir

    assert x == _x
    assert x0 == _x0

    return Equal(Limit[x:x0:dir](fx * gx), limited_f.lhs * limited_g.lhs)


@prove(proved=False)
def prove(Eq):
    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    dir = S.One
    Eq << apply(Element(Limit[x:x0:dir](f(x)), ExtendedReals), Element(Limit[x:x0:dir](g(x)), ExtendedReals - {0}))

    Eq << Reals - {0}

    Eq << ExtendedReals - {0}


if __name__ == '__main__':
    run()
# created on 2021-08-14
# updated on 2021-08-14
