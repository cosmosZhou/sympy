from util import *


@apply
def apply(limited_f, limited_g):
    (fx, (x, x0, dir)), A = limited_f.of(Equal[Limit])
    assert dir == 0
    (gx, (_x, _x0, dir)), B = limited_g.of(Equal[Limit])
    assert dir == 0

    assert x == _x
    assert x0 == _x0

    return Equal(Limit[x:x0](fx + gx), A + B)


@prove
def prove(Eq):
    from axiom import sets, calculus

    x, x0, A, B = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Equal(Limit[x:x0](f(x)), A), Equal(Limit[x:x0](g(x)), B))

    Eq << sets.eq.imply.is_real.apply(Eq[0], simplify=None)

    Eq << sets.eq.imply.is_real.apply(Eq[1], simplify=None)

    Eq << calculus.is_limited.is_limited.imply.eq.algebraic_limit_theorem.add.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].subs(Eq[0], Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-05-04
