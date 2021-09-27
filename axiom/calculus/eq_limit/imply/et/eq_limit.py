from util import *


@apply
def apply(limited_f):
    (fx, (x, x0, dir)), A = limited_f.of(Equal[Limit])
    assert dir == 0

    return Equal(Limit[x:x0:1](fx), A), Equal(Limit[x:x0:-1](fx), A)


@prove
def prove(Eq):
    from axiom import calculus

    x, x0, A = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(Limit[x:x0](f(x)), A))
    Eq << calculus.eq_limit.imply.eq_limit.right.apply(Eq[0])
    Eq << calculus.eq_limit.imply.eq_limit.left.apply(Eq[0])


if __name__ == '__main__':
    run()