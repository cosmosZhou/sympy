from util import *


@apply
def apply(is_nonzero, equality, simplify=True):
    if is_nonzero.is_Equal:
        equality, is_nonzero = is_nonzero, equality

    x = is_nonzero.of(Unequal[0])
    lhs, rhs = equality.of(Equal)
    if simplify:
        if lhs.is_Add:
            lhs = Add(*(a / x for a in lhs.args))
        else:
            lhs /= x

        if rhs.is_Add:
            rhs = Add(*(a / x for a in rhs.args))
        else:
            rhs /= x
    else:
        lhs, rhs = lhs / x, rhs / x
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    f, g, h = Function(real=True)
    Eq << apply(Unequal(f(x), 0), Equal(g(x) * f(x), h(x) * f(x) + x))

    Eq << Eq[1] / f(x)

    Eq << algebra.cond.ou.imply.cond.apply(Eq[0], Eq[-1])

    Eq << Eq[2].this.rhs.ratsimp()


if __name__ == '__main__':
    run()

# created on 2018-01-24
