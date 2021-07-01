from util import *


@apply
def apply(piecewise, index=None, reverse=False):
    if index is None:
        for index, (expr, cond) in enumerate(piecewise.args):
            if cond.is_Equal:
                break

        if not cond.is_Equal:
            for index, (expr, cond) in enumerate(piecewise.args):
                if cond.is_And:
                    break

    else:
        expr, cond = piecewise.args[index]

    if cond.is_And:
        for eq in cond.args:
            if eq.is_Equal:
                break
    else:
        eq = cond

    lhs, rhs = eq.of(Equal)
    if reverse:
        lhs, rhs = rhs, lhs

    expr = expr._subs(lhs, rhs)
    ec = [*piecewise.args]
    ec[index] = (expr, cond)
    return Equal(piecewise, piecewise.func(*ec))


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,))
    y = Symbol.y(real=True, shape=(k,))
    A = Symbol.A(etype=dtype.real * k)
    g = Function.g(shape=(), real=True)
    f = Function.f(shape=(), real=True)
    h = Function.h(shape=(), real=True)

    Eq << apply(Piecewise((g(x), Equal(x, y) & (h(y) > 0)), (f(x), Contains(y, A)), (h(x), True)))

    p = Symbol.p(Eq[0].lhs)
    Eq << p.this.definition

    Eq << algebra.eq_piecewise.imply.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[2].apply(algebra.et.imply.et.subs, index=2)

    Eq << algebra.ou.imply.eq.apply(Eq[-1], wrt=p)

    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.swap.back)

    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.swap.front)

    Eq << Eq[0].this.rhs.apply(algebra.piecewise.invert)

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq << Eq[-1].this.rhs.subs(Eq[1])


if __name__ == '__main__':
    run()

