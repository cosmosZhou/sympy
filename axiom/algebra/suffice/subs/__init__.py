from util import *



@apply(given=None)
def apply(given, index=None, reverse=False):
    p, q = given.of(Suffice)
    if index is None:
        if p.is_Equal:
            old, new = p.args
        else:
            eqs = p.of(And)
            for eq in eqs:
                if eq.is_Equal:
                    old, new = eq.args
                    break
    else:
        eqs = p.of(And)
        old, new = axiom.is_Equal(eqs[index])

    if reverse:
        old, new = new, old
    q = q._subs(old, new)
    return Equivalent(given, Suffice(p, q), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    y = Symbol.y(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)

    Eq << apply(Suffice(Equal(f(x), x + 1) & Contains(x, A), Equal(g(f(x)), y)))

    Eq.suffice, Eq.necessary = algebra.equivalent.given.cond.apply(Eq[-1])

    Eq << Eq.suffice.this.lhs.apply(algebra.suffice.imply.suffice.et, index=0)

    Eq << Eq[-1].this.lhs.rhs.apply(algebra.eq.cond.imply.cond.subs)

    Eq << Eq.necessary.this.rhs.apply(algebra.suffice.imply.suffice.et, index=0)

    Eq << Eq[-1].this.rhs.rhs.apply(algebra.eq.cond.imply.cond.subs, reverse=True)


if __name__ == '__main__':
    run()

from . import bool
