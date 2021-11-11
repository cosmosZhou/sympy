from util import *



@apply(given=None)
def apply(given, index=None, reverse=False):
    p, q = given.of(Infer)
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
    return Equivalent(given, Infer(p, q), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f, g = Function(real=True)

    Eq << apply(Infer(Equal(f(x), x + 1) & Element(x, A), Equal(g(f(x)), y)))

    Eq.suffice, Eq.necessary = algebra.iff.given.et.apply(Eq[-1])

    Eq << Eq.suffice.this.lhs.apply(algebra.infer.imply.infer.et, index=0)

    Eq << Eq[-1].this.lhs.rhs.apply(algebra.eq.cond.imply.cond.subs)

    Eq << Eq.necessary.this.rhs.apply(algebra.infer.imply.infer.et, index=0)

    Eq << Eq[-1].this.rhs.rhs.apply(algebra.eq.cond.imply.cond.subs, reverse=True)


if __name__ == '__main__':
    run()

from . import bool
# created on 2018-02-06
# updated on 2018-02-06
