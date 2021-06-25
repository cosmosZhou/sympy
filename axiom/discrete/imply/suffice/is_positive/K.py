from util import *
from axiom.discrete.K.to.add.definition import K


@apply
def apply(x, i=None):
    if i is None:
        i = x.generate_var(integer=True, var='i')

    n = x.shape[0]
    return Suffice(All[i:1:n](x[i] > 0), Greater(K(x), 0))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True, given=False)

    Eq << apply(x[:n])

    Eq.initial0 = Eq[-1].subs(n, 1)

    Eq << Eq.initial0.this.lhs.defun()

    Eq.initial1 = Eq[-1].subs(n, 2)

    Eq << Eq.initial1.this.find(K).defun()

    Eq.induct = Eq[0].subs(n, n + 2)

    Eq << Eq.induct.this.find(K).defun()

    Eq.hypothesis = Eq[0].subs(n, n + 1)

    Eq << Eq.hypothesis.this.lhs.apply(algebra.all.given.all.limits.relaxed, Range(1, n + 2))

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << Eq[-1].this.find(And, All).apply(algebra.all.imply.cond.subs, Eq[-1].lhs.variable, n + 1)

    Eq << Eq[-1].this.find(And).apply(algebra.is_positive.is_positive.imply.is_positive)

    Eq << Eq[0].this.lhs.apply(algebra.all.given.all.limits.relaxed, Range(1, n + 2))

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.find(And).apply(algebra.is_positive.is_positive.imply.is_positive.add)

    Eq << Eq.induct.induct()

    Eq << algebra.cond.cond.suffice.imply.cond.induct.apply(Eq.initial0, Eq.initial1, Eq[-1], n=n, start=1)

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[0].subs(n, n + 2)


if __name__ == '__main__':
    run()

