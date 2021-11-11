from util import *
from axiom.discrete.K.to.add.definition import K


@apply
def apply(x, i=None):
    if i is None:
        i = x.generate_var(integer=True, var='i')

    n = x.shape[0]
    return Infer(All[i:1:n](x[i] > 0), Greater(K(x), 0))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(x[:n])

    Eq.initial0 = Eq[0].subs(n, 1)

    Eq << Eq.initial0.this.lhs.defun()

    Eq.initial1 = Eq[-1].subs(n, 2)

    Eq << Eq.initial1.this.find(K).defun()

    Eq.induct = Eq[0].subs(n, n + 2)

    Eq << Eq.induct.this.find(K).defun()

    Eq.hypothesis = Eq[0].subs(n, n + 1)

    Eq << Eq.hypothesis.this.lhs.apply(algebra.all.given.all.limits.relax, Range(1, n + 2))

    Eq << algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.find(And, All).apply(algebra.all.imply.cond.subs, Eq[-1].lhs.variable, n + 1)

    Eq << Eq[-1].this.find(And).apply(algebra.gt_zero.gt_zero.imply.gt_zero)

    Eq << Eq[0].this.lhs.apply(algebra.all.given.all.limits.relax, Range(1, n + 2))

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.find(And).apply(algebra.gt_zero.gt_zero.imply.gt_zero.add)

    Eq << Infer(Eq[0] & Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.cond.cond.infer.imply.cond.induct.apply(Eq.initial0, Eq.initial1, Eq[-1], n=n, start=1)

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[0].subs(n, n + 2)


if __name__ == '__main__':
    run()

# created on 2020-09-15
# updated on 2020-09-15
