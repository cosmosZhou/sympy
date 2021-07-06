from util import *
from axiom.discrete.K.to.add.definition import K


@apply
def apply(x, n):
    return All[x[:n]:CartesianSpace(Range(1, oo), n)](Greater(K(x[:n]), 0))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol.x(integer=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True, given=False)
    Eq << apply(x, n)

    Eq.initial0 = Eq[-1].subs(n, 1)

    Eq << Eq.initial0.this.function.lhs.defun()

    Eq.initial1 = Eq[-1].subs(n, 2)

    Eq << Eq.initial1.this.function.lhs.defun()

    Eq << algebra.all.given.all.limits.split.apply(Eq[-1], index=1)

    Eq << algebra.all.given.ou.apply(Eq[-1])

    Eq.induct = Eq[0].subs(n, n + 2)

    Eq << Eq.induct.this.function.lhs.defun()

    Eq << Eq[0].this.function.apply(algebra.cond.imply.all.restrict, (x[n:n + 2], CartesianSpace(Range(1, oo), 2)), simplify=None)

    Eq.is_positive = algebra.all.imply.all.limits.merge.apply(Eq[-1])

    Eq.hypothesis = Eq[0].subs(n, n + 1)

    Eq << Eq.hypothesis.this.function.apply(algebra.cond.imply.all.restrict, (x[n + 1], 1, oo), simplify=None)

    Eq << algebra.all.imply.all_et.apply(Eq[-1], index=0, simplify=None)

    Eq << algebra.all.imply.all.limits.merge.apply(Eq[-1])

    Eq << Eq[-1].this.function.args[1].apply(sets.contains.imply.ge.split.range)

    Eq << Eq[-1].this.function.args[1].apply(algebra.ge.imply.gt.relax, 0)

    Eq << Eq[-1].this.function.apply(algebra.is_positive.is_positive.imply.is_positive)

    Eq <<= Eq.is_positive & Eq[-1]

    Eq << Eq[-1].this.function.apply(algebra.is_positive.is_positive.imply.is_positive.add)

    Eq << Suffice(Eq[0] & Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.cond.cond.suffice.imply.cond.induct.apply(Eq.initial0, Eq.initial1, Eq[-1], n=n, start=1)

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[0].subs(n, n + 2)


if __name__ == '__main__':
    run()

