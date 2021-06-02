from util import *



@apply
def apply(n):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    return Equal(Lamda[j:n, i:n](Piecewise((i, j > i), (j, j < i), (0, True))),
                    (1 - Identity(n)) * Lamda[j:n, i:n](Min(i, j)))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)

    i = Symbol.i(domain=Range(0, n))
    j = Symbol.j(domain=Range(0, n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], (i, j))

    Eq << Eq[-1].this.find(Min).astype(Piecewise)

    Eq << Eq[-1].this.rhs.apply(algebra.mul_piecewise.to.piecewise)

    Eq << Eq[-1].this.rhs.simplify(wrt=i)

    Eq << Eq[-1].this.find(LessEqual).reversed

    Eq << Eq[-1].this.find(KroneckerDelta).astype(Piecewise)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(algebra.mul_piecewise.to.piecewise, simplify=None)

    Eq << Eq[-1].this.find(Add[Piecewise]).astype(Piecewise, simplify=False)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(algebra.mul_piecewise.to.piecewise, simplify=False)

    Eq << Eq[-1].this.rhs.apply(algebra.piecewise.flatten, index=0)

    Eq << Eq[-1].this.rhs.apply(algebra.piecewise.swap.front)

    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.swap.back)

    Eq << Eq[-1].this.lhs.apply(algebra.piecewise.invert, index=0)

    Eq << Eq[-1].this.lhs.find(Equal).reversed


if __name__ == '__main__':
    run()
