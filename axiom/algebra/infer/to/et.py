from util import *



@apply(given=None)
def apply(self):
    p, q = self.of(Infer)

    return Equivalent(self, And(*(Infer(p, eq) for eq in q.of(And))), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    f, g, h = Function(integer=True)
    Eq << apply(Infer(x > y, (f(x) > g(y)) & (h(x) > g(y))))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.infer.imply.et.infer)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.given.et.infer)


if __name__ == '__main__':
    run()
# created on 2019-10-07
