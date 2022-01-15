from util import *



@apply(given=None)
def apply(self):
    p, q = self.of(Infer)
    return Equivalent(self, Infer(q.invert(), p.invert()))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Infer(x > y, f(x) > g(y)))

    Eq << Eq[0].this.lhs.apply(algebra.infer.to.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.to.ou)


if __name__ == '__main__':
    run()

#     https://en.wikipedia.org/wiki/Contraposition
# created on 2018-10-09
