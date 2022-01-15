from util import *


@apply(given=None)
def apply(self, offset):
    eqs = []
    for eq in self.of(Or):
        a, b = eq.of(Equal)
        eqs.append(Equal(a + offset, b + offset))
    return Equivalent(self, Or(*eqs), evaluate=False)


@prove
def prove(Eq):
    x, a, b, c = Symbol(complex=True)
    Eq << apply(Or(Equal(x + a, b), Equal(x + a, c)), -a)

    Eq << Eq[-1].this.lhs.args[0] - a
    Eq << Eq[-1].this.lhs.args[0] - a


if __name__ == '__main__':
    run()
# created on 2018-11-28
