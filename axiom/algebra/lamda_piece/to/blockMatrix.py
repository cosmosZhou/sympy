from util import *


@apply
def apply(self):
    ecs, *limits = self.of(Lamda[Piecewise])
    i = self.variables[-1]
    n = self.shape[0]

    blocks = []
    length = 0
    h = 0
    for expr, cond in ecs:
        if cond.is_Less:
            assert cond.lhs == i
            upper_bound = cond.rhs
        else:
            assert cond
            upper_bound = n

        length = upper_bound - length
        blocks.append(Lamda[i:length](expr._subs(i, i + h)))
        h += length

    rhs = BlockMatrix(*blocks)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    m, n = Symbol(integer=True, positive=True)
    k, i = Symbol(domain=Range(n))
    g, h = Symbol(real=True, shape=(oo, m))
    Eq << apply(Lamda[i:n](Piecewise((g[i], i < k), (h[i], True))))

    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    run()
# created on 2019-10-22
# updated on 2019-10-22
