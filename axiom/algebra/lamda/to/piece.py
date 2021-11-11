from util import *


@apply
def apply(self):
    ecs, *limits = self.of(Lamda[Piecewise])

    variables = self.variables
    args = []
    for e, c in ecs:
        assert not c._has(*variables)
        args.append((Lamda(e, *limits).simplify(), c))

    rhs = Piecewise(*args)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i, a = Symbol(integer=True)
    j = Symbol(integer=True, given=True)
    n = Symbol(integer=True, positive=True)
    g, h = Symbol(shape=(n, n), real=True)
    Eq << apply(Lamda[i:n](Piecewise((g[i, j], j < a),(h[i, j], True))))

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    run()
# created on 2019-10-19
# updated on 2019-10-19
