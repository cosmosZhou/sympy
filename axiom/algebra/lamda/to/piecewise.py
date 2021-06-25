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

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True, given=True)
    a = Symbol.a(integer=True)
    n = Symbol.n(integer=True, positive=True)
    g = Symbol.g(shape=(n, n), real=True)
    h = Symbol.h(shape=(n, n), real=True)
    Eq << apply(Lamda[i:n](Piecewise((g[i, j], j < a),(h[i, j], True))))

    i = Symbol.i(domain=Range(0, n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    run()