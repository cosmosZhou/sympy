from util import *


@apply
def apply(self, var=None):
    i = self.arg.generate_var(integer=True, var=var)
    *shape, n = self.arg.shape    
    assert shape
    
    excludes = {i}
    limits = []
    vars = []
    for m in shape:
        j = self.arg.generate_var(excludes, integer=True)
        limits.append((j, 0, m))
        vars.append(j)
        excludes.add(j)
    
    limits.reverse()
    vars.append(i)
    
    rhs = Lamda(Sum[i:n](self.arg[tuple(vars)]), *limits)
        
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    j = Symbol.j(integer=True)
    p = Symbol.p(integer=True, positive=True)
    q = Symbol.q(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    y = Symbol.y(shape=(p, q, m, n), real=True)
    Eq << apply(ReducedSum(y), var=j)

    i = Symbol.i(domain=Range(0, m))
    k = Symbol.k(domain=Range(0, q))
    h = Symbol.h(domain=Range(0, p))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], h)

    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], k)

    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], i)

    Eq << Eq[-1].this.lhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()