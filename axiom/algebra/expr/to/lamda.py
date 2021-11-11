from util import *


@apply
def apply(self):
    assert self.shape
    
    excludes = set()
    limits = []
    vars = []
    for m in self.shape:
        j = self.generate_var(excludes, integer=True)
        limits.append((j, 0, m))
        vars.append(j)
        excludes.add(j)
    
    limits.reverse()    
    rhs = Lamda(self[tuple(vars)], *limits)
        
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    p, q, n, m = Symbol(integer=True, positive=True)
    Y = Symbol(shape=(p, q, m, n), real=True)
    Eq << apply(Y)

    i = Symbol(domain=Range(p))
    k = Symbol(domain=Range(q))
    h = Symbol(domain=Range(m))
    t = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], k)

    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], h)

    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], t)


if __name__ == '__main__':
    run()
# created on 2019-05-08
# updated on 2019-05-08
