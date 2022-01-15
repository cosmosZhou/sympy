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

    j = Symbol(integer=True)
    p, q, n, m = Symbol(integer=True, positive=True)
    y = Symbol(shape=(p, q, m, n), real=True)
    Eq << apply(ReducedSum(y), var=j)

    i = Symbol(domain=Range(m))
    k = Symbol(domain=Range(q))
    h = Symbol(domain=Range(p))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], h)

    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], k)

    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], i)

    Eq << Eq[-1].this.lhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()
# created on 2020-03-11
