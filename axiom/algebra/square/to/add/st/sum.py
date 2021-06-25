from util import *


@apply
def apply(self):
    xi, limit = self.of(Sum ** 2)
    try:
        i, z, n = limit.of(Tuple)
    except:
        [i] = limit
        domain = xi.domain_defined(i)
        z, n = domain.of(Range)
        
    assert z == 0

    j = self.generate_var({i}, integer=True, var='j')
    xj = xi._subs(i, j)
    return Equal(self, 2 * Sum[j:i, i:n](xi * xj) + Sum[i:n](xi ** 2))


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True, given=False)
    x = Symbol.x(real=True, shape=(oo,))
    Eq << apply(Sum[i:n](x[i]) ** 2)

    Eq.initial = Eq[0].subs(n, 1)

    Eq << Eq.initial.this.find(Sum).apply(algebra.sum.to.add.doit.outer)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.find(Sum).split({n})

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.find(Sum).split({n})

    Eq << Eq[-1].this.rhs.find(Number * ~Sum).split({n})

    

    Eq << Eq[-1].this.rhs.find(Number * ~Sum).simplify()

    j = Eq[0].find(Number * ~Sum).variable
    Eq << Eq[-1].this.rhs.find(Indexed * ~Sum).limits_subs(j, i)

    Eq << Eq[0].induct(imply=True, reverse=True)

    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()
