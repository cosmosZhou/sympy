from util import *


@apply(given=None)
def apply(self):
    (((j, i), (S[0], u)), ((S[i], (n, S[u])), (S[j], S[i]))), ((S[j], S[i]), (S[i], S[n - u])) = self.of((Element[Expr - Expr, Range] | (Symbol >= Expr - Expr) & GreaterEqual) & (GreaterEqual | (Less)))
    assert i in Range(n) and j in Range(n)
    return Equivalent(self, Element(j - i, Range(0, u)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n, u = Symbol(domain=Range(2, oo), given=True)
    i, j = Symbol(domain=Range(n), given=True)
    #i, j = Symbol(integer=True, nonnegative=True)
    Eq << apply(And(And(j >= i, i >= n - u) | Element(j - i, Range(u)), Or(j >= i, i < n - u)))

    Eq << Eq[0].this.find(Or).apply(algebra.ou.invert)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_range.to.ou)

    Eq << Eq[-1].this.find(Symbol >= Symbol) - i

    Eq << Eq[-1].this.find(Symbol >= Symbol) - i

    Eq << Eq[-1].this.find(Or[~And]).apply(algebra.et.distribute, 1)

    Eq << Eq[-1].this.find(GreaterEqual).apply(algebra.ge.transport)

    Eq << -Eq[-1].this.find(GreaterEqual)

    Eq << Eq[-1].this.lhs.apply(algebra.et.invert)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_range.to.ou)





if __name__ == '__main__':
    run()
# created on 2022-01-02


from . import offset
# updated on 2022-03-30
from . import min
