from util import *


@apply(given=None)
def apply(self):
    (((j, i), (S[0], (n, u))), ((S[i], S[n - Min(n, u)]), (S[j], S[i]))), ((S[j], S[i]), (S[i], S[n - Min(n, u)])) = self.of((Element[Expr - Expr, Range[Min]] | GreaterEqual & GreaterEqual) & (GreaterEqual | (Less)))
    assert i in Range(n)
    assert j in Range(n)
    return Equivalent(self, Element(j - i, Range(0, u)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n, u = Symbol(domain=Range(2, oo), given=True)
    i, j = Symbol(domain=Range(n), given=True)
    Eq << apply(And(And(j >= i, i >= n - Min(n, u)) | Element(j - i, Range(Min(n, u))), Or(j >= i, i < n - Min(n, u))))

    Eq << Eq[0].this.find(Or).apply(algebra.ou.invert)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_range.to.ou)

    Eq << Eq[-1].this.find(Symbol >= Symbol) - i

    Eq << Eq[-1].this.find(Symbol >= Symbol) - i

    Eq << Eq[-1].this.find(Or[~And]).apply(algebra.et.distribute, 1)

    Eq << Eq[-1].this.find(GreaterEqual).apply(algebra.ge.transport)

    Eq << -Eq[-1].this.find(GreaterEqual)

    Eq << Eq[-1].this.lhs.apply(algebra.et.invert)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_range.to.ou)

    Eq << Eq[-1].this.find(Range).apply(sets.range_min.to.intersect)

    Eq << Eq[-1].this.find(Element).apply(sets.el_intersect.to.et)

    Eq << Eq[-1].this.lhs.find(Element).apply(sets.el_range.to.et)

    Eq << Eq[-1].this.find(Element).apply(sets.el_range.to.et)

    Eq << Eq[-1].this.find(Element).apply(sets.el_range.to.et)


if __name__ == '__main__':
    run()
# created on 2022-03-30
