from util import *


@apply(given=None)
def apply(self):
    (((j, i), ((l, n), S[1])), ((S[i], S[Min(n, l)]), (S[j], S[i]))), ((S[i], S[Min(n, l)]), (S[j], S[i])) = \
    self.of((Element[Expr - Expr, Range[1 - Min]] | Less & LessEqual) & (GreaterEqual | LessEqual))
    assert i in Range(n)
    assert j in Range(n)
    return Equivalent(self, Element(j - i, Range(-l + 1, 1)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, sets

    n, l = Symbol(domain=Range(2, oo), given=True)
    i, j = Symbol(domain=Range(n), given=True)
    Eq << apply(And(And(j <= i, i < Min(n, l)) | Element(j - i, Range(1 - Min(n, l), 1)), Or(j <= i, i >= Min(n, l))))

    Eq << Eq[0].this.find(Or).apply(algebra.ou.invert)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_range.to.ou)

    Eq << Eq[-1].this.find(Symbol <= Symbol) - i

    Eq << Eq[-1].this.find(Or[~And]).apply(algebra.et.distribute, 1)

    Eq << Eq[-1].this.find(Add < Add).apply(algebra.lt.transport)

    Eq << -Eq[-1].this.find(-Symbol < Add)

    Eq << Eq[-1].this.lhs.apply(algebra.et.invert)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_range.to.ou)

    Eq << Eq[-1].this.find(Symbol <= Symbol) - i

    Eq << Eq[-1].this.find(Element).apply(sets.el_range.to.et)

    Eq << Eq[-1].this.find(Element).apply(sets.el_range.to.et)

    Eq << Eq[-1].this.find(GreaterEqual[1 - Min]) - 1

    Eq << -Eq[-1].this.find(GreaterEqual[-Min])

    Eq << Eq[-1].this.find(LessEqual).apply(algebra.le_min.to.et.le)

    Eq << Eq[-1].this.find(LessEqual) - 1

    Eq << -Eq[-1].this.find(LessEqual)




if __name__ == '__main__':
    run()
# created on 2022-01-02
