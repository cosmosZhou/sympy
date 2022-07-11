from util import *


@apply(given=None)
def apply(self):
    (((j, i), (l, S[1])), ((S[i], S[l]), (S[j], S[i]))), ((S[i], S[l]), (S[j], S[i])) = \
    self.of((Element[Expr - Expr, Range[1 - Expr]] | Less & LessEqual) & (GreaterEqual | LessEqual))
    assert i >= 0
    assert j >= 0
    return Equivalent(self, Element(j - i, Range(-l + 1, 1)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, sets

    l = Symbol(domain=Range(2, oo))
    i, j = Symbol(integer=True, nonnegative=True)
    Eq << apply(And(And(j <= i, i < l) | Element(j - i, Range(1 - l, 1)), Or(j <= i, i >= l)))

    Eq << Eq[0].this.find(Or).apply(algebra.ou.invert)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_range.to.ou)

    Eq << Eq[-1].this.find(Symbol <= Symbol) - i

    Eq << Eq[-1].this.find(Or[~And]).apply(algebra.et.distribute, 1)

    Eq << Eq[-1].this.find(Add < Add).apply(algebra.lt.transport)

    Eq << -Eq[-1].this.find(-Symbol < Add)

    Eq << Eq[-1].this.lhs.apply(algebra.et.invert)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_range.to.ou)

    Eq << Eq[-1].this.find(Symbol <= Symbol) - i


















if __name__ == '__main__':
    run()
# created on 2022-03-17


from . import min