from util import *


@apply
def apply(self):
    (x, (_x, cond, baseset)), B = self.of(Complement[Cup[FiniteSet], Basic])
    assert _x == x
    return Equal(self, conditionset(x, cond, baseset - B))


@prove
def prove(Eq):
    from axiom import sets
    A, B = Symbol(etype=dtype.integer)
    x = Symbol(integer=True)
    f = Function(integer=True)

    Eq << apply(conditionset(x, f(x) > 0, A) - B)

    Eq << sets.eq.given.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_complement.imply.et, simplify=None), \
    Eq[-1].this.rhs.apply(sets.el_complement.given.et, simplify=None)

    Eq <<= Eq[-2].this.lhs.find(Element).simplify(), Eq[-1].this.rhs.find(Element).simplify()

    Eq <<= Eq[-2].this.rhs.simplify(), Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()

from . import is_odd
# created on 2020-11-17
