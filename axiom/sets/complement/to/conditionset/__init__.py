from util import *


@apply
def apply(self):
    (x, (_x, cond, baseset)), B = self.of(Complement[Cup[FiniteSet], Basic])
    assert _x == x
    return Equal(self, conditionset(x, cond, baseset - B))


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    f = Function.f(integer=True)

    Eq << apply(conditionset(x, f(x) > 0, A) // B)

    Eq << sets.eq.given.suffice.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.contains.imply.et.split.complement, simplify=None), \
    Eq[-1].this.rhs.apply(sets.contains.given.et.split.complement, simplify=None)

    Eq <<= Eq[-2].this.lhs.find(Contains).simplify(), Eq[-1].this.rhs.find(Contains).simplify()

    Eq <<= Eq[-2].this.rhs.simplify(), Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()

from . import is_odd
