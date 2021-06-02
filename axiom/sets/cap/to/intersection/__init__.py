from util import *


@apply
def apply(self):
    fx, *limits = self.of(Cap)
    args = fx.of(Intersection)

    return Equal(self, Intersection(*(Cap(arg, *limits) for arg in args)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(etype=dtype.real)
    g = Function.g(etype=dtype.real)

    Eq << apply(Cap[x:A, y:B](f(x, y) & g(x, y)))
#     Eq << apply(Cap[x:A](f(x) & g(x)))

    Eq << sets.eq.given.suffice.apply(Eq[0], wrt=y)

    Eq <<= Eq[-2].this.rhs.apply(sets.contains.given.contains.split.intersection, simplify=False), \
    Eq[-1].this.lhs.apply(sets.contains.imply.contains.split.intersection, simplify=False)

    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.contains.given.all_contains.st.cap), \
    Eq[-1].this.lhs.args[0].apply(sets.contains.imply.all_contains.st.cap)

    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.contains.given.all_contains.st.cap), \
    Eq[-1].this.lhs.args[0].apply(sets.contains.imply.all_contains.st.cap)

    Eq <<= Eq[-2].this.rhs.apply(algebra.et.given.all_et), \
    Eq[-1].this.lhs.apply(algebra.all.all.imply.all_et.limits_intersect)

    Eq <<= Eq[-2].this.lhs.apply(sets.contains.imply.all_contains.st.cap), \
    Eq[-1].this.rhs.apply(sets.contains.given.all_contains.st.cap)


if __name__ == '__main__':
    run()

from . import single_variable
from . import st
from . import doit
from . import dissect
