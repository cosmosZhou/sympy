from util import *

@apply
def apply(self):
    fx, *limits = self.of(Cup)
    args = fx.of(Union)

    return Equal(self, Union(*(Cup(arg, *limits) for arg in args)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(etype=dtype.real)
    g = Function.g(etype=dtype.real)
    F = Function.F(etype=dtype.real)

    Eq << apply(Cup[x:A, y:B](f(x, y) | g(x, y)))
#     Eq << apply(Cup[x:A](f(x) | g(x)))

    Eq << sets.eq.given.suffice.apply(Eq[0], wrt=y)

    Eq <<= Eq[-2].this.rhs.apply(sets.contains.given.ou.split.union, simplify=False), \
    Eq[-1].this.lhs.apply(sets.contains.imply.ou.split.union, simplify=False)

    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.contains.given.any_contains.st.cup), \
    Eq[-1].this.lhs.args[0].apply(sets.contains.imply.any_contains.st.cup)

    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.contains.given.any_contains.st.cup), \
    Eq[-1].this.lhs.args[0].apply(sets.contains.imply.any_contains.st.cup)

    Eq <<= Eq[-2].this.rhs.apply(algebra.ou.given.any_ou), \
    Eq[-1].this.lhs.apply(algebra.ou.imply.any_ou)

    Eq <<= Eq[-2].this.rhs.function.apply(sets.ou.given.contains), \
    Eq[-1].this.lhs.function.apply(sets.ou.imply.contains)

    Eq <<= Eq[-2].this.lhs.apply(sets.contains.imply.any_contains.st.cup), \
    Eq[-1].this.rhs.apply(sets.contains.given.any_contains.st.cup)


if __name__ == '__main__':
    run()

from . import doit
from . import st
from . import single_variable
from . import split