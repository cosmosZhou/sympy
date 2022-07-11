from util import *

@apply
def apply(self):
    fx, *limits = self.of(Cup)
    args = fx.of(Union)

    return Equal(self, Union(*(Cup(arg, *limits) for arg in args)))


@prove
def prove(Eq):
    from axiom import sets, algebra

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cup[x:A, y:B](f(x, y) | g(x, y)))

    #Eq << apply(Cup[x:A](f(x) | g(x)))
    Eq << sets.eq.given.et.infer.apply(Eq[0], wrt=y)

    Eq <<= Eq[-2].this.rhs.apply(sets.el_union.given.ou, simplify=False), \
    Eq[-1].this.lhs.apply(sets.el_union.imply.ou, simplify=False)

    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.el_cup.given.any_el), \
    Eq[-1].this.lhs.args[0].apply(sets.el_cup.imply.any_el)

    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.el_cup.given.any_el), \
    Eq[-1].this.lhs.args[0].apply(sets.el_cup.imply.any_el)

    Eq <<= Eq[-2].this.rhs.apply(algebra.ou.given.any_ou), \
    Eq[-1].this.lhs.apply(algebra.ou.imply.any_ou)

    Eq <<= Eq[-2].this.rhs.expr.apply(sets.ou.given.el), \
    Eq[-1].this.lhs.expr.apply(sets.ou.imply.el)

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cup.imply.any_el), \
    Eq[-1].this.rhs.apply(sets.el_cup.given.any_el)


if __name__ == '__main__':
    run()

from . import doit
from . import st
from . import single_variable
from . import split
# created on 2021-02-10
