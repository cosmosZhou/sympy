from util import *


@apply
def apply(self):
    fx, *limits = self.of(Cap)
    args = fx.of(Intersection)

    return Equal(self, Intersection(*(Cap(arg, *limits) for arg in args)))


@prove
def prove(Eq):
    from axiom import sets, algebra

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cap[x:A, y:B](f(x, y) & g(x, y)))

    #Eq << apply(Cap[x:A](f(x) & g(x)))
    Eq << sets.eq.given.et.infer.apply(Eq[0], wrt=y)

    Eq <<= Eq[-2].this.rhs.apply(sets.el_intersect.given.et.el, simplify=False), \
    Eq[-1].this.lhs.apply(sets.el_intersect.imply.et.el, simplify=False)

    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.el_cap.given.all_el), \
    Eq[-1].this.lhs.args[0].apply(sets.el_cap.imply.all_el)

    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.el_cap.given.all_el), \
    Eq[-1].this.lhs.args[0].apply(sets.el_cap.imply.all_el)

    Eq <<= Eq[-2].this.rhs.apply(algebra.all.all.given.all_et), \
    Eq[-1].this.lhs.apply(algebra.all.all.imply.all_et)

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cap.imply.all_el), \
    Eq[-1].this.rhs.apply(sets.el_cap.given.all_el)


if __name__ == '__main__':
    run()


from . import single_variable
from . import st
from . import doit
from . import split
# created on 2021-01-31
