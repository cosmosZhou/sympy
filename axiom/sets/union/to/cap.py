from util import *



@apply
def apply(self):
    for i, union in enumerate(self.args):
        if isinstance(union, Cap):
            args = [*self.args]
            del args[i]
            this = self.func(*args)
            function = union.expr | this
            return Equal(self, union.func(function, *union.limits), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol(etype=dtype.integer)
    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(etype=dtype.integer)
    Eq << apply(Cap[k:n](f(k)) | x)

    Eq << sets.eq.given.et.infer.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(sets.el_cap.given.all_el),\
    Eq[-1].this.lhs.apply(sets.el_cap.imply.all_el)

    Eq <<= Eq[-2].this.rhs.expr.apply(sets.el_union.given.ou),\
    Eq[-1].this.lhs.expr.apply(sets.el_union.imply.ou)

    Eq <<= Eq[-2].this.lhs.apply(sets.el_union.imply.ou),\
    Eq[-1].this.rhs.apply(sets.el_union.given.ou)

    Eq <<= Eq[-2].this.find(Element[Cap]).apply(sets.el_cap.imply.all_el),\
    Eq[-1].this.find(Element[Cap]).apply(sets.el_cap.given.all_el)

if __name__ == '__main__':
    run()
# created on 2021-07-11
