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
    x = Symbol.x(etype=dtype.integer)
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(etype=dtype.integer)
    Eq << apply(Cap[k:n](f(k)) | x)

    Eq << sets.eq.given.suffice.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(sets.contains.given.all_contains.st.cap),\
    Eq[-1].this.lhs.apply(sets.contains.imply.all_contains.st.cap)

    Eq <<= Eq[-2].this.rhs.expr.apply(sets.contains.given.ou.split.union),\
    Eq[-1].this.lhs.expr.apply(sets.contains.imply.ou.split.union)

    Eq <<= Eq[-2].this.lhs.apply(sets.contains.imply.ou.split.union),\
    Eq[-1].this.rhs.apply(sets.contains.given.ou.split.union)

    Eq <<= Eq[-2].this.find(Contains[Cap]).apply(sets.contains.imply.all_contains.st.cap),\
    Eq[-1].this.find(Contains[Cap]).apply(sets.contains.given.all_contains.st.cap)

if __name__ == '__main__':
    run()
