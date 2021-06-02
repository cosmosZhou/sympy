from util import *


@apply(given=None)
def apply(self):
    import axiom
    [*eqs] = self.of(And)

    for i, eq in enumerate(eqs):
        if isinstance(eq, ForAll):
            break
    else:
        return

    forall = eqs.pop(i)

    function, *limits = forall.args

    i, a, b = axiom.limit_is_Interval(limits)

    try:
        while eqs:
            j = eqs.index(function._subs(i, a - 1))
            del eqs[j]
            a -= 1
    except:
        return

    return Equivalent(self, ForAll[i:a:b](function))


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(domain=Range(0, n))

    x = Symbol.x(real=True, shape=(oo,))

    Eq << apply(And(ForAll[i:a:n](x[i] > 0), x[a - 1] > 0, x[a - 2] > 0))

    Eq << algebra.equivalent.given.cond.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(algebra.all.given.et, cond={a - 2}), Eq[-1].this.rhs.apply(algebra.all.imply.et.split, cond={a - 2})

    Eq <<= Eq[-2].this.rhs.apply(algebra.all.given.et, cond={a - 1}), Eq[-1].this.rhs.find(ForAll).apply(algebra.all.imply.et.split, cond={a - 1})


if __name__ == '__main__':
    run()

