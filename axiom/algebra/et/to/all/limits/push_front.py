from util import *


@apply(given=None)
def apply(self):
    [*eqs] = self.of(And)

    for i, eq in enumerate(eqs):
        if eq.is_All:
            break
    else:
        return

    forall = eqs.pop(i)

    function, (i, a, b) = forall.of(All[Tuple])
    assert i.is_integer
    try:
        while eqs:
            j = eqs.index(function._subs(i, a - 1))
            del eqs[j]
            a -= 1
    except:
        return

    return Equivalent(self, All[i:a:b](function))


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(domain=Range(0, n))

    x = Symbol.x(real=True, shape=(oo,))

    Eq << apply(And(All[i:a:n](x[i] > 0), x[a - 1] > 0, x[a - 2] > 0))

    Eq << algebra.equivalent.given.et.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(algebra.all.given.et, cond={a - 2}), Eq[-1].this.rhs.apply(algebra.all.imply.et.split, cond={a - 2})

    Eq <<= Eq[-2].this.rhs.apply(algebra.all.given.et, cond={a - 1}), Eq[-1].this.rhs.find(All).apply(algebra.all.imply.et.split, cond={a - 1})


if __name__ == '__main__':
    run()

