from util import *
import axiom

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


def baseset_insert(self):
    function, *limits = self.args

    * limits, limit = limits
    x, cond = limit
    assert cond.is_boolean
    baseset = function.domain_defined(x) & cond.domain_defined(x)
    return self.func(function, *limits, (x, cond, baseset))

@apply
def apply(self):
    assert self.is_Cup
    return Equal(self, baseset_insert(self))


@prove
def prove(Eq):
    from axiom import sets
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True, positive=True)

    x = Symbol.x(shape=(n,), integer=True)
    a = Symbol.a(shape=(n,), integer=True)

    f = Function.f(etype=dtype.integer)
    h = Function.h(etype=dtype.real)

    Eq << apply(Cup[j:f(k), k: x[k] > a[i]](h(x[k], j)))

    Eq << Eq[-1].this.rhs.apply(sets.cup.limits.baseset.delete)

if __name__ == '__main__':
    run()

