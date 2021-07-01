from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


def baseset_delete(self):
    function, *limits = self.args

    * limits, limit = limits
    x, cond, baseset = limit
    assert cond.is_boolean
    assert baseset.is_set

    assert function.domain_defined(x) & cond.domain_defined(x) in baseset
    return self.func(function, *limits, (x, cond))


@apply
def apply(self):
    assert self.is_Cup
    return Equal(self, baseset_delete(self))


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

    Eq << apply(Cup[j:f(k), k: x[k] > a[i]: Range(0, n)](h(x[k], j)))

    s = Symbol.s(Cup[j:f(k)](h(x[k], j)))
    Eq << s.this.definition

    Eq << sets.eq.imply.eq.cup.apply(Eq[-1], (k, x[k] > a[i], Range(0, n)))

    Eq << Eq[-1].this.lhs.function.definition

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

