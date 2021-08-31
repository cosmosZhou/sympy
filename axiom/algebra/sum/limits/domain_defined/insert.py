from util import *


def limits_insert(self):
    function, *limits = self.args

    * limits, limit = limits
    assert len(limit) == 1
    x = limit[0]

    domain_defined = function.domain_defined(x)

    return self.func(function, *limits, (x, domain_defined))

@apply
def apply(self):
    assert self.is_Sum
    return Equal(self, limits_insert(self))


@prove
def prove(Eq):
    from axiom import algebra
    i, j = Symbol(integer=True)
    k = Symbol(integer=True, positive=True)
    x = Symbol(shape=(k,), integer=True)

    f = Function(etype=dtype.integer)
    h = Function(real=True)

    Eq << apply(Sum[j:f(i), i](h(x[i], j)))

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.domain_defined.delete)

if __name__ == '__main__':
    run()

