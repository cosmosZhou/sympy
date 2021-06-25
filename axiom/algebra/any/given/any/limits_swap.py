from util import *



@apply
def apply(self):
    function, *limits = self.of(Any)
    assert len(limits) == 2
    limit0, limit1 = limits

    x, *domain_x = limit0
    y, *domain_y = limit1

    for s in domain_x:
        assert not s._has(y)

    limits = limit1, limit0
    return Any(function, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    A = Symbol.A(etype=dtype.integer)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Any[x:A, y:f(y) > 0](g(x, y) > 0))

    Eq << algebra.any.imply.any.limits.swap.apply(Eq[1])


if __name__ == '__main__':
    run()

