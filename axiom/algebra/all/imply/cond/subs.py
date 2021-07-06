from util import *


@apply
def apply(given, old, new):
    from sympy.concrete.limits import limits_dict
    cond, *limits = given.of(All)

    domain = limits_dict(limits)[old]
    if domain.is_set:
        assert new in domain
    elif domain.is_boolean:
        assert domain._subs(old, new)
    else:
        return

    return cond._subs(old, new)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(integer=True)
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(shape=(), integer=True)
    s = Symbol.s(etype=dtype.integer)
    Eq << apply(All[x:0:n + 1](Contains(f(x), s)), x, n)

    Eq << algebra.all.imply.et.split.apply(Eq[0], cond={n})

    


if __name__ == '__main__':
    run()
