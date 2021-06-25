from util import *


@apply
def apply(given, index):
    [*eqs], *limits = given.of(Any[And])
    
    eq = eqs[index]
    del eqs[index]
    wrt, B = eq.of(Contains)

    i = given.variables.index(wrt)

    function = And(*eqs)

    A = given.limits_dict[wrt]
    if A:
        limits[i] = (wrt, A & B)
    else:
        limits[i] = (wrt, B)

    return Any(function, *limits)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(oo,))

    A = Symbol.A(etype=dtype.real * n)
    B = Symbol.B(etype=dtype.real * n)

    f = Function.f(shape=(), integer=True)

    Eq << apply(Any[x[:n]: A](Contains(x[:n], B) & (f(x[:n]) > 0)), index=1)

    Eq << sets.any.imply.any_et.single_variable.apply(Eq[0])


if __name__ == '__main__':
    run()

