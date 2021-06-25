from util import *


@apply
def apply(given):
    function, (lhs, *rhs) = given.of(Any)
    if len(rhs) == 2:
        rhs = Range(*rhs) if lhs.is_integer else Interval(*rhs)
    else:
        [rhs] = rhs
    
    return Any[lhs]((function & Contains(lhs, rhs)).simplify())


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    f = Function.f(shape=(), integer=True)

    Eq << apply(Any[e:S](f(e) > 0))
    
    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

