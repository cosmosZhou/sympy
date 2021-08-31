from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(minimize):
    function, *limits = minimize.of(Minima)
    return All(LessEqual(minimize, function), *limits)


@prove
def prove(Eq):
    x = Symbol(real=True, shape=(oo,))
    n, N = Symbol(integer=True)

    Eq << apply(Minima[n:N + 1](abs(x[n])))

#     Eq << ~Eq[-1]

    _n = Symbol.n(domain=Range(0, N + 1))
    Eq << Eq[-1].limits_subs(n, _n)

    Eq << Eq[-1].this.lhs.limits_subs(n, _n)

#     Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

