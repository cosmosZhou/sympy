from util import *


def limits_absorb(given, index):
    [*eqs], *limits = given.of(Any[And])
    eq = eqs[index]
    del eqs[index]

    function = And(*eqs)
    variables = given.variables
    wrt = {v for v in variables if eq._has(v)}

    assert wrt
    if len(wrt) == 1:
        [wrt] = wrt
        i = variables.index(wrt)
        wrt, *ab = limits[i]
        if ab:
            if len(ab) == 1:
                cond, *_ = ab
                if cond.is_boolean:
                    eq &= cond
                else:
                    eq &= Contains(wrt, cond)
            else:
                assert len(ab) == 2
                a, b = ab
                if a.is_boolean:
                    eq &= a & Contains(wrt, b)
                else:
                    eq &= Contains(wrt, (Range if wrt.is_integer else Interval)(a, b))
        limits[i] = (wrt, eq)
    elif len(wrt) == 2:
        x_slice, x_index = wrt
        if x_slice.is_Indexed:
            x_slice, x_index = x_index, x_slice

        if x_slice.is_Slice and x_index.is_Indexed:
            start, stop = x_slice.index
            assert len(x_index.indices) == 1
            assert x_index.indices[0] == stop
            i = variables.index(x_slice)
            j = variables.index(x_index)

            del limits[j]
            wrt, cond = limits[i]
            wrt = x_slice.base[start:stop + 1]
            limits[i] = (wrt, cond & eq)
        else:
            limit_a, *limit_b = limits
            if len(limit_a) == 2:
                a, fa = limit_a
                if fa.is_boolean:
                    limit_a = (a, fa & eq)
                    limits[0] = limit_a
                else:
                    eq = eq.domain_conditioned(a)
                    limit_a = (a, fa & eq)
                    limits[0] = limit_a
            elif len(limit_a) == 1:
                a = limit_a[0]
                limits[0] = (a, eq)
            else:
                x, a, b = limit_a
                limits[0] = (x, eq, Range(a, b) if x.is_integer else Interval(a, b))
    else:
        return

    return Any(function, *limits)


@apply
def apply(given, index):
    return limits_absorb(given, index)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(oo,))

    f = Function.f(shape=(), integer=True)
    f_quote = Function("f'", nargs=(n,), shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    h = Function.h(shape=(), integer=True)

    Eq << apply(Any[x[:n]:f(x[:n]) > 0, x[n]]((g(x[n]) > f_quote(x[:n])) & (h(x[:n + 1]) > 0)), index=0)

    S = Symbol.S(conditionset(x[:n + 1], (g(x[n]) > f_quote(x[:n])) & (f(x[:n]) > 0)))

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[0])

    Eq << Any[x[:n + 1]](Contains(x[:n + 1], S) & (h(x[:n + 1]) > 0), plausible=True)

    Eq << Eq[-1].this.expr.args[1].rhs.definition

    Eq << Eq[-1].simplify()

    Eq << Eq[-1].this.limits[0][1].definition


if __name__ == '__main__':
    run()

