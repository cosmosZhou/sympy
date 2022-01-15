from util import *


def is_continuous(f, a, b, x=None, xi=None, plausible=None):
    if x is None:
        x = Symbol('x', real=True)

    fx = f(x)
    if xi is None:
        xi = fx.generate_var(var='xi', excludes=a.free_symbols & b.free_symbols, real=True)

    kwargs = {}
    if plausible:
        kwargs['plausible'] = plausible

    return All[xi:a:b](Equal(Limit[x:xi](fx), f(xi)), **kwargs)


@apply
def apply(given):
    ((f, (z, xi, direction)), _f), (_xi, a, b) = given.of(All[Equal[Limit]])

    assert direction == 0
    assert xi == _xi
    assert _f == f._subs(z, xi)

    y = Symbol(real=True)
    return All(Any(Equal(f, y), (z, a, b)), (y, Minima[z:a:b](f), Maxima[z:a:b](f)))


@prove(proved=False)
def prove(Eq):
    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval(a, oo, left_open=True))
    f = Function(shape=(), real=True)
    Eq << apply(is_continuous(f, a, b))


if __name__ == '__main__':
    run()

# created on 2020-04-19
