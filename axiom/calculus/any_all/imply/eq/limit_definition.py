from util import *


@apply
def apply(given):
    (lt, *limits_f), *limits_e = given.of(Any[All])

    assert len(limits_f) == 1
    x, *ab = limits_f[0]
    if len(ab) == 2:
        domain = (Range if x.is_integer else Interval)(*ab)
    else:
        [domain] = ab

    abs_fx_A, epsilon = lt.of(Less)

    assert epsilon.is_symbol
    assert epsilon > 0
    assert epsilon.is_given is None

    fx_A = abs_fx_A.of(Abs)

    if fx_A.is_Add:
        fx = []
        A = []

        for arg in fx_A.of(Add):
            if arg._has(x):
                fx.append(arg)
            else:
                A.append(arg)

        fx = Add(*fx)
        A = -Add(*A)
    else:
        fx = fx_A
        A = 0

    assert len(limits_e) == 1
    delta, *_ = limits_e[0]
    assert delta >= 0

    if x.is_integer:
        assert delta.is_integer
        
        if domain.is_set:
            N1 = domain.of(Range[Infinity])
            _delta = N1 - 1
        else:
            _x, _delta = domain.of(Greater)
            assert x == _x
            
        assert delta == _delta
        return Equal(Limit[x:oo](fx), A)
    else:
        assert x.is_real
        assert not delta.is_integer and delta.is_real

        if domain.is_And:
            lt, gt = domain.args
            xx0, _delta = lt.of(Less)
            assert _delta == delta
            if xx0.is_Abs:
                _x, x0 = xx0.of(Abs[Expr - Expr])
                assert x == _x
                assert x0.is_real

                _xx0, zero = gt.of(Greater)
                assert zero == 0
                assert _xx0 == xx0
                dir = 0
            else:
                [*args] = xx0.of(Add)
                for i, arg in enumerate(args):
                    if arg == x:
                        del args[i]
                        x0 = -Add(*args)
                        dir = 1
                        break
                    if arg == -x:
                        del args[i]
                        x0 = Add(*args)
                        dir = -1
                        break
        elif domain.is_Greater:
            dir = -1
            x0 = oo

        return Equal(Limit[x:x0:dir](fx).simplify(), A)


@prove
def prove(Eq):
    from axiom import calculus

    n, N = Symbol(integer=True, positive=True)
    x, x0, a = Symbol(real=True)
    #x = Symbol.x(real=True, shape=(n,))
    #x = Symbol.x(integer=True)
    f = Function(real=True, shape=())
    #x0 = Symbol.x0(real=True, shape=(n,))
    #x0 = oo
    #x0 = -oo
    #a = oo
    #a = -oo
    epsilon, delta = Symbol(real=True, positive=True)
    Eq << apply(Any[delta](All[x: (abs(x - x0) > 0) & (abs(x - x0) < delta)](abs(f(x) - a) < epsilon)))

    Eq << Eq[1].this.apply(calculus.eq.to.any_all.limit_definition)


if __name__ == '__main__':
    run()

