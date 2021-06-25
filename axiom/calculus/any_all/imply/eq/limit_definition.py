from util import *


@apply
def apply(given):
    (lt, *limits_f), *limits_e = given.of(Any[All])

    assert len(limits_f) == 1
    x, domain = limits_f[0]

    abs_fx_A, ε = lt.of(Less)

    assert ε.is_symbol
    assert ε > 0
    assert ε.is_given is None

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
    δ, *_ = limits_e[0]
    assert δ > 0

    if x.is_integer:
        assert δ.is_integer

        _x, _δ = domain.of(Greater)
        assert x == _x
        assert δ == _δ
        return Equal(Limit[x:oo](fx), A)
    else:
        assert x.is_real
        assert not δ.is_integer and δ.is_real

        if domain.is_And:
            lt, gt = domain.args
            xx0, _δ = lt.of(Less)
            assert _δ == δ
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

        return Equal(Limit[x:x0:dir](fx), A)


@prove
def prove(Eq):
    from axiom import calculus
    n = Symbol.n(integer=True, positive=True)

    x = Symbol.x(real=True)
#     x = Symbol.x(real=True, shape=(n,))
#     x = Symbol.x(integer=True)

    f = Function.f(real=True, shape=())

    x0 = Symbol.x0(real=True)
#     x0 = Symbol.x0(real=True, shape=(n,))

#     x0 = oo
#     x0 = -oo

    a = Symbol.a(real=True)
#     a = oo
#     a = -oo

    N = Symbol.N(integer=True, positive=True)
    ε = Symbol.ε(real=True, positive=True)
    δ = Symbol.δ(real=True, positive=True)
    Eq << apply(Any[δ](All[x: (abs(x - x0) > 0) & (abs(x - x0) < δ)](abs(f(x) - a) < ε)))

    Eq << Eq[1].this.apply(calculus.eq.to.any_all.limit_definition)


if __name__ == '__main__':
    run()

