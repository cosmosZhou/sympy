from util import *


@apply
def apply(given, epsilon=None):
    ((f, (z, xi, direction)), _f), (_xi, a, b) = given.of(All[Equal[Limit]])
    assert direction == 0
    assert xi == _xi
    assert _f == f._subs(z, xi)

    if not isinstance(epsilon, Basic):
        if epsilon is None:
            epsilon = 'epsilon'
        epsilon = given.generate_var(real=True, var=epsilon)

    return Any[epsilon:0:1](Equal(Integral(f, (z, a, b)), (b - a) * f._subs(z, a * epsilon + b * (1 - epsilon))))


@prove(proved=False)
def prove(Eq):
    from axiom import calculus

    a, b = Symbol(real=True)
    f = Function(real=True)
    from axiom.calculus.all_eq.imply.all_any_eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))


if __name__ == '__main__':
    run()
# created on 2020-05-02
