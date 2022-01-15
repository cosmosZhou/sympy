from util import *


def compute_density(condition):
    ps = pspace(condition)
    fx, y = condition.args

    prod = S.One
    limits = []
    for var, sym in ps.values2symbols().items():
        assert pspace(var).is_Continuous
        prod *= Probability(Equal(var, sym))
        fx = fx._subs(var, sym)
        limits.append((sym,))

    assert not random_symbols(fx)

    if y.is_given or not y.is_symbol:
        y = condition.generate_var(real=True)

    return Derivative[y](Integral(prod * Bool(LessEqual(fx, y)), *limits))


@apply
def apply(self):
    condition = self.of(Probability)
    return Equal(self, compute_density(condition))


@prove(provable=False)
def prove(Eq):
    x, y, z = Symbol(real=True, random=True)
    t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Probability(Equal(f(x, y, z), t)))


if __name__ == '__main__':
    run()
# created on 2021-07-24
