from util import *




@apply
def apply(self, given):
    marginal_probability = self.marginalize(given)
    x = pspace(given).symbol
    if given.is_integer:
        return Equal(Sum[x](self), marginal_probability)
    else:
        return Equal(Integral[x](self), marginal_probability)


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    P = Probability(x, y)
    Eq << apply(P, y)


if __name__ == '__main__':
    run()
