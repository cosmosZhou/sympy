from util import *


@apply
def apply(self):
    import builtins
    (first, second), *limits = self.of(Lamda[Mul])

    first = Lamda(first, *limits).simplify(squeeze=True)
    second = Lamda(second, *limits).simplify(squeeze=True)

    function = Mul(first, second)
    max_len = builtins.max(len(first.shape), len(second.shape))
    if max_len < len(self.shape):
        rhs = Lamda(function, *limits[:len(self.shape) - max_len])
    else:
        rhs = function

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a, b = Symbol(real=True, shape=(oo,))
    Eq << apply(Lamda[j:n](a[j] * b[j]))

    _j = Symbol('j', domain=Range(n))

    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], _j)


if __name__ == '__main__':
    run()

