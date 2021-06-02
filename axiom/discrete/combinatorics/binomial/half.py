from util import *



@apply
def apply(n):
    assert n.is_integer
    One = Number(1)
    return Equal(binomial(One / 2, n), -(-One / 4) ** n * binomial(2 * n, n) / (2 * n - 1))


@prove(surmountable=False)
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)
    Eq << apply(n)


if __name__ == '__main__':
    run()

