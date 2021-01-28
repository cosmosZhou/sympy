
from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy import Symbol
from axiom.discrete.combinatorics.binomial import Pascal
from sympy.concrete.summations import Sum
from sympy.core.add import Plus
from axiom import algebre
from sympy.core.numbers import Number


@apply(imply=True)
def apply(n):
    assert n.is_integer
    One = Number(1)
    return Equality(binomial(One / 2, n), -(-One / 4) ** n * binomial(2 * n, n) / (2 * n - 1))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)
    Eq << apply(n)

if __name__ == '__main__':
    prove(__file__)

