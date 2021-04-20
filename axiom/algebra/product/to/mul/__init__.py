from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets
from sympy.concrete.limits import limits_dictionary, limits_update
from axiom.algebra.sum.to.add import difference_of_domain_defined
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self, simplify=True):
    assert self.is_Product
    args = []
    domain_defined = self.function.domain_defined_for_limits(self.limits)

    limitsDict = limits_dictionary(self.limits)
    for arg in axiom.is_Mul(self.function):
        arg_domain_defined = arg.domain_defined_for_limits(self.limits)
        diff_set = difference_of_domain_defined(domain_defined, arg_domain_defined, limitsDict)
        if diff_set:
            limits = limits_update(self.limits, diff_set)
        else:
            limits = self.limits
        arg = self.func(arg, *limits)

        if simplify:
            arg = arg.simplify()
        args.append(arg)

    return Equal(self, Mul(*args, evaluate=False))


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)

    C = Symbol.C(etype=dtype.integer, given=True)

    f = Function.f(real=True)
    h = Function.h(real=True)
    x = Symbol.x(shape=(n,), real=True)
    y = Symbol.y(shape=(n, n), real=True)

    Eq << apply(Product[i:C, j](f(i) * x[i] * h(j) * x[j] * y[i, j]))


if __name__ == '__main__':
    prove()

from . import st
from . import doit
from . import dissect
