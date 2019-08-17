from sympy.core.symbol import Symbol, Wild
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq, Sum, Ref

from sympy.functions.combinatorial.numbers import Stirling
from sympy.sets.sets import FiniteSet, imageset, Union, Interval
from sympy.sets.contains import Subset
from sympy.logic.boolalg import And
from sympy.functions.elementary.complexes import Abs
from sympy.core.basic import _aresame
from sympy.core.function import Function, Application
from sympy.functions.elementary.piecewise import Piecewise
from sympy.tensor.indexed import IndexedBase


def apply(n, k):
    return Equality(Stirling(n + 1, k + 1), Stirling(n, k) + (k + 1) * Stirling(n, k + 1),
                    plausible=plausible())


from sympy.utility import check


@check
def prove():
    k = Symbol('k', integer=True, nonnegative=True)
    n = Symbol('n', integer=True, nonnegative=True)
    cout << apply(n, k)

    cout << Equality.by_definition_of(Eq[0].lhs)
    cout << Equality.by_definition_of(Eq[0].rhs.args[1])
    cout << Equality.by_definition_of(Eq[0].rhs.args[0].args[1])

    s1 = Symbol('s1', definition=Eq[1].rhs.arg)
    s2 = Symbol('s2', definition=Eq[2].rhs.arg)
    s3 = Symbol('s3', definition=Eq[3].rhs.arg)

    from sympy.core.symbol import dtype

    e = Symbol('e', dtype=dtype.integer.set)
    s2_ = imageset(e, Union(e, FiniteSet(FiniteSet(n))), s2)

    cout << Subset(s2_, s1, plausible=True)

    cout << Eq[-1].definition

    cout << Eq[-1].simplifier()

    cout << Equality.by_definition_of(s2)

    cout << Equality.by_definition_of(s1)

    cout << Eq[-2].split()

    i = Eq[-1].lhs.limits[0][0]

    x, *_ = Eq[-1].exists.keys()
    x = x.base

    cout << Equality.define(x[k], FiniteSet(n))
    cout << Eq[-1].union(Eq[-2])

    cout << Eq[-1].rewrite(exists=None)

    cout << Eq[-1].split()

    cout << Eq[12].set

    cout << Eq[-1].union(Eq[-3])

    cout << Eq[12].abs()

    cout << Eq[10] + Eq[-1]

    cout << Eq[-1].rewrite(exists=None)
    cout << Eq[-1].split()

    cout << Eq[19].subs(1, 0)

    cout << Eq[9].rewrite(exists=None)
    cout << Eq[-1].split()

    cout << (Eq[-2] & Eq[-4])

    cout << Eq[-1].simplifier()

    cout << (Eq[18] & Eq[16] & Eq[-1])

    cout << Eq[-1].rewrite(forall=False, var=Eq[-2].forall.keys())

    cout << (Eq[-1] & Eq[22])

    cout << Eq[-1].rewrite(exists=-1)

    cout << Eq[6].definition

    cout << Equality.by_definition_of(s3)

    s4 = Symbol('s4', definition=s3.definition.limits[0][1])
    cout << Equality.by_definition_of(s4)

    x_tuple, *_ = Eq[-1].forall.keys()
    cout << Eq[-1].split()

    j = Symbol('j', integer=True, domain=Interval(0, k))

    x_ = IndexedBase("x'", (k + 1,), dtype=dtype.integer,
                     definition=Ref[i](Piecewise((Union(x_tuple[i], FiniteSet(n)) , Equality(i, j)), (x_tuple[i], True))))

    cout << Equality.by_definition_of(x_)

    s4_imageset = imageset(x_tuple, x_, s4)
    imageFunction, imageSymbol, _ = s3.definition.image_set()

    s4_imageset_imageset = imageset(imageSymbol, imageFunction, s4_imageset)

    cout << Subset(s4_imageset_imageset, s1, plausible=True)

    cout << Eq[-1].definition

    cout << Eq[-1].simplifier()

    cout << Equality.by_definition_of(s4_imageset)

    eq = Eq[-1]
#     cout << eq.split_debug()
    cout << eq.split()
#     cout << Eq[-1].split_debug()


if __name__ == '__main__':
    prove()
