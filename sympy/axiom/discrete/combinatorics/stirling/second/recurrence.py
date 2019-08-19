from sympy.core.symbol import Symbol, Wild, dtype
from sympy.core.relational import Equality
from sympy.utility import plausible, cout, Eq, Sum, Ref, Union

from sympy.functions.combinatorial.numbers import Stirling
from sympy.sets.sets import FiniteSet, imageset, Interval
from sympy.sets.contains import Subset
from sympy.logic.boolalg import And
from sympy.functions.elementary.complexes import Abs
from sympy.core.basic import _aresame
from sympy.core.function import Function, Application
from sympy.functions.elementary.piecewise import Piecewise
from sympy.tensor.indexed import IndexedBase
from sympy.axiom import discrete


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

    e = Symbol('e', dtype=dtype.integer.set)
    s2_ = imageset(e, Union(e, FiniteSet(FiniteSet(n))), s2)

    plausible0 = Subset(s2_, s1, plausible=True)
    cout << plausible0

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

    plausible1 = Subset(s4_imageset_imageset, s1, plausible=True)
    cout << plausible1

    cout << Eq[-1].definition

    cout << Eq[-1].simplifier()

    cout << Equality.by_definition_of(s4_imageset)

    cout << Eq[-1].split()

    cout << Union[i:0:k](Eq[38])

    cout << Eq[-1].right.simplifier()

    cout << Eq[-1].subs(Eq[-3])

    cout << Eq[38].abs()

    cout << Sum[i:0:k](Eq[-1])

    cout << Eq[-1].right.simplifier()

    cout << discrete.sets.union.inequality.apply(*Eq[-1].rhs.args[1].arg.args)

    cout << Eq[-2].subs(Eq[-1])

    cout << Eq[-1].subs(Eq[44])

    cout << Eq[48].abs()

    u = Eq[-1].lhs.arg
    cout << discrete.sets.union.inequalities.apply(u.function, *u.limits)

    cout << Eq[-2].subs(Eq[-1])

    cout << Eq[-1].subs(Eq[-4])

    cout << Eq[49].split()

    cout << discrete.sets.union.greater_than.apply(*Eq[-2].rhs.arg.args[::-1])

    cout << Eq[-1].subs(Eq[43])

    cout << Eq[-4].subs(Eq[-1])

    cout << Eq[-4].subs(Eq[43])

    cout << (Eq[-1] & Eq[-2])

    cout << (Eq[48] & Eq[58] & Eq[-1])

    cout << Eq[-1].rewrite(forall=False, var=i)

    assumption, *_ = Eq[-1].exists.values()
    cout << Eq[-1].subs(assumption)

    cout << Eq[41].definition

    b, *_ = Eq[-1].forall.keys()

    cout << Eq[-1].subs(x[0:k + 1], b)

    cout << Ref[i](Eq[38])

    cout << plausible1.subs(Eq[-1])

    A = IndexedBase("A", (k + 1,), dtype=dtype.integer.set.set, definition=Ref[j](Eq[-1].args[0]))

    cout << Equality.by_definition_of(A)

    cout << Eq[-2].subs(Eq[-1].reversed)

    cout << Union[j](Eq[-1])

    B = Symbol("B", dtype=dtype.integer.set.set, definition=plausible0.args[0])

    cout << Equality.by_definition_of(B)

    cout << plausible0.subs(Eq[-1].reversed)

#


if __name__ == '__main__':
    prove()
