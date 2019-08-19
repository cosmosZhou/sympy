from sympy.core.relational import Equality, LessThan
from sympy.utility import plausible, cout, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union, Intersection

#reference
#www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml

def apply(A, B):
    return Equality(abs(Union(A, B)), abs(A) + abs(B) - abs(Intersection(A, B)),
                    plausible=plausible())


from sympy.utility import check


@check
def prove():
    A = Symbol('A', dtype = dtype.integer)
    B = Symbol('B', dtype = dtype.integer)
    cout << apply(A, B)

if __name__ == '__main__':
    prove()

