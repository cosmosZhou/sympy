from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import Ref, Sum, cout, Eq, plausible
from sympy.core.relational import Equality, GreaterThan
from sympy.core.function import Function
from sympy.logic.boolalg import plausibles_dict


class KL(Function):

    @classmethod
    def eval(cls, x, y):

        if x.is_Number:
            if x is S.Zero:
                return S.One
            elif x is S.Infinity:
                return S.Zero

    def _eval_is_real(self):
        return self.args[0].is_real


def apply(p, q):
    x = Symbol('x')
    y = Symbol('y')
    return GreaterThan(KL(p(x, y), q(x, y)), KL(p(x), q(x)),
                    plausible=plausible(),
                    forall=[x, y])


from sympy.utility import check
@check
def prove():
    ...
#     cout << apply(p, q)


if __name__ == '__main__':
    prove()
    print('plausibles_dict:')
    for index, eq in plausibles_dict(Eq).items():
        print("Eq[%d] : %s" % (index, eq))
