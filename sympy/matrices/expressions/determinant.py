from __future__ import print_function, division

from sympy import Basic, Expr, S, sympify
from .matexpr import ShapeError


class Determinant(Expr):
    """Matrix Determinant

    Represents the determinant of a matrix expression.

    Examples
    ========

    >>> from sympy import MatrixSymbol, Determinant, eye
    >>> A = MatrixSymbol('A', 3, 3)
    >>> Determinant(A)
    Determinant(A)
    >>> Determinant(eye(3)).doit()
    1
    """
    is_commutative = True

    def __new__(cls, mat):
        from sympy.matrices.expressions.matexpr import VConcatenate, HConcatenate
        if isinstance(mat, list):
            mat = VConcatenate(*mat)
        elif isinstance(mat, tuple):
            mat = HConcatenate(*mat)

        mat = sympify(mat)
#         if not mat.is_Matrix:
#             raise TypeError("Input to Determinant, %s, not a matrix" % str(mat))

        assert mat.is_square, "Det of a non-square matrix"

        return Basic.__new__(cls, mat)

    @property
    def arg(self):
        return self.args[0]

    def doit(self, expand=False):
        try:
            return self.arg._eval_determinant()
        except (AttributeError, NotImplementedError):
            return self
        except Exception as e:
            print(e)
            self.arg._eval_determinant()
            return self

    @property
    def shape(self):
        return ()

    @property
    def atomic_dtype(self):
        return self.arg.atomic_dtype

    def simplify(self, deep=False, **kwargs):
        if deep:
            this = Expr.simplify(self, deep=True, **kwargs)
            if this is not self:
                return this

        matrix = self.arg
        if matrix.is_DenseMatrix:
            if len(matrix._mat) == 1:
                return matrix._mat[0]
            
        return self

def det(matexpr):
    """ Matrix Determinant

    Examples
    ========

    >>> from sympy import MatrixSymbol, det, eye
    >>> A = MatrixSymbol('A', 3, 3)
    >>> det(A)
    Determinant(A)
    >>> det(eye(3))
    1
    """

    return Determinant(matexpr).doit()


from sympy.assumptions.ask import ask, Q
from sympy.assumptions.refine import handlers_dict


def refine_Determinant(expr, assumptions):
    """
    >>> from sympy import MatrixSymbol, Q, assuming, refine, det
    >>> X = MatrixSymbol('X', 2, 2)
    >>> det(X)
    Determinant(X)
    >>> with assuming(Q.orthogonal(X)):
    ...     print(refine(det(X)))
    1
    """
    if ask(Q.orthogonal(expr.arg), assumptions):
        return S.One
    elif ask(Q.singular(expr.arg), assumptions):
        return S.Zero
    elif ask(Q.unit_triangular(expr.arg), assumptions):
        return S.One

    return expr


handlers_dict['Determinant'] = refine_Determinant
