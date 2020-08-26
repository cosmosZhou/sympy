from __future__ import print_function, division

from sympy import Basic, Expr, S, sympify


class Det(Expr):
    """Matrix Determinant

    Represents the determinant of a matrix expression.

    Examples
    ========

    >>> from sympy import MatrixSymbol, Det, eye
    >>> A = MatrixSymbol('A', 3, 3)
    >>> Det(A)
    Det(A)
    >>> Det(eye(3)).doit()
    1
    """
    is_complex = True
    is_Det = True

    def __new__(cls, mat):
        from sympy.matrices.expressions.matexpr import VConcatenate, HConcatenate
        if isinstance(mat, list):
            mat = VConcatenate(*mat)
        elif isinstance(mat, tuple):
            mat = HConcatenate(*mat)

        mat = sympify(mat)
        assert mat.is_square, "Det of a non-square matrix"

        return Basic.__new__(cls, mat)

    @property
    def arg(self):
        return self.args[0]

    def doit(self, **_):
        det = self.arg._eval_determinant()
        if det is not None:
            return det
        _, n = self.arg.shape
        if n == 1:
            return self.arg[0, 0]
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

    def _latex(self, p):
        return r"\left|{%s}\right|" % p._print(self.arg)

    def _sympystr(self, p):
        return "¦%s¦" % p._print(self.arg)

    @property
    def definition(self):
        n = self.shape[0]
        from sympy import Sum, Product
        from sympy.combinatorics.permutations import Permutations, Signature
        p = self.generate_free_symbol(shape=(n,), integer=True)
        i = self.generate_free_symbol(integer=True)
        return Sum[p:Permutations(n)](Signature(p) * Product[i:n](self[i, p[i]]))


def det(matexpr):
    """ Matrix Determinant

    Examples
    ========

    >>> from sympy import MatrixSymbol, det, eye
    >>> A = MatrixSymbol('A', 3, 3)
    >>> det(A)
    Det(A)
    >>> det(eye(3))
    1
    """

    return Det(matexpr).doit()


from sympy.assumptions.ask import ask, Q
from sympy.assumptions.refine import handlers_dict


def refine_Determinant(expr, assumptions):
    """
    >>> from sympy import MatrixSymbol, Q, assuming, refine, det
    >>> X = MatrixSymbol('X', 2, 2)
    >>> det(X)
    Det(X)
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


handlers_dict['Det'] = refine_Determinant
