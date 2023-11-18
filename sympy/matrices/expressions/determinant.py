from sympy import Basic, Expr, S, sympify
from sympy.core.cache import cacheit


class Determinant(Expr):
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

    def __new__(cls, mat, evaluate=False):
        mat = sympify(mat)
        if not mat.shape:
            return mat
        
        assert mat.is_square, "Det of a non-square matrix"
        return Basic.__new__(cls, mat)

    @property
    def arg(self):
        return self.args[0]

    def doit(self, **kwargs):
        if kwargs.get('deep'):
            arg = self.arg.doit(deep=True)
            if arg != self.arg:
                return self.func(arg).doit()
            
        det = self.arg._eval_determinant(**kwargs)
        if det is not None:
            return det
        _, n = self.arg.shape
        if n == 1:
            return self.arg[0, 0]
        return self

    def _eval_shape(self):
        return ()

    @property
    def dtype(self):
        return self.arg.dtype

    def simplify(self, deep=False, **kwargs):
        if deep:
            this = Expr.simplify(self, deep=True, **kwargs)
            if this is not self:
                return this

        matrix = self.arg
        if matrix.is_DenseMatrix:
            if len(matrix._args) == 1:
                return matrix._args[0]
        elif matrix.is_Transpose:
            return self.func(matrix.arg)
            
        return self

    def _latex(self, p):
        return r"\left|{%s}\right|" % p._print(self.arg)

    def _sympystr(self, p):
        return "det(%s)" % p._print(self.arg)

    @cacheit
    def _eval_domain_defined(self, x, **_):
        domain = Expr._eval_domain_defined(self, x)
        for arg in self.args:
            domain &= arg.domain_defined(x)
        return domain

    def _eval_Eq(self, other):
        if other.is_zero:
            X = self.arg
            if X.is_singular == True:
                return S.true
            
            if X.is_singular == False:
                return S.false

Det = Determinant

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
