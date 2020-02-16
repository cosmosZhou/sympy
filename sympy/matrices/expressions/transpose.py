from __future__ import print_function, division

from sympy import Basic
from sympy.functions import adjoint, conjugate

from sympy.matrices.expressions.matexpr import MatrixExpr


class Transpose(MatrixExpr):
    """
    The transpose of a matrix expression.

    This is a symbolic object that simply stores its argument without
    evaluating it. To actually compute the transpose, use the ``transpose()``
    function, or the ``.T`` attribute of matrices.

    Examples
    ========

    >>> from sympy.matrices import MatrixSymbol, Transpose
    >>> from sympy.functions import transpose
    >>> A = MatrixSymbol('A', 3, 5)
    >>> B = MatrixSymbol('B', 5, 3)
    >>> Transpose(A)
    A.T
    >>> A.T == transpose(A) == Transpose(A)
    True
    >>> Transpose(A*B)
    (A*B).T
    >>> transpose(A*B)
    B.T*A.T

    """
    is_Transpose = True

    @property
    def dtype(self):
        return self.arg.dtype.transpose()

#     def _sympystr(self, p):
#         return p.parenthesize(self.arg, 0) + ".T"
    
    def _sympystr(self, p):
        from sympy.printing.precedence import PRECEDENCE
        return "%s.T" % p.parenthesize(self.arg, PRECEDENCE["Pow"])

    def _latex(self, p): 
        from sympy.printing.precedence import precedence_traditional
        return r"%s^{\color{red} T}" % p.parenthesize(self.arg, precedence_traditional(self), True)

#     def _latex(self, p):        
#         return r"{%s}^{\color{red} T}" % p._print(self.arg)

    def doit(self, **hints):
        arg = self.arg
        if hints.get('deep', True) and isinstance(arg, Basic):
            arg = arg.doit(**hints)
        _eval_transpose = getattr(arg, '_eval_transpose', None)
        if _eval_transpose is not None:
            result = _eval_transpose()
            return result if result is not None else Transpose(arg)
        else:
            return Transpose(arg)

    @property
    def arg(self):
        return self.args[0]

    @property
    def shape(self):
        return self.arg.shape[::-1]

    def _entry(self, i, j, expand=False, **kwargs):
        return self.arg._entry(j, i, expand=expand, **kwargs)

    def _eval_adjoint(self):
        return conjugate(self.arg)

    def _eval_conjugate(self):
        return adjoint(self.arg)

    def _eval_transpose(self):
        return self.arg

    def _eval_trace(self):
        from .trace import Trace
        return Trace(self.arg)  # Trace(X.T) => Trace(X)

    def _eval_determinant(self):
        from sympy.matrices.expressions.determinant import det
        return det(self.arg)

    def _eval_derivative_matrix_lines(self, x):
        lines = self.args[0]._eval_derivative_matrix_lines(x)
        return [i.transpose() for i in lines]

    def simplifier(self):
        from sympy.core.function import Function
        from sympy.core.mul import Mul
        f = self.arg
        if isinstance(f, Function):
            return f.func(self.func(f.arg).simplifier())
        if isinstance(f, Mul):
            if len(f.args[0].shape) == 0:
                return f.func(f.args[0], self.func(f.func(*f.args[1:])).simplifier())

        return self


def transpose(expr):
    """Matrix transpose"""
    return Transpose(expr).doit(deep=False)


from sympy.assumptions.ask import ask, Q
from sympy.assumptions.refine import handlers_dict


def refine_Transpose(expr, assumptions):
    """
    >>> from sympy import MatrixSymbol, Q, assuming, refine
    >>> X = MatrixSymbol('X', 2, 2)
    >>> X.T
    X.T
    >>> with assuming(Q.symmetric(X)):
    ...     print(refine(X.T))
    X
    """
    if ask(Q.symmetric(expr), assumptions):
        return expr.arg

    return expr


handlers_dict['Transpose'] = refine_Transpose
