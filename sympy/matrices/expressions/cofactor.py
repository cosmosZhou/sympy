from __future__ import print_function, division

from sympy.core.sympify import _sympify
from sympy.core import Basic
from sympy.matrices.expressions.matexpr import MatrixExpr


class Cofactors(MatrixExpr):
    """
    The cofactors of a matrix expression

    This is a symbolic object that simply stores its argument without
    evaluating it. To actually compute the minors, use the ``.cofactors()``
    method of matrices.

    """
    is_Cofactors = True

    def __new__(cls, mat):        
        mat = _sympify(mat)
        return Basic.__new__(cls, mat)

    @property
    def arg(self):
        return self.args[0]

    @property
    def shape(self):
        return self.arg.shape

    def to_wolfram(self, global_variables):
        from wolframclient.language import wlexpr        
        return wlexpr("Cofactors[X_] := Array[(-1)^(#1 + #2) &, Dimensions[X]] Map[Reverse, Minors[X], {0, 1}]; Cofactors[%s]" % self.arg.to_wolfram(global_variables))
    
    def doit(self, **hints):
        wolfram = hints.get("wolfram", None)
        if wolfram:
# Cofactors[mat] := SparseArray[{i_, j_} -> (-1)^(i + j), Dimensions[mat]] Map[Reverse, Minors[mat], {0, 1}]
            return self._eval_wolfram(wolfram)
        
        try:
            return self.arg.cofactor_matrix()
        except:
            return self


    @property
    def atomic_dtype(self):
        return self.arg.atomic_dtype

# Needs["Combinatorica`"]
# mat = Array[Subscript[A, ##] &, {5, 5}, 0]
# Block[{i = 3, j = 7}, 
#  Cofactor[mat, {i, j}] == 
#   Map[Reverse, Minors[mat], {0, 1}][[i, j]]*(-1)^(i + j)]