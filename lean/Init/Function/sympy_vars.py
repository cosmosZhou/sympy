import ast
from std import __set__


@__set__(ast.Name)
def sympy_vars(self):
    return self.id


@__set__(ast.Tuple)
def sympy_vars(self):
    return tuple(var.sympy_vars() for var in self.elts)


__all__ = ()