import ast, astor
from std import __set__


@__set__(ast.AST)
def __repr__(self):
    return str(self)


@__set__(ast.AST)
def __str__(self):
    return astor.to_source(self)


__all__ = ()