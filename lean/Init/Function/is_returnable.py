import ast
from std import __set__


@__set__(ast.stmt)
@property
def is_returnable(self):
    ...


@__set__(ast.Return)
@property
def is_returnable(self):
    return True


@__set__(ast.If)
@property
def is_returnable(self):
    return self.body[-1].is_returnable and self.orelse and self.orelse[-1].is_returnable


__all__ = ()