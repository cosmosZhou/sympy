import ast, sympy
from std import __set__
from sympy import Symbol
from collections import OrderedDict
from .sympy_vars import *
from .__str__ import *
from .is_returnable import *
from ..Type import *


@__set__(ast.FunctionDef)
def sympy_expr(self, locals):
    body = self.body
    if len(body) > 1 and isinstance(If := body[0], ast.If):
        if not If.orelse:
            if If.body[-1].is_returnable:
                body, If.orelse = body[:1], body[1:]
    
    *statement, last = body
    for statement in statement:
        locals = statement.sympy_expr(locals)
    return last.sympy_expr(locals)


@__set__(ast.ClassDef)
def sympy_expr(self, locals):
    *statement, last = self.body
    for statement in statement:
        locals = statement.sympy_expr(locals)

    if isinstance(last, ast.FunctionDef) and last.name == '__new__':
        args = last.args.sympy_expr(locals)
        args['return'] = last.returns.sympy_expr(locals)
        return args
    else:
        return last.sympy_expr(locals)


@__set__(ast.If)
def sympy_expr_get_key(self, var, locals):
    if var.name in locals:
        return var.name
    if var in locals.values():
        keys = tuple((key for key, value in locals.items() if value == var))
        if len(keys) == 1:
            return keys[0]


@__set__(ast.If)
def sympy_expr_locals(self, locals, test):
    key = None
    match test:
        case sympy.Equal() | sympy.Unequal():
            var, val = test.args
            if isinstance(var, Symbol):
                ...
            elif isinstance(val, Symbol):
                var, val = val, var
            
            if var:
                key = self.sympy_expr_get_key(var, locals)

        case sympy.Element():
            var, val = test.args
            if isinstance(var, Symbol):
                key = self.sympy_expr_get_key(var, locals)
        case _:
            var = val = None
    return key, var, val


@__set__(ast.If)
def sympy_expr_if(self, locals, test):
    key, var, val = self.sympy_expr_locals(locals, test)
    if key:
        locals = OrderedDict(locals)
        match test:
            case sympy.Equal():
                locals[key] = val
            case sympy.Element():
                locals[key] = Symbol(var.name, domain=val)
            case sympy.Unequal():
                domain = var.domain
                possibleDtypes = []
                for slot in domain.__slots__:
                    dtype = getattr(domain, slot)
                    if dtype is not val:
                        possibleDtypes.append(dtype)

                if len(possibleDtypes) == 1:
                    domain, = possibleDtypes
                else:
                    domain, *possibleDtypes = possibleDtypes
                    for dtype in possibleDtypes:
                        domain |= dtype
                locals[key] = Symbol(var.name, domain=domain)

    *statement, last = self.body
    assert last.is_returnable
    for statement in statement:
        assert not statement.is_returnable
        locals = statement.sympy_expr(locals)
    return last.sympy_expr(locals)


@__set__(ast.If)
def sympy_expr_else(self, locals, test):
    key, var, val = self.sympy_expr_locals(locals, test)
    if key:
        locals = OrderedDict(locals)
        match test:
            case sympy.Equal() | sympy.Element():
                domain = var.domain
                possibleDtypes = []
                for slot in domain.__slots__:
                    dtype = getattr(domain, slot)
                    if dtype is not val:
                        possibleDtypes.append(dtype)

                if len(possibleDtypes) == 1:
                    domain, = possibleDtypes
                else:
                    domain, *possibleDtypes = possibleDtypes
                    for dtype in possibleDtypes:
                        domain |= dtype
                locals[key] = Symbol(var.name, domain=domain)

    statement = self.orelse
    for i, stmt in enumerate(statement):
        if isinstance(stmt, ast.If):
            if stmt.orelse:
                ...
            else:
                if not stmt.body[-1].is_returnable:
                    stmt.body += statement[i + 1:]
                statement, stmt.orelse = statement[:i + 1], statement[i + 1:]
                break

    *statement, last = statement
    assert last.is_returnable
    for statement in statement:
        assert not statement.is_returnable
        locals = statement.sympy_expr(locals)
    return last.sympy_expr(locals)


@__set__(ast.If)
def sympy_expr(self, locals):
    test = self.test.sympy_expr(locals)
    if not isinstance(test, sympy.Boolean):
        from .Compiler import Compiler
        __bool__ = test.domain.__bool__
        parser = Compiler(__bool__)
        parser.unindent()
        test = parser.sympy_expr(__bool__.__globals__ | {'self': test})

    return sympy.Piecewise(
        (self.sympy_expr_if(locals, test), test), 
        (self.sympy_expr_else(locals, test), True),
        evaluate=False
    )


@__set__(ast.Compare)
def right_value(self, locals):
    comparator, = self.comparators
    return comparator.sympy_expr(locals)


@__set__(ast.Compare)
def sympy_expr(self, locals):
    left = self.left.sympy_expr(locals)
    # suppose self is a comparison of the form `a == b`
    right = self.right_value(locals)
    match self.ops:
        case [ast.Is()]:
            cls = sympy.Equal
        case [ast.IsNot()]:
            cls = sympy.Unequal
        case [ast.Eq()]:
            cls = sympy.Equal
        case [ast.NotEq()]:
            cls = sympy.Unequal
        case [ast.Lt()]:
            cls = sympy.Less
        case [ast.LtE()]:
            cls = sympy.LessEqual
        case [ast.Gt()]:
            cls = sympy.Greater
        case [ast.GtE()]:
            cls = sympy.GreaterEqual
        case [ast.In()]:
            cls = sympy.Element
        case [ast.NotIn()]:
            cls = sympy.NotElement
        case _:
            raise NotImplementedError(f'Unsupported comparison {self.ops}')

    if cls.is_Relational:
        assert left.dtype == right.dtype
    else:
        assert left.dtype == right.etype
    return cls(left, right, sympify=False, evaluate=False)

@__set__(ast.arguments)
def sympy_expr(self, locals):
    return OrderedDict(
        arg.sympy_expr(locals)
        for arg in self.args
    )


@__set__(ast.arg)
def sympy_expr(self, locals):
    if annotation := self.annotation:
        annotation = annotation.sympy_expr(locals)
    return self.arg, annotation


@__set__(ast.Subscript)
def sympy_expr(self, locals):
    return self.value.sympy_expr(locals)[self.slice.sympy_expr(locals)]


@__set__(ast.Tuple)
def sympy_expr(self, locals):
    return tuple(elt.sympy_expr(locals) for elt in self.elts)


@__set__(ast.Match)
def sympy_expr(self, locals):
    subject = self.subject.sympy_expr(locals)
    conds = [case.sympy_expr(locals, subject=(self.subject, subject)) for case in self.cases]
    conds[-1] = conds[-1][0], True
    return sympy.Piecewise(*conds, evaluate=False)


@__set__(ast.Name)
def sympy_expr(self, locals):
    id = self.id
    if id not in locals:
        try:
            return eval(id)
        except NameError:
            raise CompilerError(f'Variable {id} not declared', self)
    
    return locals[id]


@__set__(ast.match_case)
def sympy_expr(self, locals, subject):
    var, val = subject
    pattern = self.pattern.sympy_expr(locals)
    match val.dtype:
        case pattern.dtype:
            if isinstance(val, Symbol) and isinstance(var, ast.Name) and var.id in locals:
                locals = OrderedDict(locals)
                locals[var.id] = pattern
            pattern = sympy.Equal(val, pattern, evaluate=False, sympify=False)
        case pattern.etype:
            if isinstance(val, Symbol) and isinstance(var, ast.Name) and var.id in locals:
                locals = OrderedDict(locals)
                locals[var.id] = Symbol(val.name, domain=pattern)
            pattern = sympy.Element(val, pattern, evaluate=False, sympify=False)

    *statement, value = self.body
    for statement in statement:
        locals = statement.sympy_expr(locals)
    
    return value.sympy_expr(locals), pattern


@__set__(ast.MatchValue)
def sympy_expr(self, locals):
    return self.value.sympy_expr(locals)


@__set__(ast.MatchClass)
def sympy_expr(self, locals):
    return self.cls.sympy_expr(locals)


@__set__(ast.Return)
def sympy_expr(self, locals):
    return self.value.sympy_expr(locals)


@__set__(ast.Attribute)
def sympy_expr(self, locals):
    value = self.value.sympy_expr(locals)
    attr = self.attr
    if isinstance(value, Symbol) and isinstance(domain := value.domain, type):
        if attr == 'args':
            assert not domain.__subclasses__()
            _Ty = domain.__mro__[1]
            for constructor in _Ty.__slots__:
                if getattr(_Ty, constructor) is domain:
                    break

            __annotations__ = _Ty.__annotations__[constructor]
            if not isinstance(__annotations__, tuple):
                __annotations__ = __annotations__,
            value = tuple(
                Symbol(f"{value}.args[{i}]", domain=_Ty if domain is Self else domain) 
                for i, domain in enumerate(__annotations__)
            )
        else:
            value = getattr(domain, self.attr)
    else:
        value = getattr(value, self.attr)
        try:
            value = sympy.sympify(value, strict=True)
        except sympy.SympifyError:
            ...
    return value


@__set__(ast.Constant)
def sympy_expr(self, locals):
    return sympy.sympify(self.value)


@__set__(ast.Assign)
def sympy_expr(self, locals):
    var, = (target.sympy_vars() for target in self.targets)
    val = self.value.sympy_expr(locals)
    locals = OrderedDict(locals)
    
    if not isinstance(val, tuple):
        val = val,
        var = var,
    for var, val in zip(var, val):
        locals[var] = val

    return locals


@__set__(ast.AugAssign)
def sympy_expr(self, locals):
    var = self.target.sympy_vars()
    val = self.value.sympy_expr(locals)
    locals = OrderedDict(locals)
    match self.op:
        case ast.Add():
            locals[var] += val
        case ast.BitAnd():
            locals[var] &= val
        case ast.BitOr():
            locals[var] |= val
        case ast.BitXor():
            locals[var] ^= val
        case ast.Div():
            locals[var] /= val
        case ast.FloorDiv():
            locals[var] //= val
        case ast.LShift():
            locals[var] <<= val
        case ast.Mod():
            locals[var] %= val
        case ast.Mult():
            locals[var] *= val
        case ast.MatMult():
            locals[var] @= val
        case ast.Pow():
            locals[var] **= val
        case ast.RShift():
            locals[var] >>= val
        case ast.Sub():
            locals[var] -= val

    return locals


@__set__(ast.AnnAssign)
def sympy_expr(self, locals):
    var = self.target.sympy_vars()
    annotation = self.annotation.sympy_expr(locals)
    val = self.value.sympy_expr(locals)
    locals = OrderedDict(locals)
    if isinstance(var, tuple):
        for var, val in zip(var, val):
            locals[var] = val
    elif annotation is type:
        locals[var] = {var: val}
    else:
        locals[var] = {var: (annotation, val)}

    return locals


@__set__(ast.UnaryOp)
def sympy_expr(self, locals):
    operand = self.operand.sympy_expr(locals)
    match self.op:
        case ast.Invert():
            return ~operand
        case ast.Not():
            return sympy.Not(operand)
        case ast.UAdd():
            return +operand
        case ast.USub():
            return -operand


@__set__(ast.BinOp)
def sympy_expr(self, locals):
    left = self.left.sympy_expr(locals)
    right = self.right.sympy_expr(locals)
    match self.op:
        case ast.Add():
            return left + right
        case ast.BitAnd():
            return left & right
        case ast.BitOr():
            return left | right
        case ast.BitXor():
            return left ^ right
        case ast.Div():
            return left / right
        case ast.FloorDiv():
            return left // right
        case ast.LShift():
            return left << right
        case ast.Mod():
            return left % right
        case ast.Mult():
            return left * right
        case ast.MatMult():
            return left @ right
        case ast.Pow():
            return left ** right
        case ast.RShift():
            return left >> right
        case ast.Sub():
            return left - right


@__set__(ast.Call)
def sympy_expr(self, locals):
    match self.func:
        case ast.Name():
            match self.func.id:
                case 'isinstance':
                    return sympy.Element(
                        self.args[0].sympy_expr(locals), 
                        self.args[1].sympy_expr(locals), 
                        sympify=False, 
                        evaluate=False
                    )
                case _:
                    return self.func.sympy_expr(locals)(*(arg.sympy_expr(locals) for arg in self.args))
        case ast.Attribute():
            return self.func.sympy_expr(locals)(*(arg.sympy_expr(locals) for arg in self.args))

class CompilerError(Exception):

    def __init__(self, message, inst):
        self.message = message
        self.lineno = inst.lineno
        self.end_lineno = inst.end_lineno
        self.col_offset = inst.col_offset
        self.end_col_offset = inst.end_col_offset
