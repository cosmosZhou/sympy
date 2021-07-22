from util import MySQL

keywords = ['False', 'None', 'True', 
            'and', 'as', 'assert', 'abs',
            'complex',
            'break', 
            'case', 'class', 'continue', 
            'def', 'del', 'dict', 
            'elif', 'else', 'enumerate', 'eval', 'exec', 'except', 'exp',  
            'finally', 'for', 
            'if', 'import', 'in', 'isinstance', 
            'len', 'list',
            'or', 
            'raise', 'range', 'return', 
            'self', 'set', 'super', 'sqrt',
            'try', 
            'while', 'with', 
            'yield']

keywords += ['emptyset', 'etype', 'evaluate', 'expand', 'expr',
             'base',
             'deep',
             'index', 'integer', 'invertible', 'is_complex', 'is_emptyset', 'is_integer', 'is_invertible', 'is_negative', 'is_nonemptyset', 'is_nonnegative', 'is_nonpositive', 'is_nonzero', 'is_positive', 'is_prime', 'is_real', 'is_singular', 'is_zero',
             'negative', 'nonemptyset', 'nonnegative', 'nonpositive', 'nonzero',
             'plausible', 'positive', 'prime',
             'real',
             'set_comprehension', 'simplify', 'singular',
             'this',
             'zero']

sections = ['algebra', 'calculus', 'discrete', 'geometry', 'keras', 'sets', 'stats']

from sympy import *
import sympy
import re
from axiom import *

def local_eval(python, __globals__):    
    try:
        result = eval(python, __globals__)
    except SyntaxError: 
        try:
            exec(python, __globals__)
        except Exception as e:
            return str(e)
    
        return ''

    except Exception as e:
        try:
            print(e)
            e = str(e)
            return e
        except:
            return str(type(e))        
    
    try:
        if hasattr(result, "is_Basic"):
            latex = r'\[%s\]' % result.latex
        else:
            latex = str(result)    
    except Exception as e:
        print(e)
        latex = str(e)
        
    return latex
    
if __name__ == '__main__':
    vocab = keywords + sections    
    
    symbols = [symbol for symbol in sympy.__dict__ if re.match('^[A-Za-z]+$', symbol)]
    vocab += symbols

#     print(vocab)
    
    data = []
    
    print('max len = ', max(len(v) for v in vocab))
    for word in vocab:
        length = len(word)
        for i in range(1, length - 1):
            data.append((word[:i], word, 1))
    
    for key, value, *_ in data:
        print(key, '=>', value)
        
    print(len(data))
    
    MySQL.instance.execute('delete from tbl_hint_py')
    MySQL.instance.load_data('tbl_hint_py', data)
    
    from console import extract_latex
    
    data = []
    __globals__ = globals()
    for symbol in symbols:
        script = extract_latex(symbol)
        if not script:
            continue
        __locals__ = {**__globals__}
        latex = [local_eval(line, __locals__) for line in script]                
        script = [s.replace('\\', r'\\').replace('"', '\\"') for s in script]
        latex = [s.replace('\\', r'\\').replace('"', '\\"') for s in latex]
        datum = (symbol, script, latex)
        print(datum)
        data.append(datum) 
            
    MySQL.instance.execute('delete from tbl_console_py')
    MySQL.instance.load_data('tbl_console_py', data)
