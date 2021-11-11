from util import MySQL
from console import compile_definition_statement

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

keywords += ['axiom',
             'base',
             'countable', 'continuous',
             'deep',
             'differentiable'
             'empty', 'etype', 'evaluate', 'expand', 'expr',
             'finite', 'finiteset',
             'generate_var',
             'index', 'infinite', 'integer', 'integrable', 'invertible',
              
             'is_complex', 'is_continuous', 'is_contable', 'is_empty', 'is_integer', 'is_integrable', 'is_invertible', 
             'is_measurable', 'is_negative', 
             'is_nonempty', 'is_nonnegative', 'is_nonpositive', 'is_nonzero', 
             'is_positive', 'is_prime', 'is_real', 'is_singular', 'is_zero',
             
             'left_open', 
             'measurable', 
             'negative', 'nonempty', 'nonnegative', 'nonpositive', 'nonzero',
             'plausible', 'positive', 'prime', 'provable', 'proved'
             'real', 'right_open',
             'set_comprehension', 'simplify', 'singular',
             'this',
             'uncountable', 
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
    
    vocab.remove('symbol')
    vocab.remove('function')
    vocab.remove('binomial')
    
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
        
        latex = []
        for line in script:
            latex.append(local_eval(compile_definition_statement(line), __locals__))
                            
        script = [s.replace('\\', r'\\').replace('"', '\\"') for s in script]
        latex = [s.replace('\\', r'\\').replace('"', '\\"') for s in latex]
        datum = (symbol, script, latex)
        print(datum)
        data.append(datum) 
            
    MySQL.instance.execute('delete from tbl_console_py')
    
    print('len(data) =', len(data))
    MySQL.instance.load_data('tbl_console_py', data)


# exec(open('./util/hint.py').read())
# update tbl_axiom_py set latex = '\\[\\color{red}{This\\ technique\\ is\\ proprietory,\\ please\\ contact\\ software\\ developer\\ for\\ details!}\\]'where axiom in ('keras.imply.eq.conv1d', 'keras.imply.eq.conv2d', 'keras.imply.eq.conv3d', 'keras.imply.eq.bert.band_part_mask', 'keras.imply.eq.bert.position_representation.relative.band_part_mask');
# delete from tbl_axiom_py where axiom in ('keras.imply.eq.conv1d', 'keras.imply.eq.conv2d', 'keras.imply.eq.conv3d', 'keras.imply.eq.bert.band_part_mask', 'keras.imply.eq.bert.position_representation.relative.band_part_mask');