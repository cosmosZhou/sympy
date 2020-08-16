from wolframclient.language import wlexpr, wl
from wolframclient.evaluation.kernel.localsession import WolframLanguageSession
from sympy.matrices import Matrix
session = WolframLanguageSession()

def evaluateByWolfram(expr):
    expr = expr.toWolfram()
    result = session.evaluate(wlexpr(expr))
    return result

def wolfram(expr):
    
def sympify(expr):
    if isinstance(expr, tuple):
        return Matrix([*expr])
    if isinstance(expr, dict):
        return expr    
    return expr.sympify()

StringReverse = session.function(wl.StringReverse)
MinMax = session.function(wl.MinMax)
Map = session.function(wl.Map)
Range = session.function(wl.Range)
Total = session.function(wl.Total)
Limit = session.function(wl.Limit)
Divide = session.function(wl.Divide)

if __name__ == '__main__':
    
    res = Limit(wl.Divide(wlexpr('x'), wlexpr('Sin[x]')), wlexpr('x->0'))
    print(res)
    
#     cd D:/Program Files/Wolfram Research/Mathematica/12.1/SystemFiles/Components/WolframClientForPython
#     pip install .

# export WOLFRAM_INSTALLATION_DIRECTORY=D:\Program Files\Wolfram Research\Mathematica\12.1
# https://reference.wolfram.com/language/WolframClientForPython/
# https://reference.wolfram.com/workbench/index.jsp
# https://www.wolfram.com/language/fast-introduction-for-programmers/en/
# https://www.wolfram.com/language/fast-introduction-for-programmers/en/procedures/
# https://www.wolfram.com/language/fast-introduction-for-math-students/en/
# https://www.wolfram.com/language/elementary-introduction/2nd-ed/preface.html


