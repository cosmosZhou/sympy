from wolframclient.language import wlexpr
from wolframclient.evaluation.kernel.localsession import WolframLanguageSession
session = WolframLanguageSession()

def evaluateByWolfram(expr):
    expr = expr.toWolfram()
    result = session.evaluate(wlexpr(expr))
    return result


