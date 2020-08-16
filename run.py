# coding=utf-8
import axiom
import sys
# to run this script, please install:
# pip install mpmath==1.1.0
if __name__ == '__main__':

    if len(sys.argv) == 1:
        axiom.prove.prove()
    else:
        for package in sys.argv[1:]:
            package = package.replace('/', '.').replace('\\', '.')
            package = eval(package)
            ret = package.prove(package.__file__)
            if ret is False:
                print(package, 'is unproven')
            elif ret is None:
                print(package, 'is erroneous')

#     cd D:/Program Files/Wolfram Research/Mathematica/12.1/SystemFiles/Components/WolframClientForPython
#     pip install .

# export WOLFRAM_INSTALLATION_DIRECTORY=D:\Program Files\Wolfram Research\Mathematica\12.1
# https://reference.wolfram.com/language/WolframClientForPython/
# https://reference.wolfram.com/workbench/index.jsp
# https://www.wolfram.com/language/fast-introduction-for-programmers/en/
# https://www.wolfram.com/language/fast-introduction-for-programmers/en/procedures/
# https://www.wolfram.com/language/fast-introduction-for-math-students/en/
# https://www.wolfram.com/language/elementary-introduction/2nd-ed/preface.html
# https://mathworld.wolfram.com/
# https://reference.wolfram.com/language/JLink/tutorial/WritingJavaProgramsThatUseTheWolframLanguage.html

