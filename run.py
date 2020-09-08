# coding=utf-8

import sys
# to run this script, please install:
# pip install mpmath==1.1.0
# pip install oauthlib
if __name__ == '__main__':

    if len(sys.argv) == 1:
        from axiom.prove import prove 
        prove()
    else:
        import axiom
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

# https://store.wolfram.com/arrive.cgi?URI=/catalog/
# https://www.wolfram.com/mathematica/pricing/home-hobby/


# https://www.ginac.de/ginac.git/
# git clone git://www.ginac.de/ginac.git
# https://sourceforge.net/projects/maxima/
# http://www.mmrc.iss.ac.cn/

# http://dandelion-ecl.sourceforge.net/update/
# http://mirrors.aliyun.com/gnu/emacs/windows/emacs-27/
# http://www.gnu.org/software/emacs/download.html

# https://doc.sagemath.org/html/en/reference/index.html

