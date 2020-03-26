<?php
require_once '..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(Density\\left({\\color{red} {x_{0}}} + {\\color{red} {x_{1}}}\\right)\\left(y \\right) = \\frac{\\left(\\lambda_{0} + \\lambda_{1}\\right)^{y} {\\color{blue} e}^{- \\lambda_{0} - \\lambda_{1}}}{y!}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(Density\\left({\\color{red} {x_{0}}} + {\\color{red} {x_{1}}}\\right)\\left(y \\right) = {\\color{blue} e}^{- \\lambda_{0}} {\\color{blue} e}^{- \\lambda_{1}} \\sum\\limits_{x_{1}=0}^{\\infty} \\frac{\\lambda_{1}^{x_{1}} \\sum\\limits_{x_{0}=0}^{\\infty} \\frac{\\lambda_{0}^{x_{0}} \\delta_{y, x_{0} + x_{1}}}{x_{0}!}}{x_{1}!}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(Density\\left({\\color{red} {x_{0}}} + {\\color{red} {x_{1}}}\\right)\\left(y \\right) = {\\color{blue} e}^{- \\lambda_{0}} {\\color{blue} e}^{- \\lambda_{1}} \\sum\\limits_{x_{1}=0}^{y} \\frac{\\lambda_{0}^{- x_{1} + y} \\lambda_{1}^{x_{1}}}{x_{1}! \\left(- x_{1} + y\\right)!}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\frac{\\left(\\lambda_{0} + \\lambda_{1}\\right)^{y} {\\color{blue} e}^{- \\lambda_{0} - \\lambda_{1}}}{y!} = {\\color{blue} e}^{- \\lambda_{0}} {\\color{blue} e}^{- \\lambda_{1}} \\sum\\limits_{x_{1}=0}^{y} \\frac{\\lambda_{0}^{- x_{1} + y} \\lambda_{1}^{x_{1}}}{x_{1}! \\left(- x_{1} + y\\right)!}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\frac{\\left(\\lambda_{0} + \\lambda_{1}\\right)^{y}}{y!} = \\sum\\limits_{x_{1}=0}^{y} \\frac{\\lambda_{0}^{- x_{1} + y} \\lambda_{1}^{x_{1}}}{x_{1}! \\left(- x_{1} + y\\right)!}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\left(\\lambda_{0} + \\lambda_{1}\\right)^{y} = y! \\sum\\limits_{x_{1}=0}^{y} \\frac{\\lambda_{0}^{- x_{1} + y} \\lambda_{1}^{x_{1}}}{x_{1}! \\left(- x_{1} + y\\right)!}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\left(\\lambda_{0} + \\lambda_{1}\\right)^{y} = \\sum\\limits_{k=0}^{y} \\lambda_{0}^{k} \\lambda_{1}^{- k + y} {\\binom{y}{k}}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(y! \\sum\\limits_{x_{1}=0}^{y} \\frac{\\lambda_{0}^{- x_{1} + y} \\lambda_{1}^{x_{1}}}{x_{1}! \\left(- x_{1} + y\\right)!} = \\sum\\limits_{k=0}^{y} \\lambda_{0}^{k} \\lambda_{1}^{- k + y} {\\binom{y}{k}}\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
render(__FILE__, $txt);
?>        

