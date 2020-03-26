<?php
require_once '..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\frac{\\sqrt{2} \\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- \\frac{x^{2}}{2}}\\, dx}{2 \\sqrt{\\pi}} = 1\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- \\frac{x^{2}}{2}}\\, dx = \\sqrt{2} \\sqrt{\\pi}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\left(\\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- \\frac{x^{2}}{2}}\\, dx\\right) \\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- \\frac{y^{2}}{2}}\\, dy = 2 \\pi\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\int\\limits_{-\\infty}^{\\infty}\\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- \\frac{x^{2}}{2} - \\frac{y^{2}}{2}}\\, dx\\, dy = 2 \\pi\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\int\\limits_{- \\pi}^{\\pi}\\int\\limits_{0}^{\\infty} \\rho {\\color{blue} e}^{- \\frac{\\rho^{2}}{2}}\\, d\\rho\\, d\\theta = 2 \\pi\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
$txt[$i++] = "\\(\\left(\\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- \\frac{x^{2}}{2}}\\, dx\\right)^{2} = 2 \\pi\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- \\frac{x^{2}}{2}}\\, dx = \\sqrt{2} \\sqrt{\\pi}\\tag*{Eq[1]}\\)";
render(__FILE__, $txt);
?>        

