<?php
require_once '..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- a x^{2} - b x - c}\\, dx = \\frac{\\sqrt{\\pi} {\\color{blue} e}^{- c + \\frac{b^{2}}{4 a}}}{\\sqrt{a}}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\({\\color{blue} e}^{- c} {\\color{blue} e}^{\\frac{b^{2}}{4 a}} \\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- a x^{2}}\\, dx = \\frac{\\sqrt{\\pi} {\\color{blue} e}^{- c + \\frac{b^{2}}{4 a}}}{\\sqrt{a}}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- a x^{2}}\\, dx = \\frac{\\sqrt{\\pi}}{\\sqrt{a}}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\frac{\\sqrt{2} \\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- \\frac{x^{2}}{2}}\\, dx}{2 \\sqrt{\\pi}} = 1\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- \\frac{x^{2}}{2}}\\, dx = \\sqrt{2} \\sqrt{\\pi}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\sqrt{a} \\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- a x^{2}}\\, dx = \\sqrt{\\pi}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- a x^{2}}\\, dx = \\frac{\\sqrt{\\pi}}{\\sqrt{a}}\\tag*{Eq[2]}\\)";
render(__FILE__, $txt);
?>        

