<?php
require_once '..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin^{n - 1} {x}\\, dx = \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2}\\right)}{2 \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right)}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin {x} \\sin^{n} {x}\\, dx = \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2} + 1\\right)}{2 \\Gamma\\left(\\frac{n}{2} + \\frac{3}{2}\\right)}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(n \\int\\limits_{0}^{\\frac{\\pi}{2}} \\frac{\\sin^{n} {x} \\cos^{2} {x}}{\\sin {x}}\\, dx = \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2} + 1\\right)}{2 \\Gamma\\left(\\frac{n}{2} + \\frac{3}{2}\\right)}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(n \\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin^{n - 1} {x} \\cos^{2} {x}\\, dx = \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2} + 1\\right)}{2 \\Gamma\\left(\\frac{n}{2} + \\frac{3}{2}\\right)}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(- \\int\\limits_{0}^{\\frac{\\pi}{2}} \\frac{\\sin^{n} {x} \\cos^{2} {x}}{\\sin {x}}\\, dx + \\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin^{n - 1} {x}\\, dx = \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2}\\right)}{2 \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right)} - \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2} + 1\\right)}{2 n \\Gamma\\left(\\frac{n}{2} + \\frac{3}{2}\\right)}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\left(\\sin^{n - 1} {x} - \\frac{\\sin^{n} {x} \\cos^{2} {x}}{\\sin {x}}\\right)\\, dx = \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2}\\right)}{2 \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right)} - \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2} + 1\\right)}{2 n \\Gamma\\left(\\frac{n}{2} + \\frac{3}{2}\\right)}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin {x} \\sin^{n} {x}\\, dx = \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2}\\right)}{2 \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right)} - \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2} + 1\\right)}{2 n \\Gamma\\left(\\frac{n}{2} + \\frac{3}{2}\\right)}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin^{n + 1} {x}\\, dx = \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2}\\right)}{2 \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right)} - \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2} + 1\\right)}{2 n \\Gamma\\left(\\frac{n}{2} + \\frac{3}{2}\\right)}\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2}\\right)}{2 \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right)} - \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2} + 1\\right)}{2 n \\Gamma\\left(\\frac{n}{2} + \\frac{3}{2}\\right)} = \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2} + 1\\right)}{2 \\Gamma\\left(\\frac{n}{2} + \\frac{3}{2}\\right)}\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(\\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2}\\right)}{2 \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right)} - \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2}\\right)}{2 n \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right) + 2 \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right)} = \\frac{\\sqrt{\\pi} n \\Gamma\\left(\\frac{n}{2}\\right)}{2 n \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right) + 2 \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right)}\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(\\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2}\\right)}{2 \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right)} = \\frac{\\sqrt{\\pi} n \\Gamma\\left(\\frac{n}{2}\\right)}{2 n \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right) + 2 \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right)} + \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{n}{2}\\right)}{2 n \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right) + 2 \\Gamma\\left(\\frac{n}{2} + \\frac{1}{2}\\right)}\\tag*{Eq[10]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
render(__FILE__, $txt);
?>        

