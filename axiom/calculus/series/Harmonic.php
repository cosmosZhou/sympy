<?php
require_once '..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\lim\\limits_{n \\to \\infty} \\frac{\\sum\\limits_{k=1}^{n} \\frac{1}{k}}{\\log{\\left(n + 1 \\right)}} = 1\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\lim\\limits_{x \\to x_{0}} \\frac{1}{x} = \\frac{1}{x_{0}}\\tag*{Eq.continuity}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{k \\le x_{0} \\le k + 1}}{\\lim\\limits_{x \\to x_{0}} \\frac{1}{x} = \\frac{1}{x_{0}}}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{k \\le x_{0} \\le k + 1}}{\\int\\limits_{k}^{k + 1} \\frac{1}{x}\\, dx = \\frac{1}{x_{0}}}\\tag*{Eq.mean_value_theorem}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{k \\le x_{0} \\le k + 1}}{x_{0} \\geq k}\\tag*{Eq[2]}\\)\\(\\forall_{\\substack{k \\le x_{0} \\le k + 1}}{x_{0} \\leq k + 1}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{k \\le x_{0} \\le k + 1}}{\\frac{1}{x_{0}} \\leq \\frac{1}{k}}\\tag*{Eq[4]}\\)\\(\\forall_{\\substack{k \\le x_{0} \\le k + 1}}{\\frac{1}{x_{0}} \\geq \\frac{1}{k + 1}}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\int\\limits_{k}^{k + 1} \\frac{1}{x}\\, dx \\leq \\frac{1}{k}\\tag*{Eq[6]}\\)\\(\\int\\limits_{k}^{k + 1} \\frac{1}{x}\\, dx \\geq \\frac{1}{k + 1}\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{k=1}^{n} \\int\\limits_{k}^{k + 1} \\frac{1}{x}\\, dx \\leq \\sum\\limits_{k=1}^{n} \\frac{1}{k}\\tag*{Eq[8]}\\)\\(\\sum\\limits_{k=1}^{n - 1} \\int\\limits_{k}^{k + 1} \\frac{1}{x}\\, dx \\geq \\sum\\limits_{k=1}^{n - 1} \\frac{1}{k + 1}\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(\\log{\\left(n + 1 \\right)} \\leq \\sum\\limits_{k=1}^{n} \\frac{1}{k}\\tag*{Eq[10]}\\)\\(\\sum\\limits_{k=1}^{n - 1} \\frac{1}{k + 1} \\leq \\log{n}\\tag*{Eq[11]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{k=1}^{n} \\frac{1}{k} \\leq \\log{n} + 1\\tag*{Eq[12]}\\)";
$txt[$i++] = "\\(1 \\leq \\frac{\\sum\\limits_{k=1}^{n} \\frac{1}{k}}{\\log{\\left(n + 1 \\right)}}\\tag*{Eq[13]}\\)\\(\\frac{\\sum\\limits_{k=1}^{n} \\frac{1}{k}}{\\log{\\left(n + 1 \\right)}} \\leq \\frac{\\log{n} + 1}{\\log{\\left(n + 1 \\right)}}\\tag*{Eq[14]}\\)";
$txt[$i++] = "\\(1 \\leq \\lim\\limits_{n \\to \\infty} \\frac{\\sum\\limits_{k=1}^{n} \\frac{1}{k}}{\\log{\\left(n + 1 \\right)}}\\tag*{Eq[15]}\\)\\(\\lim\\limits_{n \\to \\infty} \\frac{\\sum\\limits_{k=1}^{n} \\frac{1}{k}}{\\log{\\left(n + 1 \\right)}} \\leq 1\\tag*{Eq[16]}\\)";
$txt[$i++] = "\\(\\lim\\limits_{n \\to \\infty} \\frac{\\sum\\limits_{k=1}^{n} \\frac{1}{k}}{\\log{\\left(n + 1 \\right)}} = 1\\tag*{Eq[0]}\\)";
render(__FILE__, $txt);
?>        

