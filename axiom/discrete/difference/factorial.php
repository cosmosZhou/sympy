<?php
require_once '..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\({\\color{blue} \\Delta}_{x}^{n}\\ {x^{n}} = n!\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
$txt[$i++] = "\\({\\color{blue} \\Delta}_{x}^{n + 1}\\ {x^{n + 1}} = \\left(n + 1\\right)!\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\({\\color{blue} \\Delta}_{x}^{n}\\ {{\\color{blue} \\Delta}_{x}\\ {x^{n + 1}}} = \\left(n + 1\\right)!\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\({\\color{blue} \\Delta}_{x}^{n}\\ {\\left(- x^{n + 1} + \\left(x + 1\\right)^{n + 1}\\right)} = \\left(n + 1\\right)!\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(- x^{n + 1} + \\left(x + 1\\right)^{n + 1} = - x^{n + 1} + \\sum\\limits_{k=0}^{n + 1} x^{k} {\\binom{n + 1}{k}}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(- x^{n + 1} + \\left(x + 1\\right)^{n + 1} = \\sum\\limits_{k=0}^{n} x^{k} {\\binom{n + 1}{k}}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\({\\color{blue} \\Delta}_{x}^{n}\\ {\\sum\\limits_{k=0}^{n} x^{k} {\\binom{n + 1}{k}}} = \\left(n + 1\\right)!\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{k=0}^{n} {\\color{blue} \\Delta}_{x}^{n}\\ {x^{k}} {\\binom{n + 1}{k}} = \\left(n + 1\\right)!\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\left(n + 1\\right) {\\color{blue} \\Delta}_{x}^{n}\\ {x^{n}} + \\sum\\limits_{k=0}^{n - 1} {\\color{blue} \\Delta}_{x}^{n}\\ {x^{k}} {\\binom{n + 1}{k}} = \\left(n + 1\\right)!\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(\\left(n + 1\\right) n! + \\sum\\limits_{k=0}^{n - 1} {\\color{blue} \\Delta}_{x}^{n}\\ {x^{k}} {\\binom{n + 1}{k}} = \\left(n + 1\\right)!\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(\\left(n + 1\\right)! = \\left(n + 1\\right) n!\\tag*{Eq[10]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{k=0}^{n - 1} {\\color{blue} \\Delta}_{x}^{n}\\ {x^{k}} {\\binom{n + 1}{k}} = 0\\tag*{Eq.equation}\\)";
$txt[$i++] = "\\({\\color{blue} \\Delta}_{x}^{k}\\ {x^{k}} = k!\\tag*{Eq[11]}\\)";
$txt[$i++] = "\\({\\color{blue} \\Delta}_{x}^{- k + n}\\ {{\\color{blue} \\Delta}_{x}^{k}\\ {x^{k}}} = 0\\tag*{Eq[12]}\\)";
$txt[$i++] = "\\({\\color{blue} \\Delta}_{x}^{n}\\ {x^{k}} = 0\\tag*{Eq[13]}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{0 \\le k < n}}{{\\color{blue} \\Delta}_{x}^{n}\\ {x^{k}} = 0}\\tag*{Eq[14]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
render(__FILE__, $txt);
?>        

