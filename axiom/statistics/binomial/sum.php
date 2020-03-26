<?php
require_once '..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(Density\\left({\\color{red} {x_{0}}} + {\\color{red} {x_{1}}}\\right)\\left(y \\right) = p^{y} \\left(1 - p\\right)^{n_{0} + n_{1} - y} {\\binom{n_{0} + n_{1}}{y}}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(Density\\left({\\color{red} {x_{0}}} + {\\color{red} {x_{1}}}\\right)\\left(y \\right) = \\sum\\limits_{x_{1}=0}^{n_{1}} p^{x_{1}} \\left(1 - p\\right)^{n_{1} - x_{1}} {\\binom{n_{1}}{x_{1}}} \\sum\\limits_{x_{0}=0}^{n_{0}} p^{x_{0}} \\left(1 - p\\right)^{n_{0} - x_{0}} \\delta_{y, x_{0} + x_{1}} {\\binom{n_{0}}{x_{0}}}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(Density\\left({\\color{red} {x_{0}}} + {\\color{red} {x_{1}}}\\right)\\left(y \\right) = \\sum\\limits_{x_{1}=\\max\\left(0, - n_{0} + y\\right)}^{\\min\\left(n_{1}, y\\right)} p^{x_{1}} p^{- x_{1} + y} \\left(1 - p\\right)^{n_{1} - x_{1}} \\left(1 - p\\right)^{n_{0} + x_{1} - y} {\\binom{n_{0}}{- x_{1} + y}} {\\binom{n_{1}}{x_{1}}}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(Density\\left({\\color{red} {x_{0}}} + {\\color{red} {x_{1}}}\\right)\\left(y \\right) = p^{y} \\left(1 - p\\right)^{n_{0} + n_{1} - y} \\sum\\limits_{x_{1}=\\max\\left(0, - n_{0} + y\\right)}^{\\min\\left(n_{1}, y\\right)} {\\binom{n_{0}}{- x_{1} + y}} {\\binom{n_{1}}{x_{1}}}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\({\\binom{n_{0} + n_{1}}{y}} = \\sum\\limits_{x_{1}=\\max\\left(0, - n_{0} + y\\right)}^{\\min\\left(n_{1}, y\\right)} {\\binom{n_{0}}{- x_{1} + y}} {\\binom{n_{1}}{x_{1}}}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\left(p + 1\\right)^{n_{0}} = \\sum\\limits_{k=0}^{n_{0}} p^{k} {\\binom{n_{0}}{k}}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\left(p + 1\\right)^{n_{1}} = \\sum\\limits_{k=0}^{n_{1}} p^{k} {\\binom{n_{1}}{k}}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\left(p + 1\\right)^{n_{0}} \\left(p + 1\\right)^{n_{1}} = \\left(\\sum\\limits_{k=0}^{n_{0}} p^{k} {\\binom{n_{0}}{k}}\\right) \\sum\\limits_{k=0}^{n_{1}} p^{k} {\\binom{n_{1}}{k}}\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\left(p + 1\\right)^{n_{0} + n_{1}} = \\left(\\sum\\limits_{k=0}^{n_{0}} p^{k} {\\binom{n_{0}}{k}}\\right) \\sum\\limits_{k=0}^{n_{1}} p^{k} {\\binom{n_{1}}{k}}\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(\\left(\\sum\\limits_{k=0}^{n_{0}} p^{k} {\\binom{n_{0}}{k}}\\right) \\sum\\limits_{k=0}^{n_{1}} p^{k} {\\binom{n_{1}}{k}} = \\sum\\limits_{k=0}^{n_{0} + n_{1}} p^{k} {\\binom{n_{0} + n_{1}}{k}}\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{\\substack{0 \\leq k \\leq n_{0}\\\\0 \\leq l \\leq n_{1}}} p^{k + l} {\\binom{n_{0}}{k}} {\\binom{n_{1}}{l}} = \\sum\\limits_{k=0}^{n_{0} + n_{1}} p^{k} {\\binom{n_{0} + n_{1}}{k}}\\tag*{Eq[10]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{\\substack{l \\leq k \\leq l + n_{0}\\\\0 \\leq l \\leq n_{1}}} p^{k} {\\binom{n_{0}}{k - l}} {\\binom{n_{1}}{l}} = \\sum\\limits_{k=0}^{n_{0} + n_{1}} p^{k} {\\binom{n_{0} + n_{1}}{k}}\\tag*{Eq[11]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{k=0}^{n_{0} + n_{1}} p^{k} \\sum\\limits_{l=\\max\\left(0, k - n_{0}\\right)}^{\\min\\left(k, n_{1}\\right)} {\\binom{n_{0}}{k - l}} {\\binom{n_{1}}{l}} = \\sum\\limits_{k=0}^{n_{0} + n_{1}} p^{k} {\\binom{n_{0} + n_{1}}{k}}\\tag*{Eq[12]}\\)";
$txt[$i++] = "\\([k:n_{0} + n_{1} + 1]\\sum\\limits_{l=\\max\\left(0, k - n_{0}\\right)}^{\\min\\left(k, n_{1}\\right)} {\\binom{n_{0}}{k - l}} {\\binom{n_{1}}{l}} = [k:n_{0} + n_{1} + 1]{\\binom{n_{0} + n_{1}}{k}}\\tag*{Eq[13]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
render(__FILE__, $txt);
?>        

