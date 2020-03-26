<?php
require_once '..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(S = \\operatorname{softmax}{\\left(\\frac{Q \\times K^{\\color{red} T}}{\\sqrt{d}} \\right)} \\times V\\tag*{Eq[0]}\\)\\({S}_{0} = \\operatorname{softmax}{\\left(\\frac{{Q}_{0} \\times K^{\\color{red} T}}{\\sqrt{d}} \\right)} \\times V\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\({S}_{0} = \\operatorname{softmax}{\\left(\\frac{{Q}_{0} \\times K^{\\color{red} T}}{\\sqrt{d}} \\right)} \\times V\\tag*{Eq[1]}\\)";
render(__FILE__, $txt);
?>        

