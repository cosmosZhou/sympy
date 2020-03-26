<?php
require_once '..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\sum\\limits_{j=0}^{n - 1} {t}_{j} = 1\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(y = \\operatorname{softmax}{\\left(x \\right)}\\tag*{Eq[1]}\\)\\(L = - t \\times \\log{y}\\tag*{Eq[2]}\\)\\(\\sum\\limits_{j=0}^{n - 1} {t}_{j} = 1\\tag*{Eq[0]}\\)\\(\\frac{d}{d x} L = - t + y\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(L = - \\sum\\limits_{j=0}^{n - 1} {t}_{j} \\log{{y}_{j}}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\frac{d}{d {x}_{i}} L = \\frac{\\partial}{\\partial {x}_{i}} \\left(- \\sum\\limits_{j=0}^{n - 1} {t}_{j} \\log{{y}_{j}}\\right)\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\frac{d}{d {x}_{i}} L = - \\sum\\limits_{j=0}^{n - 1} \\frac{{t}_{j} \\frac{\\partial}{\\partial {x}_{i}} {y}_{j}}{{y}_{j}}\\tag*{Eq.loss}\\)";
$txt[$i++] = "\\({y}_{i} = \\frac{{\\color{blue} e}^{{x}_{i}}}{\\sum\\limits_{\\substack{}} {\\color{blue} e}^{x}}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\({y}_{j} = \\frac{{\\color{blue} e}^{{x}_{j}}}{\\sum\\limits_{\\substack{}} {\\color{blue} e}^{x}}\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\frac{\\partial}{\\partial {x}_{i}} {y}_{j} = - \\frac{{\\color{blue} e}^{{x}_{i}} {\\color{blue} e}^{{x}_{j}}}{\\left(\\sum\\limits_{\\substack{}} {\\color{blue} e}^{x}\\right)^{2}} + \\frac{{\\color{blue} e}^{{x}_{j}} \\delta_{i j}}{\\sum\\limits_{\\substack{}} {\\color{blue} e}^{x}}\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(\\frac{\\frac{\\partial}{\\partial {x}_{i}} {y}_{j}}{{y}_{j}} = - {y}_{i} + \\delta_{i j}\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(\\frac{d}{d {x}_{i}} L = \\sum\\limits_{j=0}^{n - 1} {t}_{j} {y}_{i} - \\sum\\limits_{j=0}^{n - 1} {t}_{j} \\delta_{i j}\\tag*{Eq.loss}\\)";
$txt[$i++] = "\\(\\frac{d}{d {x}_{i}} L = {y}_{i} \\sum\\limits_{j=0}^{n - 1} {t}_{j} - \\sum\\limits_{j=0}^{n - 1} {t}_{j} \\delta_{i j}\\tag*{Eq.loss}\\)";
$txt[$i++] = "\\(\\frac{d}{d {x}_{i}} L = - {t}_{i} + {y}_{i} \\sum\\limits_{j=0}^{n - 1} {t}_{j}\\tag*{Eq.loss}\\)";
$txt[$i++] = "\\(\\frac{d}{d {x}_{i}} L = - {t}_{i} + {y}_{i}\\tag*{Eq.loss}\\)";
$txt[$i++] = "\\(\\frac{d}{d x} L = - t + y\\tag*{Eq[3]}\\)";
render(__FILE__, $txt);
?>        

