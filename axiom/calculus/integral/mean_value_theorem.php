<?php
require_once '..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\forall_{\\substack{a \\le \\xi \\le b}}{\\lim\\limits_{z \\to \\xi} f{\\left(z \\right)} = f{\\left(\\xi \\right)}}\\tag*{Eq[0]}\\)\\(\\exists_{\\substack{a \\le \\xi \\le b}}{\\int\\limits_{a}^{b} f{\\left(z \\right)}\\, dz = \\left(- a + b\\right) f{\\left(\\xi \\right)}}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(m = \\min\\limits_{a \\leq z \\leq b} f{\\left(z \\right)}\\tag*{Eq.min}\\)";
$txt[$i++] = "\\(M = \\max\\limits_{a \\leq z \\leq b} f{\\left(z \\right)}\\tag*{Eq.max}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{\\min\\limits_{a \\leq z \\leq b} f{\\left(z \\right)} \\le y \\le \\max\\limits_{a \\leq z \\leq b} f{\\left(z \\right)}}}{\\exists_{\\substack{a \\le z \\le b}}{f{\\left(z \\right)} = y}}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{m \\le y \\le M}}{\\exists_{\\substack{a \\le z \\le b}}{f{\\left(z \\right)} = y}}\\tag*{Eq.intermediate_value}\\)";
$txt[$i++] = "\\(m \\leq - \\frac{\\int\\limits_{a}^{b} f{\\left(z \\right)}\\, dz}{a - b}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(M \\geq - \\frac{\\int\\limits_{a}^{b} f{\\left(z \\right)}\\, dz}{a - b}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(- \\frac{\\int\\limits_{a}^{b} f{\\left(z \\right)}\\, dz}{a - b} \\in \\left[m, M\\right]\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(- \\frac{\\int\\limits_{a}^{b} f{\\left(z \\right)}\\, dz}{a - b} \\not\\in \\left[m, M\\right] \\vee \\exists_{\\substack{a \\le z \\le b}}{f{\\left(z \\right)} = - \\frac{\\int\\limits_{a}^{b} f{\\left(z \\right)}\\, dz}{a - b}}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(- \\frac{\\int\\limits_{a}^{b} f{\\left(z \\right)}\\, dz}{a - b} \\in \\left[m, M\\right]\\wedge \\exists_{\\substack{a \\le z \\le b}}{f{\\left(z \\right)} = - \\frac{\\int\\limits_{a}^{b} f{\\left(z \\right)}\\, dz}{a - b}}\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(- \\frac{\\int\\limits_{a}^{b} f{\\left(z \\right)}\\, dz}{a - b} \\in \\left[m, M\\right]\\tag*{Eq[5]}\\)\\(\\exists_{\\substack{a \\le z \\le b}}{f{\\left(z \\right)} = - \\frac{\\int\\limits_{a}^{b} f{\\left(z \\right)}\\, dz}{a - b}}\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{a \\le z \\le b}}{\\left(- a + b\\right) f{\\left(z \\right)} = - \\frac{\\left(- a + b\\right) \\int\\limits_{a}^{b} f{\\left(z \\right)}\\, dz}{a - b}}\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{a \\le z \\le b}}{\\int\\limits_{a}^{b} f{\\left(z \\right)}\\, dz = \\left(- a + b\\right) f{\\left(z \\right)}}\\tag*{Eq[10]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{a \\le z \\le b}}{\\int\\limits_{a}^{b} f{\\left(z \\right)}\\, dz = \\left(- a + b\\right) f{\\left(z \\right)}}\\tag*{Eq[10]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{a \\le z \\le b}}{\\int\\limits_{a}^{b} f{\\left(z \\right)}\\, dz = \\left(- a + b\\right) f{\\left(z \\right)}}\\tag*{Eq[10]}\\)";
render(__FILE__, $txt);
?>        

