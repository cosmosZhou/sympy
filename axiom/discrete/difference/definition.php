<?php
require_once '..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\({\\color{blue} \\Delta}_{x}^{n}\\ {f{\\left(x \\right)}} = \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{n + o} f{\\left(o + x \\right)} {\\binom{n}{o}}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
$txt[$i++] = "\\({\\color{blue} \\Delta}_{x}^{n + 1}\\ {f{\\left(x \\right)}} = \\sum\\limits_{o=0}^{n + 1} \\left(-1\\right)^{n + o + 1} f{\\left(o + x \\right)} {\\binom{n + 1}{o}}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\({\\color{blue} \\Delta}_{x}^{n}\\ {{\\color{blue} \\Delta}_{x}\\ {f{\\left(x \\right)}}} = \\sum\\limits_{o=0}^{n + 1} \\left(-1\\right)^{n + o + 1} f{\\left(o + x \\right)} {\\binom{n + 1}{o}}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\({\\color{blue} \\Delta}_{x}^{n}\\ {\\left(- f{\\left(x \\right)} + f{\\left(x + 1 \\right)}\\right)} = \\sum\\limits_{o=0}^{n + 1} \\left(-1\\right)^{n + o + 1} f{\\left(o + x \\right)} {\\binom{n + 1}{o}}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(- {\\color{blue} \\Delta}_{x}^{n}\\ {f{\\left(x \\right)}} + {\\color{blue} \\Delta}_{x}^{n}\\ {f{\\left(x + 1 \\right)}} = \\sum\\limits_{o=0}^{n + 1} \\left(-1\\right)^{n + o + 1} f{\\left(o + x \\right)} {\\binom{n + 1}{o}}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(- {\\color{blue} \\Delta}_{x}^{n}\\ {f{\\left(x \\right)}} + {\\color{blue} \\Delta}_{x}^{n}\\ {f{\\left(x + 1 \\right)}} = - \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{n + o} f{\\left(o + x \\right)} {\\binom{n}{o}} + \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{n + o} f{\\left(o + x + 1 \\right)} {\\binom{n}{o}}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{o=0}^{n + 1} \\left(-1\\right)^{n + o + 1} f{\\left(o + x \\right)} {\\binom{n + 1}{o}} = - \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{n + o} f{\\left(o + x \\right)} {\\binom{n}{o}} + \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{n + o} f{\\left(o + x + 1 \\right)} {\\binom{n}{o}}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\({\\binom{n + 1}{o}} = {\\binom{n}{o}} + {\\binom{n}{o - 1}}\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{o=0}^{n + 1} \\left(-1\\right)^{n + o + 1} \\left({\\binom{n}{o}} + {\\binom{n}{o - 1}}\\right) f{\\left(o + x \\right)} = - \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{n + o} f{\\left(o + x \\right)} {\\binom{n}{o}} + \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{n + o} f{\\left(o + x + 1 \\right)} {\\binom{n}{o}}\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(- \\sum\\limits_{o=0}^{n + 1} \\left(-1\\right)^{n} \\left(-1\\right)^{o} f{\\left(o + x \\right)} {\\binom{n}{o}} - \\sum\\limits_{o=0}^{n + 1} \\left(-1\\right)^{n} \\left(-1\\right)^{o} f{\\left(o + x \\right)} {\\binom{n}{o - 1}} = - \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{n} \\left(-1\\right)^{o} f{\\left(o + x \\right)} {\\binom{n}{o}} + \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{n} \\left(-1\\right)^{o} f{\\left(o + x + 1 \\right)} {\\binom{n}{o}}\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(- \\left(-1\\right)^{n} \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{o} f{\\left(o + x \\right)} {\\binom{n}{o}} - \\sum\\limits_{o=0}^{n + 1} \\left(-1\\right)^{n} \\left(-1\\right)^{o} f{\\left(o + x \\right)} {\\binom{n}{o - 1}} = - \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{n} \\left(-1\\right)^{o} f{\\left(o + x \\right)} {\\binom{n}{o}} + \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{n} \\left(-1\\right)^{o} f{\\left(o + x + 1 \\right)} {\\binom{n}{o}}\\tag*{Eq[10]}\\)";
$txt[$i++] = "\\(- \\sum\\limits_{o=0}^{n + 1} \\left(-1\\right)^{n} \\left(-1\\right)^{o} f{\\left(o + x \\right)} {\\binom{n}{o - 1}} = \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{n} \\left(-1\\right)^{o} f{\\left(o + x + 1 \\right)} {\\binom{n}{o}}\\tag*{Eq[11]}\\)";
$txt[$i++] = "\\(- \\left(-1\\right)^{n} \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{o + 1} f{\\left(o + x + 1 \\right)} {\\binom{n}{o}} = \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{n} \\left(-1\\right)^{o} f{\\left(o + x + 1 \\right)} {\\binom{n}{o}}\\tag*{Eq[12]}\\)";
$txt[$i++] = "\\(- \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{o + 1} f{\\left(o + x + 1 \\right)} {\\binom{n}{o}} = \\sum\\limits_{o=0}^{n} \\left(-1\\right)^{o} f{\\left(o + x + 1 \\right)} {\\binom{n}{o}}\\tag*{Eq[13]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
render(__FILE__, $txt);
?>        

