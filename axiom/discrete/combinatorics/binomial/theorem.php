<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\left(x + y\\right)^{n} = \\sum\\limits_{k=0}^{n} x^{k} y^{- k + n} {\\binom{n}{k}}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\left(x + y\\right)^{n + 1} = \\sum\\limits_{k=0}^{n + 1} x^{k} y^{- k + n + 1} {\\binom{n + 1}{k}}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\left(x + y\\right)^{n + 1} = \\left(x + y\\right) \\sum\\limits_{k=0}^{n} x^{k} y^{- k + n} {\\binom{n}{k}}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{k=0}^{n + 1} x^{k} y^{- k + n + 1} {\\binom{n + 1}{k}} = \\left(x + y\\right) \\sum\\limits_{k=0}^{n} x^{k} y^{- k + n} {\\binom{n}{k}}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{k=0}^{n + 1} x^{k} y^{- k + n + 1} {\\binom{n + 1}{k}} = \\sum\\limits_{k=0}^{n} x^{k} y^{- k + n} \\left(x + y\\right) {\\binom{n}{k}}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{k=0}^{n + 1} x^{k} y^{- k + n + 1} {\\binom{n + 1}{k}} = \\sum\\limits_{k=0}^{n} \\left(x x^{k} y^{- k} y^{n} {\\binom{n}{k}} + x^{k} y y^{- k} y^{n} {\\binom{n}{k}}\\right)\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{k=0}^{n + 1} x^{k} y^{- k + n + 1} {\\binom{n + 1}{k}} = \\sum\\limits_{k=0}^{n} \\left(x^{k} y^{- k + n + 1} {\\binom{n}{k}} + x^{k + 1} y^{- k + n} {\\binom{n}{k}}\\right)\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{k=0}^{n + 1} x^{k} y^{- k + n + 1} {\\binom{n + 1}{k}} = \\sum\\limits_{k=0}^{n} x^{k} y^{- k + n + 1} {\\binom{n}{k}} + \\sum\\limits_{k=0}^{n} x^{k + 1} y^{- k + n} {\\binom{n}{k}}\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{k=0}^{n + 1} x^{k} y^{- k + n + 1} {\\binom{n + 1}{k}} = \\sum\\limits_{k=0}^{n} x^{k} y^{- k + n + 1} {\\binom{n}{k}} + \\sum\\limits_{k=1}^{n + 1} x^{k} y^{- k + n + 1} {\\binom{n}{k - 1}}\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{k=0}^{n + 1} x^{k} y^{- k + n + 1} \\left({\\binom{n}{k}} + {\\binom{n}{k - 1}}\\right) = \\sum\\limits_{k=0}^{n} x^{k} y^{- k + n + 1} {\\binom{n}{k}} + \\sum\\limits_{k=1}^{n + 1} x^{k} y^{- k + n + 1} {\\binom{n}{k - 1}}\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
render(__FILE__, $txt);
?>        

