<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(A \\neq \\emptyset\\tag*{Eq[0]}\\)\\(\\left|{A}\\right| \\geq 1\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\left|{A}\\right| > 0\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\exists_{A}{\\left|{A}\\right| < 1}\\tag*{~Eq[3]}\\)";
$txt[$i++] = "\\(\\exists_{A}{\\left|{A}\\right| = 0}\\tag*{~Eq[4]}\\)";
$txt[$i++] = "\\(\\text{False}\\)";
render(__FILE__, $txt);
?>        

