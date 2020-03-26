<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| \\geq \\left|{A}\\right|\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(A \\cup B = A \\cup \\left(B \\setminus A\\right)\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| = \\left|{A}\\right| + \\left|{B \\setminus A}\\right|\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| \\geq \\left|{A}\\right|\\tag*{Eq[0]}\\)";
render(__FILE__, $txt);
?>        

