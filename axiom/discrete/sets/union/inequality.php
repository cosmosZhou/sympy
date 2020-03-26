<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| \\leq \\left|{A}\\right| + \\left|{B}\\right|\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\left|{A}\\right| + \\left|{B}\\right| - \\left|{A \\cap B}\\right| = \\left|{A \\cup B}\\right|\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
render(__FILE__, $txt);
?>        

