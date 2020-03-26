<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| = \\left|{A}\\right| + \\left|{B}\\right|\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| = \\left|{A}\\right| + \\left|{B}\\right|\\tag*{Eq[0]}\\)\\(A \\cap B = \\emptyset\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| = \\left|{A}\\right| + \\left|{B}\\right| - \\left|{A \\cap B}\\right|\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(0 = \\left|{A \\cap B}\\right|\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(A \\cap B = \\emptyset\\tag*{Eq[1]}\\)";
render(__FILE__, $txt);
?>        

