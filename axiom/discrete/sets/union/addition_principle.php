<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(A \\cap B = \\emptyset\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| = \\left|{A}\\right| + \\left|{B}\\right|\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(C = A \\cup B\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(D = A \\setminus B\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(A \\cup D = A\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(B \\cup D = A \\cup B\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(A \\setminus B = A\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\left|{A \\setminus B}\\right| = \\left|{A}\\right|\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| = \\left|{B}\\right| + \\left|{A \\setminus B}\\right|\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(- \\left|{B}\\right| + \\left|{A \\cup B}\\right| = \\left|{A \\setminus B}\\right|\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| = \\left|{B}\\right| + \\left|{A \\setminus B}\\right|\\tag*{Eq[8]}\\)";
render(__FILE__, $txt);
?>        

