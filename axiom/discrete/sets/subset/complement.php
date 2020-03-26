<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(A \\subset B\\tag*{Eq[0]}\\)\\(\\left|{B \\setminus A}\\right| = - \\left|{A}\\right| + \\left|{B}\\right|\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\left|{B}\\right| = \\left|{B \\setminus A}\\right| + \\left|{A \\cap B}\\right|\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(0 = - \\left|{A}\\right| + \\left|{A \\cap B}\\right|\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\left|{A}\\right| = \\left|{A \\cap B}\\right|\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(A \\subset A \\cap B\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(A\\supset A \\cap B\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(A = A \\cap B\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\left|{A}\\right| = \\left|{A \\cap B}\\right|\\tag*{Eq[4]}\\)";
render(__FILE__, $txt);
?>        

