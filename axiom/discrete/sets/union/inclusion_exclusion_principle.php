<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| = \\left|{A}\\right| + \\left|{B}\\right| - \\left|{A \\cap B}\\right|\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| = \\left|{A}\\right| + \\left|{B \\setminus A}\\right|\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\left|{B}\\right| - \\left|{A \\cap B}\\right| = \\left|{B \\setminus A}\\right|\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\left|{B}\\right| = \\left|{B \\setminus A}\\right| + \\left|{A \\cap B}\\right|\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(C = A \\cap B\\tag*{Eq.C_definition}\\)";
$txt[$i++] = "\\(D = B \\setminus A\\tag*{Eq.D_definition}\\)";
$txt[$i++] = "\\(C \\cap D = \\emptyset\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
$txt[$i++] = "\\(\\left|{C \\cup D}\\right| = \\left|{C}\\right| + \\left|{D}\\right|\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\left|{B}\\right| = \\left|{B \\setminus A}\\right| + \\left|{A \\cap B}\\right|\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(A \\cap D = \\emptyset\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
$txt[$i++] = "\\(\\left|{A \\cup D}\\right| = \\left|{A}\\right| + \\left|{D}\\right|\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| = \\left|{A}\\right| + \\left|{B \\setminus A}\\right|\\tag*{Eq[1]}\\)";
render(__FILE__, $txt);
?>        

