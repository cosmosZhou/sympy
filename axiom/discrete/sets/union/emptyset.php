<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(A \\cup B = \\emptyset\\tag*{Eq[0]}\\)\\(A = \\emptyset\\wedge B = \\emptyset\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\exists_{A}{A \\neq \\emptyset} \\vee \\exists_{B}{B \\neq \\emptyset}\\tag*{~Eq[2]}\\)";
$txt[$i++] = "\\(\\exists_{A}{A \\neq \\emptyset}\\tag*{~Eq.A_nonempty}\\)";
$txt[$i++] = "\\(\\exists_{B}{B \\neq \\emptyset}\\tag*{~Eq.B_nonempty}\\)";
$txt[$i++] = "\\(\\exists_{A}{\\left|{A}\\right| > 0}\\tag*{~Eq.A_positive}\\)";
$txt[$i++] = "\\(\\exists_{B}{\\left|{B}\\right| > 0}\\tag*{~Eq.B_positive}\\)";
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| = 0\\tag*{Eq.AB_union_empty}\\)";
$txt[$i++] = "\\(B \\setminus A = \\emptyset\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\left|{B \\setminus A}\\right| = 0\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| = \\left|{A}\\right| + \\left|{B \\setminus A}\\right|\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(0 = \\left|{A}\\right|\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\text{False}\\)";
$txt[$i++] = "\\(A \\setminus B = \\emptyset\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\left|{A \\setminus B}\\right| = 0\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(\\left|{A \\cup B}\\right| = \\left|{B}\\right| + \\left|{A \\setminus B}\\right|\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(0 = \\left|{B}\\right|\\tag*{Eq[10]}\\)";
$txt[$i++] = "\\(\\text{False}\\)";
$txt[$i++] = "\\(\\forall_{A}{A = \\emptyset}\\tag*{Eq[11]}\\)";
$txt[$i++] = "\\(\\forall_{B}{B = \\emptyset}\\tag*{Eq[12]}\\)";
$txt[$i++] = "\\(A = \\emptyset\\wedge B = \\emptyset\\tag*{Eq[1]}\\)";
render(__FILE__, $txt);
?>        

