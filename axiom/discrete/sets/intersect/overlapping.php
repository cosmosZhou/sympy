<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(A \\cap B \\neq \\emptyset\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{a \\in B}}{a \\in A}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\exists_{a}{a \\in A \\cap B} \\vee A \\cap B = \\emptyset\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\exists_{a}{a \\in A \\cap B}\\wedge A \\cap B \\neq \\emptyset\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\exists_{a}{a \\in A \\cap B}\\tag*{Eq[4]}\\)\\(A \\cap B \\neq \\emptyset\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\exists_{a}{a \\in A}\\tag*{Eq[5]}\\)\\(\\exists_{a}{a \\in B}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\text{False}\\)";
render(__FILE__, $txt);
?>        

