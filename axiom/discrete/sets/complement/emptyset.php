<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(A \\neq B\\tag*{Eq[0]}\\)\\(A \\subset B\\tag*{Eq[1]}\\)\\(B \\setminus A \\neq \\emptyset\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\exists_{B, A}{B \\setminus A = \\emptyset}\\tag*{~Eq[3]}\\)";
$txt[$i++] = "\\(\\exists_{B, A}{A \\cup B = A}\\tag*{~Eq[4]}\\)";
$txt[$i++] = "\\(B \\subset A\\tag*{~Eq[5]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
$txt[$i++] = "\\(A = B\\tag*{~Eq[6]}\\)";
$txt[$i++] = "\\(\\text{False}\\)";
render(__FILE__, $txt);
?>        

