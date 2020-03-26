<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(A = B\\tag*{Eq[0]}\\)\\(A\\supset B\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\exists_{B, A}{A\\not\\supset B}\\tag*{~Eq[2]}\\)";
$txt[$i++] = "\\(\\text{False}\\)";
render(__FILE__, $txt);
?>        

