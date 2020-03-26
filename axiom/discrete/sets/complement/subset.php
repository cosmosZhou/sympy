<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(B \\cap C = \\emptyset\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(A \\subset B\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(C \\setminus A = C\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(A \\cap C = \\emptyset\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(C \\setminus A = C\\tag*{Eq[2]}\\)";
render(__FILE__, $txt);
?>        

