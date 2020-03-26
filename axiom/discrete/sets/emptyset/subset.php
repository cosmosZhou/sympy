<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(B \\cap C = \\emptyset\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(A \\subset B\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(A \\cap C = \\emptyset\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(A \\cap C \\subset B \\cap C\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(A \\cap C \\subset \\emptyset\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(A \\cap C\\supset \\emptyset\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(A \\cap C = \\emptyset\\tag*{Eq[2]}\\)";
render(__FILE__, $txt);
?>        

