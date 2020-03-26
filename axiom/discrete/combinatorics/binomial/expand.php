<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\({\\binom{n}{k}} = \\frac{n {\\binom{n - 1}{k - 1}}}{k}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
render(__FILE__, $txt);
?>        

