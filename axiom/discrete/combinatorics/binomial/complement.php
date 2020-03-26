<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\({\\binom{n}{k}} = {\\binom{n}{- k + n}}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
render(__FILE__, $txt);
?>        

