<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\({\\binom{n}{k}} = {\\binom{n - 1}{k}} + {\\binom{n - 1}{k - 1}}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
render(__FILE__, $txt);
?>        

