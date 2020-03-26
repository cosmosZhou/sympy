<?php
require_once '..\..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\left[\\begin{matrix}{n + 1}\\\\{k + 1}\\end{matrix}\\right] = \\left(n + 1\\right) \\left[\\begin{matrix}{n}\\\\{k + 1}\\end{matrix}\\right] + \\left[\\begin{matrix}{n}\\\\{k}\\end{matrix}\\right]\\tag*{?=>Eq[0]}\\)";
render(__FILE__, $txt);
?>        

