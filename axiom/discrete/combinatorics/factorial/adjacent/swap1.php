<?php
require_once '..\..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\({w}_{j} = Swap\\left(n, 0, j\\right)\\tag*{Eq[0]}\\)\\([i:n]{x}_{{w}_{j,i} \\times [i:n]i} = [i:n]\\begin{cases} {x}_{0} & \\text{if}\\: i = j \\\\{x}_{j} & \\text{if}\\: i = 0 \\\\{x}_{i} & \\text{else} \\end{cases}\\tag*{?=>Eq[1]}\\)";
render(__FILE__, $txt);
?>        

