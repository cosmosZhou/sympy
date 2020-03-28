<?php
require_once '..\..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\({w}_{j} = Swap\\left(n, 0, j\\right)\\tag*{Eq[0]}\\)\\({x}_{{w}_{j,i} \\times [i]i} = \\begin{cases} {x}_{0} & \\text{if}\\: i = j \\\\{x}_{j} & \\text{if}\\: i = 0 \\\\{x}_{i} & \\text{else} \\end{cases}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\({w}_{j,i} = [k:n]\\begin{cases} \\delta_{0 k} & \\text{if}\\: i = j \\\\\\delta_{j k} & \\text{if}\\: i = 0 \\\\\\delta_{i k} & \\text{else} \\end{cases}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\({w}_{j,i} \\times [i]i = [k:n]\\begin{cases} \\delta_{0 k} & \\text{if}\\: i = j \\\\\\delta_{j k} & \\text{if}\\: i = 0 \\\\\\delta_{i k} & \\text{else} \\end{cases} \\times [i]i\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\({w}_{j,i} \\times [i]i = \\begin{cases} 0 & \\text{if}\\: i = j \\\\j & \\text{if}\\: i = 0 \\\\i & \\text{else} \\end{cases}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\({x}_{{w}_{j,i} \\times [i]i} = \\begin{cases} {x}_{0} & \\text{if}\\: i = j \\\\{x}_{j} & \\text{if}\\: i = 0 \\\\{x}_{i} & \\text{else} \\end{cases}\\tag*{Eq[1]}\\)";
render(__FILE__, $txt);
?>        

