<?php
require_once '..\..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\({w}_{i,j} = Swap\\left(n, i, j\\right)\\tag*{Eq[0]}\\)\\(\\bigcup\\limits_{k=0}^{n - 1} \\left\\{{w}_{i,j,k} \\times x\\right\\} = \\left\\{*x\\right\\} \\tag*{Eq[1]}\\)";
$txt[$i++] = "\\({w}_{i,j,k} = [l:n]\\begin{cases} \\delta_{i l} & \\text{if}\\: k = j \\\\\\delta_{j l} & \\text{if}\\: k = i \\\\\\delta_{k l} & \\text{else} \\end{cases}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\({w}_{i,j,k} \\times x = [l:n]\\begin{cases} \\delta_{i l} & \\text{if}\\: k = j \\\\\\delta_{j l} & \\text{if}\\: k = i \\\\\\delta_{k l} & \\text{else} \\end{cases} \\times x\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\({w}_{i,j,k} \\times x = \\begin{cases} {x}_{i} & \\text{if}\\: k = j \\\\{x}_{j} & \\text{if}\\: k = i \\\\{x}_{k} & \\text{else} \\end{cases}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\left\\{{w}_{i,j,k} \\times x\\right\\} = \\begin{cases} \\left\\{{x}_{i}\\right\\} & \\text{if}\\: k = j \\\\\\left\\{{x}_{j}\\right\\} & \\text{if}\\: k = i \\\\\\left\\{{x}_{k}\\right\\} & \\text{else} \\end{cases}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\bigcup\\limits_{k=0}^{n - 1} \\left\\{{w}_{i,j,k} \\times x\\right\\} = \\left\\{*x\\right\\} \\tag*{Eq[1]}\\)";
render(__FILE__, $txt);
?>        

