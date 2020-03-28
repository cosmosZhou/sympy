<?php
require_once '..\..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\({w}_{i,j} = Swap\\left(n, i, j\\right)\\tag*{Eq[0]}\\)\\(\\forall_{\\substack{1 \\le j < n\\\\x \\in S}}{[i:n]\\begin{cases} {x}_{0} & \\text{if}\\: i = j \\\\{x}_{j} & \\text{if}\\: i = 0 \\\\{x}_{i} & \\text{else} \\end{cases} \\in S}\\tag*{Eq[1]}\\)\\(\\forall_{\\substack{0 \\le i < n\\\\0 \\le j < n}}{[k:n]{x}_{{w}_{i,j,k} \\times [k:n]k} \\in S}\\tag*{Eq[1]=>Eq[2]}\\)";
render(__FILE__, $txt);
?>        

