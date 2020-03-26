<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\forall_{\\substack{1 \\le j < n\\\\x \\in S}}{[i:n]\\begin{cases} {x}_{0} & \\text{if}\\: i = j \\\\{x}_{j} & \\text{if}\\: i = 0 \\\\{x}_{i} & \\text{else} \\end{cases} \\in S}\\tag*{Eq[0]}\\)\\(\\forall_{\\substack{x \\in S}}{\\left|{\\left\\{*x\\right\\} }\\right| = n}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\left|{S}\\right| = \\left|{\\left\\{\\left. \\left\\{*x\\right\\}  \\right| x \\in S \\right\\}}\\right| n!\\tag*{?=>Eq[2]}\\)";
render(__FILE__, $txt);
?>        

