<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\forall_{\\substack{j \\in \\left[0; n\\right) \\setminus \\left\\{i\\right\\}\\\\0 \\le i < n}}{{x}_{i} \\cap {x}_{j} = \\emptyset}\\tag*{Eq[0]}\\)\\(\\left|{\\bigcup\\limits_{i=0}^{n - 1} {x}_{i}}\\right| = \\sum\\limits_{i=0}^{n - 1} \\left|{{x}_{i}}\\right|\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(y = [i]\\begin{cases} {x}_{i} & \\text{if}\\: i < n \\\\\\emptyset & \\text{else} \\end{cases}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\({y}_{i} = \\begin{cases} {x}_{i} & \\text{if}\\: i < n \\\\\\emptyset & \\text{else} \\end{cases}\\tag*{Eq.y_definition}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{0 \\le i < n}}{{y}_{i} = {x}_{i}}\\tag*{Eq.yi_definition}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{0 \\le i < n}}{{x}_{i} = {y}_{i}}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{j \\in \\left[0; n\\right) \\setminus \\left\\{i\\right\\}\\\\0 \\le i < n}}{{y}_{i} \\cap {y}_{j} = \\emptyset}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{i \\ge n}}{{y}_{i} = \\emptyset}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{j \\in \\left[0; n\\right) \\setminus \\left\\{i\\right\\}\\\\i \\ge n}}{{y}_{i} \\cap {y}_{j} = \\emptyset}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{j \\in \\left[0; n\\right) \\setminus \\left\\{i\\right\\}}}{{y}_{i} \\cap {y}_{j} = \\emptyset}\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\left|{\\bigcup\\limits_{i=0}^{n - 1} {y}_{i}}\\right| = \\sum\\limits_{i=0}^{n - 1} \\left|{{y}_{i}}\\right|\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(\\left|{\\bigcup\\limits_{i=0}^{n - 1} {x}_{i}}\\right| = \\sum\\limits_{i=0}^{n - 1} \\left|{{x}_{i}}\\right|\\tag*{Eq[1]}\\)";
render(__FILE__, $txt);
?>        

