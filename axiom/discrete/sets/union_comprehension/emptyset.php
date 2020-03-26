<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\bigcup\\limits_{i=0}^{k} {x}_{i} = \\emptyset\\tag*{Eq[0]}\\)\\(\\forall_{\\substack{0 \\le i \\le k}}{{x}_{i} = \\emptyset}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\({x}_{j} = \\emptyset\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\exists_{{x}_{j}}{{x}_{j} \\neq \\emptyset}\\tag*{~Eq.paradox}\\)";
$txt[$i++] = "\\(\\exists_{{x}_{j}}{\\left|{{x}_{j}}\\right| > 0}\\tag*{~Eq.positive}\\)";
$txt[$i++] = "\\(\\left|{\\bigcup\\limits_{i=0}^{k} {x}_{i}}\\right| = 0\\tag*{Eq.union_empty}\\)";
$txt[$i++] = "\\(\\bigcup\\limits_{i=0}^{k} {x}_{i} \\setminus {x}_{j} = \\emptyset\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\left|{\\bigcup\\limits_{i=0}^{k} {x}_{i} \\setminus {x}_{j}}\\right| = 0\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\left|{\\bigcup\\limits_{i=0}^{k} {x}_{i}}\\right| = \\left|{{x}_{j}}\\right| + \\left|{\\bigcup\\limits_{i=0}^{k} {x}_{i} \\setminus {x}_{j}}\\right|\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(0 = \\left|{{x}_{j}}\\right|\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\text{False}\\)";
render(__FILE__, $txt);
?>        

