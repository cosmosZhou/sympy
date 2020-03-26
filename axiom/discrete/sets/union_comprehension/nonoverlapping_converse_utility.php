<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\forall_{\\substack{j \\in \\left[0; n\\right) \\setminus \\left\\{i\\right\\}}}{{x}_{i} \\cap {x}_{j} = \\emptyset}\\tag*{Eq[0]}\\)\\(\\left|{\\bigcup\\limits_{i=0}^{n - 1} {x}_{i}}\\right| = \\sum\\limits_{i=0}^{n - 1} \\left|{{x}_{i}}\\right|\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\left|{{x}_{0} \\cup {x}_{1}}\\right| = \\left|{{x}_{0}}\\right| + \\left|{{x}_{1}}\\right|\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{j \\in \\left[0; n\\right) \\setminus \\left\\{1\\right\\}}}{{x}_{1} \\cap {x}_{j} = \\emptyset}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\({x}_{0} \\cap {x}_{1} = \\emptyset\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\left|{{x}_{0} \\cup {x}_{1}}\\right| = \\left|{{x}_{0}}\\right| + \\left|{{x}_{1}}\\right|\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\left|{\\bigcup\\limits_{i=0}^{n} {x}_{i}}\\right| = \\sum\\limits_{i=0}^{n} \\left|{{x}_{i}}\\right|\\tag*{Eq.plausible}\\)";
$txt[$i++] = "\\(\\bigcup\\limits_{i=0}^{n} {x}_{i} = {x}_{n} \\cup \\bigcup\\limits_{i=0}^{n - 1} {x}_{i}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\left|{\\bigcup\\limits_{i=0}^{n} {x}_{i}}\\right| = \\left|{{x}_{n}}\\right| - \\left|{{x}_{n} \\cap \\bigcup\\limits_{i=0}^{n - 1} {x}_{i}}\\right| + \\left|{\\bigcup\\limits_{i=0}^{n - 1} {x}_{i}}\\right|\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{0 \\le i < n}}{{x}_{i} \\cap {x}_{n} = \\emptyset}\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\({x}_{n} \\cap \\bigcup\\limits_{i=0}^{n - 1} {x}_{i} = \\emptyset\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(\\left|{\\bigcup\\limits_{i=0}^{n} {x}_{i}}\\right| = \\left|{{x}_{n}}\\right| + \\left|{\\bigcup\\limits_{i=0}^{n - 1} {x}_{i}}\\right|\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(\\left|{\\bigcup\\limits_{i=0}^{n} {x}_{i}}\\right| = \\left|{{x}_{n}}\\right| + \\sum\\limits_{i=0}^{n - 1} \\left|{{x}_{i}}\\right|\\tag*{Eq[10]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{i=0}^{n} \\left|{{x}_{i}}\\right| = \\left|{{x}_{n}}\\right| + \\sum\\limits_{i=0}^{n - 1} \\left|{{x}_{i}}\\right|\\tag*{Eq[11]}\\)";
$txt[$i++] = "\\(\\left|{\\bigcup\\limits_{i=0}^{n} {x}_{i}}\\right| = \\sum\\limits_{i=0}^{n} \\left|{{x}_{i}}\\right|\\tag*{Eq.plausible}\\)";
render(__FILE__, $txt);
?>        

