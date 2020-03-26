<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(\\left|{\\bigcup\\limits_{i=0}^{k} {x}_{i}}\\right| = \\sum\\limits_{i=0}^{k} \\left|{{x}_{i}}\\right|\\tag*{Eq[0]}\\)\\(\\forall_{\\substack{j \\in \\left[0; k\\right] \\setminus \\left\\{i\\right\\}\\\\0 \\le i \\le k}}{{x}_{i} \\cap {x}_{j} = \\emptyset}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{j \\in \\left[0; k\\right] \\setminus \\left\\{i\\right\\}\\\\0 \\le i \\le k}}{{x}_{i} \\cap {x}_{j} \\neq \\emptyset}\\tag*{~Eq[2]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{j \\in \\left[0; k\\right] \\setminus \\left\\{i\\right\\}\\\\0 \\le i \\le k}}{\\left|{{x}_{i} \\cap {x}_{j}}\\right| > 0}\\tag*{~Eq[3]}\\)";
$txt[$i++] = "\\(\\left|{{x}_{i} \\cup {x}_{j}}\\right| = \\left|{{x}_{i}}\\right| + \\left|{{x}_{j}}\\right| - \\left|{{x}_{i} \\cap {x}_{j}}\\right|\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{j \\in \\left[0; k\\right] \\setminus \\left\\{i\\right\\}\\\\0 \\le i \\le k}}{\\left|{{x}_{i} \\cup {x}_{j}}\\right| < \\left|{{x}_{i}}\\right| + \\left|{{x}_{j}}\\right|}\\tag*{~Eq[5]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{j \\in \\left[0; k\\right] \\setminus \\left\\{i\\right\\}\\\\0 \\le i \\le k}}{- \\left|{{x}_{i} \\cup {x}_{j}}\\right| + \\left|{\\bigcup\\limits_{i=0}^{k} {x}_{i}}\\right| > - \\left|{{x}_{i}}\\right| - \\left|{{x}_{j}}\\right| + \\sum\\limits_{i=0}^{k} \\left|{{x}_{i}}\\right|}\\tag*{~Eq.strict_greater_than}\\)";
$txt[$i++] = "\\(\\bigcup\\limits_{i=0}^{k} {x}_{i} = \\bigcup\\limits_{i \\in \\left[0; k\\right] \\setminus \\left\\{i, j\\right\\}} {x}_{i} \\cup \\bigcup\\limits_{i \\in \\left[0; k\\right] \\cap \\left\\{i, j\\right\\}} {x}_{i}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\left|{\\bigcup\\limits_{i \\in \\left[0; k\\right] \\setminus \\left\\{i, j\\right\\}} {x}_{i}}\\right| \\leq \\sum\\limits_{\\substack{i \\in \\left[0; k\\right] \\setminus \\left\\{i, j\\right\\}}} \\left|{{x}_{i}}\\right|\\tag*{Eq.union_less_than}\\)";
$txt[$i++] = "\\(\\left|{\\bigcup\\limits_{i=0}^{k} {x}_{i}}\\right| \\leq \\left|{\\bigcup\\limits_{i \\in \\left[0; k\\right] \\setminus \\left\\{i, j\\right\\}} {x}_{i}}\\right| + \\left|{\\bigcup\\limits_{i \\in \\left[0; k\\right] \\cap \\left\\{i, j\\right\\}} {x}_{i}}\\right|\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{j \\in \\left[0; k\\right] \\setminus \\left\\{i\\right\\}\\\\0 \\le i \\le k}}{- \\left|{{x}_{i} \\cup {x}_{j}}\\right| + \\left|{\\bigcup\\limits_{i \\in \\left[0; k\\right] \\setminus \\left\\{i, j\\right\\}} {x}_{i}}\\right| + \\left|{\\bigcup\\limits_{i \\in \\left[0; k\\right] \\cap \\left\\{i, j\\right\\}} {x}_{i}}\\right| > - \\left|{{x}_{i}}\\right| - \\left|{{x}_{j}}\\right| + \\sum\\limits_{i=0}^{k} \\left|{{x}_{i}}\\right|}\\tag*{~Eq[8]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{j \\in \\left[0; k\\right] \\setminus \\left\\{i\\right\\}\\\\0 \\le i \\le k}}{\\left|{\\bigcup\\limits_{i \\in \\left[0; k\\right] \\setminus \\left\\{i, j\\right\\}} {x}_{i}}\\right| > - \\left|{{x}_{i}}\\right| - \\left|{{x}_{j}}\\right| + \\sum\\limits_{i=0}^{k} \\left|{{x}_{i}}\\right|}\\tag*{~Eq[9]}\\)";
$txt[$i++] = "\\(\\exists_{\\substack{j \\in \\left[0; k\\right] \\setminus \\left\\{i\\right\\}\\\\0 \\le i \\le k}}{\\sum\\limits_{\\substack{i \\in \\left[0; k\\right] \\setminus \\left\\{i, j\\right\\}}} \\left|{{x}_{i}}\\right| > - \\left|{{x}_{i}}\\right| - \\left|{{x}_{j}}\\right| + \\sum\\limits_{i=0}^{k} \\left|{{x}_{i}}\\right|}\\tag*{~Eq[10]}\\)";
$txt[$i++] = "\\(\\text{False}\\)";
render(__FILE__, $txt);
?>        

