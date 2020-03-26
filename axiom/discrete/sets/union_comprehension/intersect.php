<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(A \\cap \\bigcup\\limits_{i=0}^{k} {x}_{i} = \\emptyset\\tag*{Eq[0]}\\)\\(\\forall_{\\substack{0 \\le i \\le k}}{A \\cap {x}_{i} = \\emptyset}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(A \\cap {x}_{i} = \\emptyset\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\bigcup\\limits_{i=0}^{k} A \\cap {x}_{i} = A \\cap \\bigcup\\limits_{i=0}^{k} {x}_{i}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\bigcup\\limits_{i=0}^{k} A \\cap {x}_{i} = \\emptyset\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(A \\cap {x}_{i} = \\emptyset\\tag*{Eq[2]}\\)";
render(__FILE__, $txt);
?>        

