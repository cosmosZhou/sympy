<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(e \\not\\in s\\tag*{Eq[0]}\\)\\(s \\cap \\left\\{e\\right\\} = \\emptyset\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\exists_{f}{f \\in s \\cap \\left\\{e\\right\\}} \\vee s \\cap \\left\\{e\\right\\} = \\emptyset\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\exists_{f}{f \\in s \\cap \\left\\{e\\right\\}}\\tag*{~Eq[3]}\\)\\(s \\cap \\left\\{e\\right\\} = \\emptyset\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\exists_{f}{f \\in s}\\tag*{~Eq[4]}\\)\\(\\exists_{f}{f \\in \\left\\{e\\right\\}}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\exists_{f}{f = e}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
$txt[$i++] = "\\(e \\in s\\tag*{~Eq[7]}\\)";
$txt[$i++] = "\\(\\text{False}\\)";
$txt[$i++] = "\\(\\forall_{f}{f \\not\\in s \\cap \\left\\{e\\right\\}}\\tag*{Eq[8]}\\)\\(s \\cap \\left\\{e\\right\\} = \\emptyset\\tag*{Eq[1]}\\)";
render(__FILE__, $txt);
?>        

