<?php
require_once '..\..\utility.php';
$i = 0;
$txt[$i++] = "\\({s}_{t} = \\sum\\limits_{i=1}^{t} {G}_{{y}_{i},{y}_{i - 1}} + \\sum\\limits_{i=0}^{t} {x}_{i,{y}_{i}}\\tag*{Eq.s_definition}\\)";
$txt[$i++] = "\\({x'}_{t} = [{y}_{t}]\\min\\limits_{{y}_{0:t}} {s}_{t}\\tag*{Eq.x_quote_definition}\\)";
$txt[$i++] = "\\({x'}_{t + 1} = {x}_{t + 1} + \\min \\left({x'}_{t} + G\\right)\\tag*{Eq.recursion}\\)";
$txt[$i++] = "\\(\\min\\limits_{{y}_{0:t + 1}} {s}_{t} = \\min {x'}_{t}\\tag*{Eq.aggregate}\\)";
$txt[$i++] = "\\({s}_{t + 1} = \\sum\\limits_{i=1}^{t + 1} {G}_{{y}_{i},{y}_{i - 1}} + \\sum\\limits_{i=0}^{t + 1} {x}_{i,{y}_{i}}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\({s}_{t + 1} - {s}_{t} = - \\sum\\limits_{i=1}^{t} {G}_{{y}_{i},{y}_{i - 1}} + \\sum\\limits_{i=1}^{t + 1} {G}_{{y}_{i},{y}_{i - 1}} - \\sum\\limits_{i=0}^{t} {x}_{i,{y}_{i}} + \\sum\\limits_{i=0}^{t + 1} {x}_{i,{y}_{i}}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\({s}_{t + 1} = {G}_{{y}_{t + 1},{y}_{t}} + {s}_{t} + {x}_{t + 1,{y}_{t + 1}}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\({x'}_{t + 1} = [{y}_{t + 1}]\\min\\limits_{{y}_{0:t + 1}} {s}_{t + 1}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\({x'}_{t + 1} = [{y}_{t + 1}]\\min\\limits_{{y}_{0:t + 1}} \\left({G}_{{y}_{t + 1},{y}_{t}} + {s}_{t} + {x}_{t + 1,{y}_{t + 1}}\\right)\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\({x'}_{t + 1} = {x}_{t + 1} + [{y}_{t + 1}]\\min\\limits_{{y}_{0:t + 1}} \\left({G}_{{y}_{t + 1},{y}_{t}} + {s}_{t}\\right)\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\({x'}_{t + 1} = {x}_{t + 1} + [{y}_{t + 1}]\\min\\limits_{{y}_{t}} \\left({G}_{{y}_{t + 1},{y}_{t}} + \\min\\limits_{{y}_{0:t}} {s}_{t}\\right)\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\({x'}_{t + 1} = {x}_{t + 1} + [{y}_{t + 1}]\\min \\left({G}_{{y}_{t + 1}} + [{y}_{t}]\\min\\limits_{{y}_{0:t}} {s}_{t}\\right)\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\({x'}_{t + 1} = {x}_{t + 1} + \\min \\left(G + [{y}_{t}]\\min\\limits_{{y}_{0:t}} {s}_{t}\\right)\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\({x'}_{t + 1} = {x}_{t + 1} + \\min \\left({x'}_{t} + G\\right)\\tag*{Eq.recursion}\\)";
$txt[$i++] = "\\(\\min\\limits_{{y}_{t}} \\min\\limits_{{y}_{0:t}} {s}_{t} = \\min {x'}_{t}\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(\\min [{y}_{t}]\\min\\limits_{{y}_{0:t}} {s}_{t} = \\min {x'}_{t}\\tag*{Eq[10]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
render(__FILE__, $txt);
?>        

