<?php
require_once '..\..\utility.php';
$i = 0;
$txt[$i++] = "\\({s}_{t} = \\sum\\limits_{i=1}^{t} {G}_{{y}_{i},{y}_{i - 1}} + \\sum\\limits_{i=0}^{t} {x}_{i,{y}_{i}}\\tag*{Eq.s_definition}\\)";
$txt[$i++] = "\\({z}_{t} = [{y}_{t}]\\sum_{{y}_{0:t}} {\\color{blue} e}^{- {s}_{t}}\\tag*{Eq.z_definition}\\)";
$txt[$i++] = "\\({x'}_{t} = - \\log{{z}_{t}}\\tag*{Eq.x_quote_definition}\\)";
$txt[$i++] = "\\({x'}_{t + 1} = {x}_{t + 1} - \\log{\\sum\\limits_{\\substack{}} {\\color{blue} e}^{- {x'}_{t} - G}}\\tag*{Eq.plausible0}\\)";
$txt[$i++] = "\\(- \\log{\\left(\\frac{{\\color{blue} e}^{- {s}_{t}}}{\\sum_{{y}_{0:t + 1}} {\\color{blue} e}^{- {s}_{t}}} \\right)} = {s}_{t} + \\log{\\sum\\limits_{\\substack{}} {\\color{blue} e}^{- {x'}_{t}}}\\tag*{Eq.plausible1}\\)";
$txt[$i++] = "\\({s}_{t + 1} - {s}_{t} = - \\sum\\limits_{i=1}^{t} {G}_{{y}_{i},{y}_{i - 1}} + \\sum\\limits_{i=1}^{t + 1} {G}_{{y}_{i},{y}_{i - 1}} - \\sum\\limits_{i=0}^{t} {x}_{i,{y}_{i}} + \\sum\\limits_{i=0}^{t + 1} {x}_{i,{y}_{i}}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\({s}_{t + 1} = {G}_{{y}_{t + 1},{y}_{t}} + {s}_{t} + {x}_{t + 1,{y}_{t + 1}}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\({z}_{t + 1} = [{y}_{t + 1}]\\sum_{{y}_{0:t + 1}} {\\color{blue} e}^{- {s}_{t + 1}}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\({z}_{t + 1} = [{y}_{t + 1}]\\sum_{{y}_{0:t + 1}} {\\color{blue} e}^{- {G}_{{y}_{t + 1},{y}_{t}} - {s}_{t} - {x}_{t + 1,{y}_{t + 1}}}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\({z}_{t + 1} = [{y}_{t + 1}]\\left({\\color{blue} e}^{- {x}_{t + 1,{y}_{t + 1}}} \\sum_{{y}_{0:t + 1}} {\\color{blue} e}^{- {G}_{{y}_{t + 1},{y}_{t}}} {\\color{blue} e}^{- {s}_{t}}\\right)\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\({z}_{t + 1} = {\\color{blue} e}^{- {x}_{t + 1}} [{y}_{t + 1}]\\sum_{{y}_{0:t + 1}} {\\color{blue} e}^{- {G}_{{y}_{t + 1},{y}_{t}}} {\\color{blue} e}^{- {s}_{t}}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\({z}_{t + 1} = {\\color{blue} e}^{- {x}_{t + 1}} [{y}_{t + 1}]\\sum_{{y}_{t}} {\\color{blue} e}^{- {G}_{{y}_{t + 1},{y}_{t}}} \\sum_{{y}_{0:t}} {\\color{blue} e}^{- {s}_{t}}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\({z}_{t + 1} = {\\color{blue} e}^{- {x}_{t + 1}} [{y}_{t + 1}]\\sum\\limits_{\\substack{}} [{y}_{t}]\\left({\\color{blue} e}^{- {G}_{{y}_{t + 1},{y}_{t}}} \\sum_{{y}_{0:t}} {\\color{blue} e}^{- {s}_{t}}\\right)\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\({z}_{t + 1} = \\left([{y}_{t}]\\sum_{{y}_{0:t}} {\\color{blue} e}^{- {s}_{t}} \\times {\\color{blue} e}^{- G^{\\color{red} T}}\\right) {\\color{blue} e}^{- {x}_{t + 1}}\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\({z}_{t + 1} = \\left({z}_{t} \\times {\\color{blue} e}^{- G^{\\color{red} T}}\\right) {\\color{blue} e}^{- {x}_{t + 1}}\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\({x'}_{t + 1} = - \\log{{z}_{t + 1}}\\tag*{Eq[10]}\\)";
$txt[$i++] = "\\({x'}_{t + 1} = - \\log{\\left(\\left({z}_{t} \\times {\\color{blue} e}^{- G^{\\color{red} T}}\\right) {\\color{blue} e}^{- {x}_{t + 1}} \\right)}\\tag*{Eq[11]}\\)";
$txt[$i++] = "\\({x'}_{t + 1} = {x}_{t + 1} - \\log{\\left({z}_{t} \\times {\\color{blue} e}^{- G^{\\color{red} T}} \\right)}\\tag*{Eq[12]}\\)";
$txt[$i++] = "\\({z}_{t} = {\\color{blue} e}^{- {x'}_{t}}\\tag*{Eq.z_definition_by_x_quote}\\)";
$txt[$i++] = "\\({x'}_{t + 1} = {x}_{t + 1} - \\log{\\left({\\color{blue} e}^{- {x'}_{t}} \\times {\\color{blue} e}^{- G^{\\color{red} T}} \\right)}\\tag*{Eq[13]}\\)";
$txt[$i++] = "\\({x'}_{t + 1} = {x}_{t + 1} - \\log{\\sum\\limits_{\\substack{}} {\\color{blue} e}^{- {x'}_{t} - G}}\\tag*{Eq.plausible0}\\)";
$txt[$i++] = "\\(\\log{\\sum_{{y}_{0:t + 1}} {\\color{blue} e}^{- {s}_{t}}} = \\log{\\sum\\limits_{\\substack{}} {\\color{blue} e}^{- {x'}_{t}}}\\tag*{Eq[14]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{\\substack{}} {\\color{blue} e}^{- {x'}_{t}} = \\sum_{{y}_{0:t + 1}} {\\color{blue} e}^{- {s}_{t}}\\tag*{Eq[15]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{\\substack{}} {z}_{t} = \\sum\\limits_{\\substack{}} [{y}_{t}]\\sum_{{y}_{0:t}} {\\color{blue} e}^{- {s}_{t}}\\tag*{Eq[16]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{\\substack{}} {z}_{t} = \\sum_{{y}_{0:t + 1}} {\\color{blue} e}^{- {s}_{t}}\\tag*{Eq[17]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{\\substack{}} {\\color{blue} e}^{- {x'}_{t}} = \\sum_{{y}_{0:t + 1}} {\\color{blue} e}^{- {s}_{t}}\\tag*{Eq[15]}\\)";
render(__FILE__, $txt);
?>        

