<?php
require_once '..\..\utility.php';
$i = 0;
$txt[$i++] = "\\({m}_{k} = \\beta^{k} \\left(1 - \\beta\\right) \\sum\\limits_{t=1}^{k} \\beta^{- t} {g}_{t}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\({m}_{0} = 0\\tag*{Eq[1]}\\)\\({m}_{t} = \\beta {m}_{t - 1} + {g}_{t} \\left(1 - \\beta\\right)\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\beta^{- t} {m}_{t} = - \\beta^{- t} \\left(\\beta {g}_{t} - \\beta {m}_{t - 1} - {g}_{t}\\right)\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\beta^{- t} {m}_{t} = - \\beta \\beta^{- t} {g}_{t} + \\beta \\beta^{- t} {m}_{t - 1} + \\beta^{- t} {g}_{t}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\beta^{- t} {m}_{t} = - \\beta^{1 - t} {g}_{t} + \\beta^{1 - t} {m}_{t - 1} + \\beta^{- t} {g}_{t}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\beta^{- t} {m}_{t} = \\beta^{1 - t} {m}_{t - 1} + {g}_{t} \\left(- \\beta^{1 - t} + \\beta^{- t}\\right)\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{t=1}^{k} \\beta^{- t} {m}_{t} = \\sum\\limits_{t=1}^{k} \\left(\\beta^{1 - t} {m}_{t - 1} + {g}_{t} \\left(- \\beta^{1 - t} + \\beta^{- t}\\right)\\right)\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{t=1}^{k} \\beta^{- t} {m}_{t} = \\sum\\limits_{t=1}^{k} \\beta^{1 - t} {m}_{t - 1} + \\sum\\limits_{t=1}^{k} {g}_{t} \\left(- \\beta^{1 - t} + \\beta^{- t}\\right)\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{t=1}^{k} \\beta^{- t} {m}_{t} - \\sum\\limits_{t=1}^{k} \\beta^{1 - t} {m}_{t - 1} = \\sum\\limits_{t=1}^{k} {g}_{t} \\left(- \\beta^{1 - t} + \\beta^{- t}\\right)\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(- {m}_{0} + \\beta^{- k} {m}_{k} = \\sum\\limits_{t=1}^{k} {g}_{t} \\left(- \\beta^{1 - t} + \\beta^{- t}\\right)\\tag*{Eq[10]}\\)";
$txt[$i++] = "\\(\\beta^{- k} {m}_{k} = \\sum\\limits_{t=1}^{k} {g}_{t} \\left(- \\beta^{1 - t} + \\beta^{- t}\\right)\\tag*{Eq[11]}\\)";
$txt[$i++] = "\\({m}_{k} = \\beta^{k} \\left(1 - \\beta\\right) \\sum\\limits_{t=1}^{k} \\beta^{- t} {g}_{t}\\tag*{Eq[0]}\\)";
render(__FILE__, $txt);
?>        

