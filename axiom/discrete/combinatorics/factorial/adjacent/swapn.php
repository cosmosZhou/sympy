<?php
require_once '..\..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(P = \\left\\{\\left. p \\right| \\left\\{*p\\right\\}  = \\left[0; n\\right) \\right\\}\\tag*{Eq.P_definition}\\)";
$txt[$i++] = "\\({w}_{i,j} = Swap\\left(n, i, j\\right)\\tag*{Eq.w_definition}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{x \\in S}}{[k]{x}_{{w}_{i,j,k} \\times [k]k} \\in S}\\tag*{Eq.swap}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{p \\in P}}{[k]{x}_{{p}_{k}} \\in S}\\tag*{Eq.swap=>Eq.axiom}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{x \\in S}}{[k]{x}_{{w}_{i,i,k} \\times [k]k} \\in S}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\({w}_{i,i,k} \\times [k]k = [o:n]\\delta_{k o} \\times [k]k\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\({w}_{i,i,k} \\times [k]k = k\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
$txt[$i++] = "\\(\\forall_{\\substack{x \\in S}}{[k]{x}_{{w}_{{p}_{0},0,k} \\times [k]k} \\in S}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\exists_{{r}_{0}}{{r}_{0} = [k]k}\\tag*{Eq.r0_definition}\\)";
$txt[$i++] = "\\({d}_{j} = [k]\\delta_{j {r}_{j,k}} \\times [k]k\\tag*{Eq.d_definition}\\)";
$txt[$i++] = "\\(\\exists_{r}{{r}_{j + 1} = {w}_{{p}_{j},{d}_{j}} \\times {r}_{j}}\\tag*{Eq.r_definition}\\)";
$txt[$i++] = "\\({r}_{j,{d}_{j}} = j\\tag*{?=>Eq.d_assertion}\\)";
$txt[$i++] = "\\({r}_{0,{d}_{0}} = 0\\tag*{Eq.d0_assertion}\\)";
$txt[$i++] = "\\({d}_{j} = \\sum\\limits_{l=1}^{n - 1} l \\delta_{j {r}_{j,l}}\\tag*{Eq.d_definition_expand}\\)";
$txt[$i++] = "\\({d}_{0} = 0\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\({d}_{0} = 0\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\({r}_{j + 1,{d}_{j + 1}} = j + 1\\tag*{Eq.d_assertion=>Eq.d_assertion_induction}\\)";
$txt[$i++] = "\\({d}_{j + 1} = \\sum\\limits_{l=1}^{n - 1} l \\delta_{{r}_{j + 1,l}, j + 1}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\exists_{r}{{r}_{j + 1,l} = {w}_{{p}_{j},{d}_{j},l} \\times {r}_{j}}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\exists_{r}{{d}_{j + 1} = \\sum\\limits_{l=1}^{n - 1} l \\delta_{{w}_{{p}_{j},{d}_{j},l} \\times {r}_{j}, j + 1}}\\tag*{Eq[7]}\\)";
render(__FILE__, $txt);
?>        

