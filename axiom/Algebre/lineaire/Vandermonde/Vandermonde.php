<?php
require_once '..\..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\([i,j:m]\\left(\\left(-1\\right)^{d + i + j} {\\binom{d}{- i + j}}\\right) \\times [i:m,j]\\left(x^{i} \\left(\\delta + i\\right)^{j}\\right) = [i,j]\\left(x^{i} \\left(\\delta + i\\right)^{j}\\right) \\times [i:n,j]\\left({\\binom{j}{i}} \\sum\\limits_{h=0}^{d} \\left(-1\\right)^{d + h} h^{- i + j} x^{h} {\\binom{d}{h}}\\right)\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\([i,j]\\sum\\limits_{e=0}^{m - 1} \\left(-1\\right)^{d + e + i} x^{e} \\left(\\delta + e\\right)^{j} {\\binom{d}{e - i}} = [i,j]\\sum\\limits_{e=0}^{n - 1} x^{i} \\left(\\delta + i\\right)^{e} {\\binom{j}{e}} \\sum\\limits_{h=0}^{d} \\left(-1\\right)^{d + h} h^{- e + j} x^{h} {\\binom{d}{h}}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{e=0}^{m - 1} \\left(-1\\right)^{d + e + i} x^{e} \\left(\\delta + e\\right)^{j} {\\binom{d}{e - i}} = \\sum\\limits_{e=0}^{n - 1} x^{i} \\left(\\delta + i\\right)^{e} {\\binom{j}{e}} \\sum\\limits_{h=0}^{d} \\left(-1\\right)^{d + h} h^{- e + j} x^{h} {\\binom{d}{h}}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{e=0}^{m - 1} \\left(-1\\right)^{d + e + i} x^{e} \\left(\\delta + e\\right)^{j} {\\binom{d}{e - i}} = \\sum\\limits_{h=0}^{d} \\left(-1\\right)^{d + h} x^{h + i} {\\binom{d}{h}} \\sum\\limits_{e=0}^{n - 1} h^{- e + j} \\left(\\delta + i\\right)^{e} {\\binom{j}{e}}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{e=0}^{m - 1} \\left(-1\\right)^{d + e + i} x^{e} \\left(\\delta + e\\right)^{j} {\\binom{d}{e - i}} = \\sum\\limits_{h=i}^{d + i} \\left(-1\\right)^{d + h + i} x^{h} {\\binom{d}{h - i}} \\sum\\limits_{e=0}^{j} \\left(\\delta + i\\right)^{e} \\left(h - i\\right)^{- e + j} {\\binom{j}{e}}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{h=i}^{d + i} \\left(-1\\right)^{d + h + i} x^{h} \\left(\\delta + h\\right)^{j} {\\binom{d}{h - i}} = \\sum\\limits_{h=i}^{d + i} \\left(-1\\right)^{d + h + i} x^{h} {\\binom{d}{h - i}} \\sum\\limits_{e=0}^{j} \\left(\\delta + i\\right)^{e} \\left(h - i\\right)^{- e + j} {\\binom{j}{e}}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{k=0}^{j} \\left(\\delta + i\\right)^{k} \\left(h - i\\right)^{j - k} {\\binom{j}{k}} = \\left(\\delta + h\\right)^{j}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\sum\\limits_{e=0}^{j} \\left(\\delta + i\\right)^{e} \\left(h - i\\right)^{- e + j} {\\binom{j}{e}} = \\left(\\delta + h\\right)^{j}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(\\text{True}\\)";
$txt[$i++] = "\\([i,j]\\sum\\limits_{e=0}^{m - 1} \\left(-1\\right)^{d + e + i} x^{e} \\left(\\delta + e\\right)^{j} {\\binom{d}{e - i}} = [i,j]\\sum\\limits_{e=0}^{n - 1} x^{i} \\left(\\delta + i\\right)^{e} {\\binom{j}{e}} \\sum\\limits_{h=0}^{d} \\left(-1\\right)^{d + h} h^{- e + j} x^{h} {\\binom{d}{h}}\\tag*{Eq[1]}\\)";
render(__FILE__, $txt);
?>        

