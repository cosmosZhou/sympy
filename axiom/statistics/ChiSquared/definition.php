<?php
require_once '..\..\..\utility.php';
$i = 0;
$txt[$i++] = "\\(Density\\left(\\sum\\limits_{i=0}^{k - 1} {\\color{red} {{x}_{i}}}^{2}\\right)\\left(y \\right) = \\frac{2^{- \\frac{k}{2}} y^{\\frac{k}{2} - 1} {\\color{blue} e}^{- \\frac{y}{2}}}{\\Gamma\\left(\\frac{k}{2}\\right)}\\tag*{Eq[0]}\\)";
$txt[$i++] = "\\({\\color{red} {{Y}_{k}}} = \\sum\\limits_{i=0}^{k - 1} {\\color{red} {{x}_{i}}}^{2}\\tag*{Eq[1]}\\)";
$txt[$i++] = "\\(Density\\left({\\color{red} {{Y}_{k}}}\\right)\\left(y \\right) = \\frac{2^{- \\frac{k}{2}} y^{\\frac{k}{2} - 1} {\\color{blue} e}^{- \\frac{y}{2}}}{\\Gamma\\left(\\frac{k}{2}\\right)}\\tag*{Eq[2]}\\)";
$txt[$i++] = "\\(Density\\left({\\color{red} {{Y}_{k + 1}}}\\right)\\left(y \\right) = \\frac{2^{- \\frac{k}{2} - \\frac{1}{2}} y^{\\frac{k}{2} - \\frac{1}{2}} {\\color{blue} e}^{- \\frac{y}{2}}}{\\Gamma\\left(\\frac{k}{2} + \\frac{1}{2}\\right)}\\tag*{Eq[3]}\\)";
$txt[$i++] = "\\({\\color{red} {{Y}_{k + 1}}} = {\\color{red} {{Y}_{k}}} + {\\color{red} {{x}_{k}}}^{2}\\tag*{Eq[4]}\\)";
$txt[$i++] = "\\(Density\\left({\\color{red} {{Y}_{k}}} + {\\color{red} {{x}_{k}}}^{2}\\right)\\left(y \\right) = \\frac{2^{- \\frac{k}{2} - \\frac{1}{2}} y^{\\frac{k}{2} - \\frac{1}{2}} {\\color{blue} e}^{- \\frac{y}{2}}}{\\Gamma\\left(\\frac{k}{2} + \\frac{1}{2}\\right)}\\tag*{Eq[5]}\\)";
$txt[$i++] = "\\(Density\\left({\\color{red} {{Y}_{k}}} + {\\color{red} {{x}_{k}}}^{2}\\right)\\left(y \\right) = \\frac{\\sqrt{2} \\int\\limits_{0}^{\\infty} \\left(Density\\left(\\sum\\limits_{i=0}^{k - 1} {\\color{red} {{x}_{i}}}^{2}\\right)\\left({Y}_{k} \\right)\\right) \\int\\limits_{-\\infty}^{\\infty} {\\color{blue} e}^{- \\frac{{x}_{k}^{2}}{2}} \\delta\\left(- y + {Y}_{k} + {x}_{k}^{2}\\right)\\, d{x}_{k}\\, d{Y}_{k}}{2 \\sqrt{\\pi}}\\tag*{Eq[6]}\\)";
$txt[$i++] = "\\(Density\\left({\\color{red} {{Y}_{k}}} + {\\color{red} {{x}_{k}}}^{2}\\right)\\left(y \\right) = \\frac{\\sqrt{2} \\int\\limits_{0}^{y} \\frac{{\\color{blue} e}^{- \\frac{y}{2} + \\frac{{Y}_{k}}{2}} Density\\left(\\sum\\limits_{i=0}^{k - 1} {\\color{red} {{x}_{i}}}^{2}\\right)\\left({Y}_{k} \\right)}{\\left|{\\sqrt{y - {Y}_{k}}}\\right|}\\, d{Y}_{k}}{2 \\sqrt{\\pi}}\\tag*{Eq[7]}\\)";
$txt[$i++] = "\\(Density\\left(\\sum\\limits_{i=0}^{k - 1} {\\color{red} {{x}_{i}}}^{2}\\right)\\left({Y}_{k} \\right) = \\frac{2^{- \\frac{k}{2}} {Y}_{k}^{\\frac{k}{2} - 1} {\\color{blue} e}^{- \\frac{{Y}_{k}}{2}}}{\\Gamma\\left(\\frac{k}{2}\\right)}\\tag*{Eq[8]}\\)";
$txt[$i++] = "\\(Density\\left({\\color{red} {{Y}_{k}}} + {\\color{red} {{x}_{k}}}^{2}\\right)\\left(y \\right) = \\frac{\\sqrt{2} \\cdot 2^{- \\frac{k}{2}} {\\color{blue} e}^{- \\frac{y}{2}} \\int\\limits_{0}^{y} \\frac{{Y}_{k}^{\\frac{k}{2}}}{{Y}_{k} \\left|{\\sqrt{y - {Y}_{k}}}\\right|}\\, d{Y}_{k}}{2 \\sqrt{\\pi} \\Gamma\\left(\\frac{k}{2}\\right)}\\tag*{Eq[9]}\\)";
$txt[$i++] = "\\(\\frac{2^{- \\frac{k}{2} - \\frac{1}{2}} y^{\\frac{k}{2} - \\frac{1}{2}}}{\\Gamma\\left(\\frac{k}{2} + \\frac{1}{2}\\right)} = \\frac{\\sqrt{2} \\cdot 2^{- \\frac{k}{2}} \\int\\limits_{0}^{y} \\frac{{Y}_{k}^{\\frac{k}{2}}}{{Y}_{k} \\left|{\\sqrt{y - {Y}_{k}}}\\right|}\\, d{Y}_{k}}{2 \\sqrt{\\pi} \\Gamma\\left(\\frac{k}{2}\\right)}\\tag*{Eq[10]}\\)";
$txt[$i++] = "\\(\\frac{y^{\\frac{k}{2}}}{\\sqrt{y} \\Gamma\\left(\\frac{k}{2} + \\frac{1}{2}\\right)} = \\frac{\\int\\limits_{0}^{y} \\frac{{Y}_{k}^{\\frac{k}{2}}}{{Y}_{k} \\left|{\\sqrt{y - {Y}_{k}}}\\right|}\\, d{Y}_{k}}{\\sqrt{\\pi} \\Gamma\\left(\\frac{k}{2}\\right)}\\tag*{Eq[11]}\\)";
$txt[$i++] = "\\(\\frac{1}{\\Gamma\\left(\\frac{k}{2} + \\frac{1}{2}\\right)} = \\frac{2 \\int\\limits_{0}^{\\frac{\\pi}{2}} \\frac{\\sin^{k} {t}}{\\sin {t}}\\, dt}{\\sqrt{\\pi} \\Gamma\\left(\\frac{k}{2}\\right)}\\tag*{Eq[12]}\\)";
$txt[$i++] = "\\(\\frac{1}{\\Gamma\\left(\\frac{k}{2} + \\frac{1}{2}\\right)} = \\frac{2 \\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin^{k - 1} {t}\\, dt}{\\sqrt{\\pi} \\Gamma\\left(\\frac{k}{2}\\right)}\\tag*{Eq[13]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin^{k - 1} {t}\\, dt = \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{k}{2}\\right)}{2 \\Gamma\\left(\\frac{k}{2} + \\frac{1}{2}\\right)}\\tag*{Eq[14]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin^{k - 1} {x}\\, dx = \\frac{\\operatorname{B}\\left(\\frac{1}{2}, \\frac{k}{2}\\right)}{2}\\tag*{Eq[15]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin^{k - 1} {t}\\, dt = \\frac{\\operatorname{B}\\left(\\frac{1}{2}, \\frac{k}{2}\\right)}{2}\\tag*{Eq[15]}\\)";
$txt[$i++] = "\\(\\int\\limits_{0}^{\\frac{\\pi}{2}} \\sin^{k - 1} {t}\\, dt = \\frac{\\sqrt{\\pi} \\Gamma\\left(\\frac{k}{2}\\right)}{2 \\Gamma\\left(\\frac{k}{2} + \\frac{1}{2}\\right)}\\tag*{Eq[14]}\\)";
$txt[$i++] = "\\(Density\\left({\\color{red} {{Y}_{1}}}\\right)\\left(y \\right) = \\frac{\\sqrt{2} {\\color{blue} e}^{- \\frac{y}{2}}}{2 \\sqrt{\\pi} \\sqrt{y}}\\tag*{Eq[16]}\\)";
$txt[$i++] = "\\({\\color{red} {{Y}_{1}}} = {\\color{red} {{x}_{0}}}^{2}\\tag*{Eq[17]}\\)";
$txt[$i++] = "\\(Density\\left({\\color{red} {{x}_{0}}}^{2}\\right)\\left(y \\right) = \\frac{\\sqrt{2} {\\color{blue} e}^{- \\frac{y}{2}}}{2 \\sqrt{\\pi} \\sqrt{y}}\\tag*{Eq[18]}\\)";
$txt[$i++] = "\\(Density\\left({\\color{red} {{x}_{0}}}^{2}\\right)\\left(y \\right) = \\frac{\\sqrt{2} {\\color{blue} e}^{- \\frac{y}{2}}}{2 \\sqrt{\\pi} \\sqrt{y}}\\tag*{Eq[18]}\\)";
render(__FILE__, $txt);
?>        

