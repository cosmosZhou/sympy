<?php
require_once 'std.php';
require_once 'mysql.php';

$symbol = $_GET["symbol"];

// list (list ($script, $latex)) = iterator_to_array();
foreach (\mysql\select("select script, latex from tbl_console_py where symbol = '$symbol'") as list ($script, $latex)) {
    error_log("script = " . \std\jsonify($script));
    error_log("latex = " . \std\jsonify($latex));
    $latex = trim($latex);
    $latex = json_decode($latex, true);

    $script = json_decode($script);

    for ($i = 0; $i < count($latex); ++ $i) {
        $statements[] = [
            'script' => $script[$i],
            'latex' => $latex[$i]
        ];
    }
}

$statements[] = [
    'script' => '',
    'latex' => ''
];
?>

<title><?php echo $symbol;?></title>
<div id=root>
	<console :statements=statements></console>
</div>

<script src="https://cdn.jsdelivr.net/npm/axios/dist/axios.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/qs/dist/qs.js"></script>

<script src="https://unpkg.com/vue@3.2.11/dist/vue.global.prod.js"></script>
<script src="https://cdn.jsdelivr.net/npm/vue3-sfc-loader/dist/vue3-sfc-loader.js"></script>

<script async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-svg.js"></script>

<script src="static/js/std.js"></script>
<script src="static/js/utility.js"></script>

<script type=module>
createApp('console', {
    statements : <?php echo \std\jsonify($statements)?>,
});
</script>
