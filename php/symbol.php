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

<script src="https://cdn.jsdelivr.net/npm/vue@2.6.12/dist/vue.min.js"></script>
<script	src="https://cdn.jsdelivr.net/npm/http-vue-loader@1.4.2/src/httpVueLoader.min.js"></script>
<script async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-svg.js"></script>

<script src="static/js/std.js"></script>
<script src="static/js/utility.js"></script>
<script>
    var data = {
        statements : <?php echo \std\jsonify($statements)?>,
    };
    
    Vue.use(httpVueLoader);
    Vue.component('console', 'url:static/vue/console.vue');

    var app = new Vue({
        el : '#root',
        data : data,
    });

</script>
