<?php
// ^ *error_log

// input is a py file
$python_file = dirname(dirname(__file__)) . '/sympy/' . str_replace(".", "/", $sympy) . ".py";
error_log($python_file);
if (array_key_exists('code', $_POST)) {
    $code = $_POST['code'];
    file_put_contents($python_file, $code);
} else {
    $code = file_get_contents($python_file);
}

$code = str_replace("\\", "\\\\", $code);
$code = str_replace("`", "\\`", $code);
?>

<title><?php echo $sympy;?></title>
<link rel=stylesheet href="static/codemirror/lib/codemirror.css">
<link rel=stylesheet href="static/codemirror/theme/eclipse.css">
<link rel=stylesheet href="static/codemirror/addon/hint/show-hint.css">
<body></body>

<script src="https://unpkg.com/vue@3.2.11/dist/vue.global.prod.js"></script>
<script src="https://cdn.jsdelivr.net/npm/axios/dist/axios.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/qs/dist/qs.js"></script>
<script
	src="https://cdn.jsdelivr.net/npm/vue3-sfc-loader/dist/vue3-sfc-loader.js"></script>

<script src='static/js/std.js'></script>
<script src='static/js/utility.js'></script>

<script type=module>
import * as codemirror from "./static/codemirror/lib/codemirror.js";
import * as python from "./static/codemirror/mode/python/python.js";
import * as active_line from "./static/codemirror/addon/selection/active-line.js";
import * as show_hint from "./static/codemirror/addon/hint/show-hint.js";
import * as matchbrackets from "./static/codemirror/addon/edit/matchbrackets.js";

createApp('sympy', {
    code: `<?php echo $code;?>`,
});
//http://codemirror.net/doc/manual.html
</script>


