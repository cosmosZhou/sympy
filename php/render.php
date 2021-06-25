<?php
//^ *error_log
if ($input != null) {
    $inputs[] = piece_together($input);
}

$pos = strpos(py_to_module($py), '.given.');
// error_log("py = " . $py);
// error_log("pos = " . $pos);
// https://www.php.net/manual/en/function.strpos.php
if ($pos === false) {
    $imply = "imply";
} else {
    $imply = "given";
}

$numOfReturnsFromApply = $lengths[$indexOfYield];
// error_log("numOfReturnsFromApply = " . $numOfReturnsFromApply);
// error_log("lengths = " . \std\jsonify($lengths));

$p = [];
$i = 0;
$statements = '';
$statements_before_yield = '';

error_log("module = $module");
// error_log("statements From MySQL  =" . \std\jsonify(\mysql\yield_from_mysql($module)));
// error_log("statements From SQLFile=" . \std\jsonify($statementsFromSQLFile));

$content = [];

$indexOfImply = - 1;

$res = \mysql\yield_from_mysql($module);

error_log("res = ".\std\jsonify($res));

foreach ($statementsFromSQLFile === null ? \mysql\yield_from_mysql($module) : $statementsFromSQLFile as $statement) {

    if ($i == $indexOfYield) {

// error_log($statement);
        -- $lengths[$i];
        $statements .= $statement;
        if ($lengths[$i] == 0) {

            if ($numOfReturnsFromApply == 1) {
                if (is_latex($statement, $matches)) {
                    
// error_log("matches = ".\std\jsonify($matches));

                    $numOfReturnsFromApply = count($matches);
                    
// error_log("count(matches) = ".$numOfReturnsFromApply);

                    $statements_before_yield = array_slice($matches, 0, $numOfReturnsFromApply - $numOfYields);
                    // error_log("statements_before_yield = ".jsonify($statements_before_yield));
                    $statements = array_slice($matches, $numOfReturnsFromApply - $numOfYields);
                    // error_log("statements_after_yield = ".jsonify($statements));

                    foreach ($statements as &$statement) {
                        $statement = $statement[0];
                    }
                    $statements = join('', $statements);

                    foreach ($statements_before_yield as &$statement) {
                        $statement = $statement[0];
                    }
                    $statements_before_yield = join('', $statements_before_yield);
                }
            }

            $p[] = $statements_before_yield;

            $indexOfImply = count($p);

            array_splice($inputs, $indexOfImply, 0, $imply);
            $p[] = $statements;

            $statements = '';
            $statements_before_yield = '';
            ++ $i;
        } else if ($lengths[$i] == $numOfYields) {
            $statements_before_yield = $statements;
// error_log("lengths[i] = ".$lengths[$i]);
// error_log("statements_before_yield = $statements_before_yield");

            $statements = '';
        }
    } else {
        $statements .= $statement;
        if ($i >= count($lengths))
            continue;
        
        -- $lengths[$i];
        if ($lengths[$i] == 0) {
            $p[] = $statements;
            $statements = '';
            ++ $i;
        }
    }
}

?>

<title>render</title>
<link rel=stylesheet
	href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/lib/codemirror.css" />
<link rel="stylesheet"
	href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/theme/eclipse.css">
<link rel="stylesheet"
	href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/addon/hint/show-hint.css">
<link rel="stylesheet" href="/sympy/css/codemirror.css">
<style>
.error{
    color: red;
}

.error:hover{
	cursor: pointer;
}

</style>

<div id=root>

	<form name="form" spellcheck=false enctype="multipart/form-data"
		method="post" action="">
		<template v-for="(p, i) in p">
			<template v-if="i == indexOfImply">
				<hr>
				<h3 title='callee hierarchy'>
					<a style='font-size: inherit'
						:href="'/%s/php/hierarchy.php?callee=%s'.format(user, module)"><font
						color=blue>{{inputs[i]}}:</font></a>
				</h3>
			</template>
			<template v-else>
				<textarea name=prove[]>{{inputs[i]}}</textarea>
			</template>

			<p>{{p}}</p>
		</template>

		<template v-for="(_, i) in inputs.length - p.length">
			<textarea name=prove[]>{{inputs[i + p.length]}}</textarea>
			<br>
		</template>

	</form>

	<template v-if="logs.length != 0">
		<br> <br>
		<h3>debugging information is printed as follows:</h3>
	</template>

	<div v-for="log in logs">
		<p v-if="typeof log == 'string'">{{log}}</p>
		<font v-else class=error :title=log.module @click=click>
			{{log.code}}<br>
			{{log.type}}: {{log.error}}<br>
		</font>
	</div>
	
</div>

<script>	
	logs = <?php echo \std\jsonify($logs)?>;
	for (let i = 0; i < logs.length; ++i){
		var log = logs[i];
		if (log.startsWith('{') && log.endsWith('}')){
			logs[i] = JSON.parse(log);
		}
	}

	var data = {
		logs : logs,
		inputs : <?php echo \std\jsonify($inputs)?>,
		p : <?php echo \std\jsonify($p)?>,
		indexOfImply: <?php echo $indexOfImply?>,			
		user: <?php global $user; echo \std\jsonify($user)?>,
		module: <?php echo \std\jsonify($module)?>,
	};

    var sql = `<?php echo $sql_statement?>`;

    var apply = `<?php echo array_key_exists('apply', $_GET)? $_GET['apply']: null ?>`;
</script>

<script
	src='https://cdn.jsdelivr.net/npm/jquery@3.5.1/dist/jquery.min.js'></script>
<script
	src="https://cdn.jsdelivr.net/npm/mathjax@2.7.8/MathJax.js?config=TeX-AMS-MML_HTMLorMML"></script>
<script
	src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/lib/codemirror.js"></script>
<script
	src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/mode/python/python.js"></script>

<script
	src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/mode/markdown/markdown.js"></script>

<script
	src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/addon/hint/show-hint.js"></script>
<script
	src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/addon/edit/matchbrackets.js"></script>
<script src="https://cdn.jsdelivr.net/npm/vue@2.6.12/dist/vue.min.js"></script>

<script src='/sympy/js/std.js'></script>
<script src='/sympy/js/utility.js'></script>
<script src='/sympy/js/render.js'></script>