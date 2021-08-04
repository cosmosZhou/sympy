<?php
// ^ *error_log
if ($input != null) {
    $inputs[] = piece_together($input);
}

$numOfReturnsFromApply = $lengths[$indexOfYield];
// error_log("numOfReturnsFromApply = " . $numOfReturnsFromApply);
// error_log("lengths = " . \std\jsonify($lengths));

$latex = [];
$i = 0;
$statements = '';
$statements_before_yield = '';

error_log("module = $module");

$content = [];

if (!$statementsFromSQLFile){
    $statementsFromSQLFile = \mysql\yield_from_mysql($module);
}

preg_match("/([\w.]+)\.(imply|given)\./", $module, $m);
$numOfRequisites = $m ? count(explode(".", $m[1])) - 1 : 0;

$where = '';
foreach ($statementsFromSQLFile as $statement) {

    if ($i == $indexOfYield) {
        -- $lengths[$i];
        $statements .= $statement;
        if ($lengths[$i] == 0) {

            if ($numOfReturnsFromApply == 1) {
                if (is_latex($statement, $matches)) {

                    $numOfReturnsFromApply = count($matches);

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

                    if ($numOfRequisites < count($statements_before_yield)) {
                        $where = array_slice($statements_before_yield, $numOfRequisites);
                        $where = join('', $where);
                        $statements_before_yield = array_slice($statements_before_yield, 0, $numOfRequisites);
                    } else {
                        $where = '';
                    }

                    $statements_before_yield = join('', $statements_before_yield);
                }
            }

            $given = [
                'py' => $inputs[0],
                'latex' => $statements_before_yield
            ];

            $inputs = array_slice($inputs, 1);

            $imply = $statements;

            $statements = '';
            $statements_before_yield = '';
            ++ $i;
        } else if ($lengths[$i] == $numOfYields) {
            $statements_before_yield = $statements;
            $statements = '';
        }
    } else {
        $statements .= $statement;
        if ($i >= count($lengths))
            continue;

        -- $lengths[$i];
        if ($lengths[$i] == 0) {
            $latex[] = $statements;
            $statements = '';
            ++ $i;
        }
    }
}

$size = count($latex);
if (count($inputs) > $size) {
    $unused = array_slice($inputs, $size);
} else {
    $unused = [];
}

$prove = [];
for ($i = 0; $i < $size; ++ $i) {
    $prove[] = [
        'py' => $inputs[$i],
        'latex' => $latex[$i]
    ];
}

?>

<title><?php echo $module;?></title>
<link rel=stylesheet
	href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/lib/codemirror.css" />
<link rel="stylesheet"
	href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/theme/eclipse.css">
<link rel="stylesheet"
	href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/addon/hint/show-hint.css">
<link rel="stylesheet" href="static/css/codemirror.css">

<div id=root>
	<render ref=render :logs=logs :prove=prove :given=given :imply=imply
		:where=where :module=module :apply=apply :apply-arg=applyArg
		:unused=unused></render>
</div>

<script>
	MathJax = {
  		startup: {
    		ready(){
      			console.log('MathJax is loaded, but not yet initialized');
      			MathJax.startup.defaultReady();
      			console.log('MathJax is initialized, and the initial typeset is queued');
      			
				MathJax.startup.promise.then(() => {					
      	        	console.log('MathJax initial typesetting complete');
      	        	setTimeout(() => {      	        		
      	        		for (let p of document.querySelectorAll('p')){
          	        		if (p.innerText.startsWith("\\[")) {
              	        		console.log("unfinished work detected!");
              	        		console.log(p.innerText);
              	        		console.log('trying MathJax.typesetPromise() again;');
              	        		MathJax.typesetPromise();
              	        		break;
              	        	}
          	        	}      	        		      	        		
      				}, 500);
      	      	});      			
			}
  		},

  		tex: {
  		    maxBuffer: 10 * 1024,       // maximum size for the internal TeX string (10K)
  		  //reference: http://docs.mathjax.org/en/latest/options/input/tex.html?highlight=MAXBUFFER#the-configuration-block
  	  	},
	};
</script>
<script async
	src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"></script>

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
<script
	src="https://cdn.jsdelivr.net/npm/http-vue-loader@1.4.2/src/httpVueLoader.min.js"></script>

<script src="https://cdn.jsdelivr.net/npm/axios/dist/axios.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/qs/dist/qs.js"></script>


<script src='static/js/std.js'></script>
<script src='static/js/utility.js'></script>

<script>
	logs = <?php echo \std\jsonify($logs)?>;

	console.log(logs);
	for (let i = 0; i < logs.length; ++i){
		var log = logs[i];
		if (log.startsWith('{') && log.endsWith('}')){
			logs[i] = JSON.parse(log);
		}
	}

    var applyArg = `<?php echo array_key_exists('apply', $_GET)? $_GET['apply']: null ?>`;
    var apply = applyArg? `<?php echo fetch_codes($module); ?>` : null;
	
	var data = {
		logs : logs,
		apply: apply,
		applyArg: applyArg,
		prove : <?php echo \std\jsonify($prove)?>,
		unused : <?php echo \std\jsonify($unused)?>,
		module: <?php echo \std\jsonify($module)?>,
		given: <?php echo \std\jsonify($given)?>,
		imply: <?php echo \std\jsonify($imply)?>,
		where: <?php echo \std\jsonify($where)?>,
	};

    Vue.use(httpVueLoader);
    Vue.component('render', 'url:static/vue/render.vue');

    var app = new Vue({
    	el: '#root',
    	data: data,
    });

    function locate_definition(cm, index, symbol) {
    	var regex = eval(`/(?:    )*from axiom\\.(.+) import ${symbol}\\b/`);

    	for (; index >= 0; --index) {
    		var line = cm.getLine(index);
    		console.log(line);

    		var m = line.match(regex);
    		if (m) {
    			return m[1];
    		}
    	}
    }

    function F3(cm, refresh) {
    	var cursor = cm.getCursor();
    	console.log("cursor.ch = " + cursor.ch);

    	var text = cm.getLine(cursor.line);

    	var selectionStart = cursor.ch;
    	console.log("selectionStart = " + selectionStart);

    	for (; selectionStart < text.length; ++selectionStart) {
    		var char = text[selectionStart];
    		if (char >= 'a' && char <= 'z' ||
    			char >= 'A' && char <= 'Z' ||
    			char == '_' ||
    			char >= '0' && char <= '9') {
    			continue;
    		}
    		else {
    			break;
    		}
    	}

    	var textForFocus = text.slice(0, selectionStart);
    	var m = textForFocus.match(/(\w+)(?:\.\w+)*$/);
    	var module = m[0];
    	console.log('module = ' + module);
    	switch (module) {
    		case 'apply':
    			app.$refs.render.open_apply();
    			break;

    		case 'prove':
    			break;

    		default:
    			var m = module.match(/(.+)\.apply$/);
    			if (m) {
    				module = m[1];
    				var apply = true;
    			}
    			else {
    				var apply = false;
    			}

    			m = module.match(/^axiom\.(.+)/);
    			if (m) {
    				module = m[1];
    			}

    			var symbol = null;

    			if (module.indexOf('.') < 0) {
    				switch (module) {
    					case 'algebra':
    					case 'calculus':
    					case 'discrete':
    					case 'geometry':
    					case 'keras':
    					case 'sets':
    					case 'stats':
    						break;
    					default:
    						var symbol = module;
    						module = locate_definition(cm, cursor.line, symbol);
    						if (module == null){
								var href = `/sympy/axiom.php?symbol=${symbol}`;
    			    			if (refresh)
    			    				location.href = href;
    			    			else
    			    				window.open(href);
    							return;
        					}    							
    				}
    			}
    			else {
    				m = module.match(/^(\w+)\.(.+)/);
    				switch (m[1]) {
    					case 'algebra':
    					case 'calculus':
    					case 'discrete':
    					case 'geometry':
    					case 'keras':
    					case 'sets':
    					case 'stats':
    						break;
    					default:
    						return;
    				}
    			}

    			var user = sympy_user();
    			var href = `/${user}/axiom.php?module=${module}`;

    			if (apply)
    				href += "&apply=0";
    			else if (symbol)
    				href += `&apply=${symbol}`;

    			if (refresh)
    				location.href = href;
    			else
    				window.open(href);

    			break;
    	}
    }

    var sqlFile = `<?php echo $sql_statement?>`;
    if (sqlFile) {
		console.log(`execute sql file: ${sqlFile}`);

		form_post("php/request/execute.php", { sqlFile: sqlFile }).then(res => {
			console.log('success code = ');
			console.log(res);
		}).catch(fail);
    }
	
//http://codemirror.net/doc/manual.html
//http://docs.mathjax.org/en/latest/
</script>


