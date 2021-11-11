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

// error_log("module = $module");

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

$logStr = [];
foreach ($logs as $log){
    $log = str_replace("\\", "\\\\", $log);
    $log = str_replace("'", "\\'", $log);    
    $logStr[] = "'$log'";
}

$logStr = implode(",", $logStr);
$logStr = "[$logStr]";

?>

<title><?php echo $module;?></title>
<link rel=stylesheet href="static/codemirror/lib/codemirror.css">
<link rel=stylesheet href="static/codemirror/theme/eclipse.css">
<link rel=stylesheet href="static/codemirror/addon/hint/show-hint.css">
<body></body>

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
                  }, 700);
                });                  
        }
      },

    tex: {
        maxBuffer: 60 * 1024,       // maximum size for the internal TeX string (10K)
        //reference: http://docs.mathjax.org/en/latest/options/input/tex.html?highlight=MAXBUFFER#the-configuration-block
    },
};
</script>

<script async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"></script>
<script src="https://unpkg.com/vue@3.2.11/dist/vue.global.prod.js"></script>
<script src="https://cdn.jsdelivr.net/npm/vue3-sfc-loader/dist/vue3-sfc-loader.js"></script>

<script src="https://cdn.jsdelivr.net/npm/axios/dist/axios.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/qs/dist/qs.js"></script>

<script src='static/js/std.js'></script>
<script src='static/js/utility.js'></script>

<script type=module>
import * as codemirror from "./static/codemirror/lib/codemirror.js";
import * as python from "./static/codemirror/mode/python/python.js";
import * as active_line from "./static/codemirror/addon/selection/active-line.js";
import * as show_hint from "./static/codemirror/addon/hint/show-hint.js";
import * as matchbrackets from "./static/codemirror/addon/edit/matchbrackets.js";

var logs = <?php echo $logStr?>;

var error = [];
//console.log(logs);
for (let i = 0; i < logs.length; ++i){
    var log = logs[i];
    if (log.startsWith('{') && log.endsWith('}')){
    	error.push(JSON.parse(log));
    	logs.remove(i);
        break;
    }
    
    if (log.startsWith('[') && log.endsWith(']')){
    	logs.remove(i);
        error = JSON.parse(log);
        break;
    }
}

createApp('render', {
	error : error,
    logs : logs,
    prove : <?php echo \std\jsonify($prove)?>,
    unused : <?php echo \std\jsonify($unused)?>,
    module: <?php echo \std\jsonify($module)?>,
    given: <?php echo \std\jsonify($given)?>,
    imply: <?php echo \std\jsonify($imply)?>,
    where: <?php echo \std\jsonify($where)?>,
    createdTime: `<?php echo $createdTime?>`,
    updatedTime: `<?php echo $updatedTime?>`,
});

var sqlFile = `<?php echo $sql_statement?>`;
if (sqlFile) {
    console.log(`execute sql file: ${sqlFile}`);

    form_post("php/request/mysql/update.php", { sqlFile: sqlFile }).then(res => {
        console.log('success code = ');
        console.log(res);
    });
}

//http://codemirror.net/doc/manual.html
//http://docs.mathjax.org/en/latest/
</script>


