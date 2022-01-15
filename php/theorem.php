<?php
// ^ *error_log
if ($input != null) {
    $inputs[] = piece_together($input);
}

$numOfReturnsFromApply = $lengths[$indexOfYield];
// error_log("lengths = " . \std\jsonify($lengths));

$latex = [];
$i = 0;
$statements = '';
// error_log("module = $module");

$content = [];

if ($data) {
    $statementsFromSQL = explode("\n", end($data));
}
else{
    $statementsFromSQL = \mysql\yield_from_mysql($module);
}

$where = '';

function is_latex_with_tabs($latex, &$matches)
{
    $matches = [];

    if (strpos($latex, "\t") !== false) {
        $array = explode("\t", $latex);

        foreach ($array as $tex) {
            if (! preg_match_all('/\\\\\[.+?\\\\\]/', $tex, $match, PREG_SET_ORDER)) {
                return false;
            }

            foreach ($match as &$statement) {
                $statement = $statement[0];
            }

            $matches[] = join('', $match);
        }
        return true;
    } else {
        if (! preg_match_all('/\\\\\[.+?\\\\\]/', $latex, $matches, PREG_SET_ORDER)) {
            return false;
        }

        foreach ($matches as &$statement) {
            $statement = $statement[0];
        }
        return true;
    }
    return false;
}

$resultsFromApply = [];

foreach ($statementsFromSQL as $statement) {

    if ($i == $indexOfYield) {
        if ($numOfReturnsFromApply == 1) {
            
            -- $lengths[$i];
            if ($lengths[$i] == 0) {
                if (is_latex_with_tabs($statement, $matches)) {                    
                    switch (count($matches)) {
                        case 3:
                            list ($given, $where, $imply) = $matches;
                            break;
                        case 2:
                            if ($numOfRequisites) {
                                list ($given, $imply) = $matches;
                                $where = '';
                            } else {
                                list ($where, $imply) = $matches;
                                $given = '';
                            }
                            break;
                        case 1:
                            $where = '';
                            $given = '';
                            $imply = $matches[0];
                            break;
                    }
                }
                
                $given = [
                    'py' => $inputs[0],
                    'latex' => $given
                ];

                $inputs = array_slice($inputs, 1);

                $statements = '';
                ++ $i;
            }
        } else {
            $resultsFromApply[] = $statement;

            -- $lengths[$i];
            if ($lengths[$i] == 0) {
                $given = array_slice($resultsFromApply, 0, $lengthOfGiven);
                $given = join('', $given);
                $given = [
                    'py' => $inputs[0],
                    'latex' => $given
                ];

                if ($lengthOfWhere) {
                    $where = array_slice($resultsFromApply, $lengthOfGiven, $lengthOfWhere);
                    $where = join('', $where);
                } else {
                    $where = '';
                }

                $imply = array_slice($resultsFromApply, $lengthOfGiven + $lengthOfWhere);
                $imply = join('', $imply);

                $statements = '';
                $inputs = array_slice($inputs, 1);
                ++ $i;
            }
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
foreach ($logs as $log) {
    $log = str_replace("\\", "\\\\", $log);
    $log = str_replace("'", "\\'", $log);
    $logStr[] = "'$log'";
}

$logStr = implode(",", $logStr);
$logStr = "[$logStr]";

?>

<title><?php echo $title;?></title>
<link rel=stylesheet href="static/codemirror/lib/codemirror.css">
<link rel=stylesheet href="static/codemirror/theme/eclipse.css">
<link rel=stylesheet href="static/codemirror/addon/hint/show-hint.css">
<style>
div {
	caret-color: transparent;
}
</style>
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

<script async src="static/unpkg.com/mathjax@3.2.0/es5/tex-chtml.js"></script>
<script src="static/unpkg.com/vue@3.2.11/dist/vue.global.prod.js"></script>
<script src="static/unpkg.com/vue3-sfc-loader@0.8.4/dist/vue3-sfc-loader.js"></script>

<script src="static/unpkg.com/axios@0.24.0/dist/axios.min.js"></script>
<script src="static/unpkg.com/qs@6.10.2/dist/qs.js"></script>

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
    updatedTime: `<?php echo isset($updatedTime)? $updatedTime: ''?>`,
});

var data = <?php echo \std\jsonify($data)?>;
if (data) {
    console.log(`update mysql data`);
    console.log(data);

    data = JSON.stringify(data);
    form_post("php/request/mysql/update.php", {data}).then(res => {
        console.log('success code = ');
        console.log(res);
    });
}

//http://codemirror.net/doc/manual.html
//http://docs.mathjax.org/en/latest/
</script>


