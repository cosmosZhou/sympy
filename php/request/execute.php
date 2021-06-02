<?php
require_once '../utility.php';
require_once '../mysql.php';
use std\Text;

$dict = empty($_POST) ? $_GET : $_POST;

$sqlFile = $dict['sqlFile'];

// error_log("fetching $sqlFile");
$file = new Text($sqlFile);
// never put new Text($sqlFile) inside the loop! it will cause the following infinite loop!
// feof(): supplied resource is not a valid stream resource

$ROOT = $_SERVER['DOCUMENT_ROOT'];

foreach ($file as $query) {
    if (! $query)
        continue;
    $query = substr($query, 0, - 1);

    error_log("executing $query");

    if (! empty($query) && $query != ";") {
        \mysql\execute($query);
    }

    if (! preg_match("/replace into tbl_axiom_py values\((.+)\)/", $query, $m)) {
        continue;
    }

    list ($user, $axiom, , ,) = json_decode("[" . $m[1] . "]");
    error_log("user = $user");
    error_log("axiom = $axiom");

    $tuples = [];

    $tokens = explode('.', $axiom);
    $prefix = "";

    $size = count($tokens) - 1;
    for ($i = 0; $i < $size; ++ $i) {
        $prefix .= $tokens[$i] . ".";
        $phrase = $tokens[$i + 1];
        $usage = 1;

        $tuples[] = [
            $user,
            $prefix,
            $phrase,
            $usage
        ];
    }

    error_log(\std\jsonify($tuples));
    \mysql\insertmany("tbl_suggest_py", $tuples);

    $theorem = str_replace('.', '/', $axiom);
    $py = $ROOT . "/" . $user . "/axiom/$theorem.py";
    error_log("py = $py");
    $linkCount = [];
    foreach (yield_from_py($py) as $dict) {
        if (array_key_exists('a', $dict)) {
            $a = $dict['a'];
            foreach ($a as $line => $link) {
                if (! array_key_exists($link, $linkCount)) {
                    $linkCount[$link] = 0;
                }
                ++ $linkCount[$link];
            }
        }
    }

    error_log("linkCount = " . \std\jsonify($linkCount));

    $tuples = [];
    $caller = $axiom;
    foreach ($linkCount as $callee => $count) {
        $tuples[] = [
            $user,
            $caller,
            $callee,
            $count
        ];
    }
    
    \mysql\execute("delete from tbl_hierarchy_py where user = '$user' and caller = '$caller'");
    \mysql\insertmany("tbl_suggest_py", $tuples, false);
}

// error_log("deleting $sqlFile");
unlink($sqlFile);

?>