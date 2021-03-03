<?php
require_once 'utility.php';
function get_count()
{
    $count = 0;
    foreach (read_all_php(dirname(__file__)) as $php) {
        // https://www.php.net/manual/en/function.substr.php
        $py = substr($php, 0, - 3) . 'py';
        if (! file_exists($py)) {
            continue;
        }

        ++ $count;
    }
    return $count;
}

 
foreach ($_POST as $key => $value) {
    switch ($key) {
        case 'query':
            switch ($value) {
                case 'count':
                    echo(get_count());
            }
    }
}

foreach ($_GET as $key => $value) {
    switch ($key) {
        case 'query':
            switch ($value) {
                case 'count':
                    echo(get_count());
            }
    }
}

?>