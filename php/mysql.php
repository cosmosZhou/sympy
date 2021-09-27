<?php
// use the following regex to remove error_log prints:
// ^ *error_log
namespace mysql;

require_once 'utility.php';
include_once 'std.php';
use mysqli, Exception;
use std\Text, std\Set, std\Queue, std\Graph;
$user = basename(dirname(dirname(__file__)));

function desc_table($table)
{
    return iterator_to_array(select("desc $table"));
}

function load_data($table, $data, $replace = true, $step = 10000)
{
    if (is_array($data)) {
        load_data_from_list($table, $data, $replace);
    } else {
        load_data_from_csv($table, $data, $replace);
    }
}

function load_data_from_list($table, $array, $replace = true, $step = 10000, $ignore = false, $truncate = false)
{
    $desc = desc_table($table);

    // error_log(\std\jsonify($desc));

    $has_training_field = False;

    $char_length = array_fill(0, count($desc), 256);
    foreach (\std\range(0, count($desc)) as $i) {
        list ($Field, $Type, , , ,) = $desc[$i];
        // $Type = implode(array_map("chr", $Type));
        if (\std\equals($Field, 'training')) {
            $has_training_field = True;
        }

        if (\std\equals($Type, 'text')) {
            $char_length[$i] = 65535;
            continue;
        }

        if (preg_match("/varchar\((\d+)\)/", $Type, $m)) {
            $char_length[$i] = (int) $m[1];
        }
    }

    // error_log(\std\jsonify($char_length));

    $folder = sys_get_temp_dir();

    foreach (\std\range(0, count($array), $step) as $i) {
        $csv = $folder . "/$table-$i.csv";

        // error_log("csv = " . $csv);
        $file = new Text($csv);

        foreach (array_slice($array, $i, $step) as $args) {
            foreach (\std\range(0, count($args)) as $i) {
                $arg = $args[$i];

                if (is_string($arg)) {
                    $arg = substr(\std\jsonify($arg), 1, - 1);
                } else {
                    $arg = \std\jsonify($arg);
                }

                if (! $ignore && strlen($arg) > $char_length[$i]) {
                    if ($truncate) {
                        $arg = substr($arg, 0, $char_length[$i]);
                    } else {
                        // error_log(\std\jsonify($args));
                        // error_log("args[$i] exceeds the allowable length " . $char_length[$i]);
                        $args = null;
                        break;
                    }
                }
                $args[$i] = $arg;
            }
            if ($args != null) {
                if ($has_training_field) {
                    $args[] = "" . rand(0, 1);
                }

                // error_log("args = " . \std\jsonify($args));
                $line = join("\t", $args);
                // error_log("line = " . $line);
                $file->append($line);
            }
        }
        $file->flush();

        // error_log(\std\jsonify($csv));

        // error_log("csv = " . $csv);
        load_data_from_csv($table, $csv, True, $replace, $ignore);
    }
}

function load_data_from_csv($table, $csv, $delete = True, $replace = true, $step = 10000)
{
    $start = time();
    // error_log("csv = " . $csv);
    $csv = str_replace('\\', '/', $csv);
    // error_log("csv = " . $csv);

    if ($replace)
        $sql = "load data local infile '$csv' replace into table $table character set utf8";
    else if ($ignore)
        $sql = "load data local infile '$csv' ignore into table $table character set utf8";
    else
        $sql = "load data local infile '$csv' into table $table character set utf8";
    // add the following line into php.ini;
    // mysqli.allow_local_infile = On

    // add the following line into my.ini;
    // [mysql]
    // local-infile=1
    // [mysqld]
    // local-infile=1

    try {
        // error_log($sql);
        execute($sql);
    } catch (Exception $e) {
        // error_log($e->getMessage());
        return;
    }

    $cost = time() - $start;
    // print('time cost =', (time.time() - start));
    if ($delete) {
        // print("os.remove(csv)", csv);
        unlink($csv);
    }

    return $cost;
}

function commit()
{
    $dbc = ConnectMysqli::getInstance();
    $dbc->commit();
}

function multi_query($sql, $resulttype = MYSQLI_ASSOC)
{
    $dbc = ConnectMysqli::getInstance();
    $array = $dbc->multi_query($sql);
    return $array;
}

function execute($sql)
{
    $dbc = ConnectMysqli::getInstance();

    try {
        $array = $dbc->query($sql);
        assert($array === true);
    } catch (Exception $e) {
        error_log($e);
        return 0;
    }

    return $dbc->affected_rows();
}

function insertmany($table, $matrix, $replace = true)
{
    $insert = $replace ? 'replace' : 'insert';

    $sql = "$insert into $table values" . implode(",", array_map(fn ($vector) => "(" . substr(\std\jsonify($vector), 1, - 1) . ")", $matrix));
//     error_log("sql = $sql");
    return execute($sql);
}

function &select($sql, $resulttype = MYSQLI_NUM) // the other choice is MYSQLI_ASSOC
{
    $dbc = ConnectMysqli::getInstance();

    // error_log("sql = $sql");
    $array = $dbc->query($sql);

    while ($row = $array->fetch_array($resulttype)) {
        yield $row;
    }
}

class ConnectMysqli
{

    public static $instance = null;

    private $link;

    private function __construct()
    {
        $config = parse_ini_file(dirname(dirname(__file__)) . "/config.ini", true)['client'];
        // error_log(\std\jsonify($config));

        $this->link = new mysqli($config['host'], $config['user'], $config['password'], $config['database']);
        if (! $this->link) {
            die('Could not connect: this->link is null');
        }
        if ($this->link->connect_error)
            die('Could not connect: ' . $this->link->connect_error);

        $this->link->query("set names utf8");
    }

    public function commit()
    {
        $this->link->commit();
    }

    public function __destruct()
    {
        // echo 'closing mysql!<br>';
        $this->link->close();
    }

    private function __clone()
    {
        die('clone is not allowed');
    }

    public static function getInstance()
    {
        if (self::$instance == null) {
            self::$instance = new self();
        }
        return self::$instance;
    }

    public function query($sql)
    {
        $array = $this->link->query($sql);
        if ($array === false) {
            throw new Exception($this->link->error);
        }
        return $array;
    }

    public function multi_query($sql)
    {
        if (is_array($sql))
            $sql = implode(';', $sql);

        $array = $this->link->multi_query($sql);
        if ($array === false) {
            throw new Exception($this->link->error);
        }
        return $array;
    }

    public function affected_rows()
    {
        return $this->link->affected_rows;
    }

    public function getInsertid()
    {
        return $this->link->insert_id;
    }

    /**
     *
     * @param
     * @return string or int
     */
    public function getOne($sql)
    {
        $query = $this->query($sql);
        return mysqli_free_result($query);
    }

    public function getRow($sql, $type = "assoc")
    {
        $query = $this->query($sql);
        if (! in_array($type, [
            "assoc",
            'array',
            "row"
        ])) {
            die("mysqli_query error");
        }
        $funcname = "mysqli_fetch_" . $type;
        return $funcname($query);
    }

    public function getFormSource($query, $type = "assoc")
    {
        if (! in_array($type, [
            "assoc",
            "array",
            "row"
        ])) {
            die("mysqli_query error");
        }
        $funcname = "mysqli_fetch_" . $type;
        return $funcname($query);
    }

    public function getAll($sql)
    {
        $query = $this->query($sql);
        $list = [];
        while ($r = $this->getFormSource($query)) {
            $list[] = $r;
        }
        return $list;
    }

    /**
     *
     * @param string $table
     * @param
     */
    public function insert($table, $data)
    {
        $key_str = '';
        $v_str = '';
        foreach ($data as $key => $v) {
            if (empty($v)) {
                die("error");
            }
            $key_str .= $key . ',';
            $v_str .= "'$v',";
        }
        $key_str = trim($key_str, ',');
        $v_str = trim($v_str, ',');
        $sql = "insert into $table ($key_str) values ($v_str)";
        $this->query($sql);
        return $this->getInsertid();
    }

    /*
     */
    public function deleteOne($table, $where)
    {
        if (is_array($where)) {
            foreach ($where as $key => $val) {
                $condition = $key . '=' . $val;
            }
        } else {
            $condition = $where;
        }
        $sql = "delete from $table where $condition";
        $this->query($sql);
        return mysqli_affected_rows($this->link);
    }

    /*
     */
    public function deleteAll($table, $where)
    {
        if (is_array($where)) {
            foreach ($where as $key => $val) {
                if (is_array($val)) {
                    $condition = $key . ' in (' . implode(',', $val) . ')';
                } else {
                    $condition = $key . '=' . $val;
                }
            }
        } else {
            $condition = $where;
        }
        $sql = "delete from $table where $condition";
        $this->query($sql);
        return mysqli_affected_rows($this->link);
    }

    /**
     *
     * @return [type]
     */
    public function update($table, $data, $where)
    {
        $str = '';
        foreach ($data as $key => $v) {
            $str .= "$key='$v',";
        }
        $str = rtrim($str, ',');
        $sql = "update $table set $str where $where";
        $this->query($sql);
        return mysqli_affected_rows($this->link);
    }
}

function select_axiom_by_state($state)
{
    global $user;
    $result = select("select axiom from tbl_axiom_py where user = '$user' and state = '$state'");
    $array = [];
    foreach ($result as &$value) {
        $array[] = $value[0];
    }
    return $array;
}

function select_axiom_by_regex($regex, $binary = false)
{
    global $user;

    if ($binary) {
        $binary = " binary ";
    } else {
        $binary = " ";
    }

    $sql = "select axiom from tbl_axiom_py where user = '$user' and axiom regexp$binary'$regex'";
    // echo $sql . "<br>";

    $result = select($sql);
    $array = [];
    foreach ($result as &$value) {
        $array[] = $value[0];
    }
    return $array;
}

function select_axiom_by_like($keyword, $binary = false)
{
    global $user;

    if ($binary) {
        $binary = " binary ";
    } else {
        $binary = " ";
    }

    $keyword = str_replace('_', '\_', $keyword);
    $sql = "select axiom from tbl_axiom_py where user = '$user' and axiom like$binary'%$keyword%'";
    // echo $sql . "<br>";

    $result = select($sql);
    $array = [];
    foreach ($result as &$value) {
        $array[] = $value[0];
    }

    // echo "result = " . \std\jsonify($result) . "<br>";
    // echo "array = " . \std\jsonify($array) . "<br>";
    return $array;
}

function select_count($state = null)
{
    global $user;

    $sql = "select count(*) from tbl_axiom_py where user = '$user'";
    if ($state) {
        $sql .= " and state = '$state'";
    }

    foreach (select($sql) as $count) {
        return $count[0];
    }
}

function select_axiom_by_state_not($state)
{
    global $user;
    yield from select("select axiom, state from tbl_axiom_py where user = '$user' and state != '$state'");
}

function yield_from_mysql($axiom)
{
    global $user;
    error_log("user = $user");

    foreach (select("select latex, timestamp from tbl_axiom_py where user = '$user' and axiom = '$axiom'") as list ($latex, $timestamp)) {
        return [
            explode("\n", $latex),
            $timestamp
        ];
    }
}

function yield_from_sql($sqlFile)
{
//     error_log("function yield_from_sql($sqlFile)");
//     error_log(file_get_contents($sqlFile));
//     error_log(\std\jsonify(explode(';', file_get_contents($sqlFile))));
    
    $text = new Text($sqlFile);

    foreach ($text as $line) {
        if (! $line) {
            continue;
        }

        if (\std\startsWith($line, 'b'))
            $line = substr($line, 2, - 1);

//         error_log("line = " . $line);
        preg_match("/update tbl_axiom_py set state = \"\w+\", lapse = \S+, latex = (\"[\s\S]+\") where user = \"\w+\" and axiom = \"\S+\"/", $line, $matches);
        $latex = $matches[1];
        $latex = eval("return $latex;");
        $latex = str_replace("\\'", "'", $latex);
        yield from explode("\n", $latex);
    }
}

function select_hierarchy($axiom, $reverse = false)
{
    global $user;
    if ($reverse) {
        $callee = 'caller';
        $caller = 'callee';
    } else {
        $callee = 'callee';
        $caller = 'caller';
    }

    try {
        foreach (select("select $callee from tbl_hierarchy_py where user = '$user' and $caller = '$axiom'") as &$result) {
            yield $result[0];
        }
    } catch (Exception $e) {
        if (preg_match("/Table '(\w+).(\w+)' doesn't exist/", $e->getMessage(), $matches)) {
            assert(\std\equals($matches[1], "axiom"));
            assert(\std\equals($matches[2], "tbl_hierarchy_py"));
        } else {
            die($e->getMessage());
        }

        $sql = <<<EOT
        CREATE TABLE `tbl_hierarchy_py` (
          `user` varchar(32) NOT NULL,
          `caller` varchar(256) NOT NULL,
          `callee` varchar(256) NOT NULL,  
          `count` int default 0,
          PRIMARY KEY (`user`, `caller`, `callee`) 
        ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
        PARTITION BY KEY () PARTITIONS 8;
        EOT;

        execute($sql);

        foreach (retrieve_all_dependency() as list ($caller, $counts)) {
            foreach ($counts as $callee => $count) {
                execute("insert into tbl_hierarchy_py values('$user', '$caller', '$callee', $count)");
            }
        }

        yield from select_hierarchy($axiom, $reverse);
    }
}

function establish_hierarchy($node, $reverse = false)
{
    $G = [];
    $setProcessed = new Set();

    $queue = new Queue();
    $queue->push($node);

    while (! $queue->isEmpty()) {
        $node = $queue->pop();
        if ($setProcessed->contains($node))
            continue;

        $setProcessed->add($node);

        // error_log("theoremSetProcessed = " . \std\jsonify($setProcessed));
        foreach (select_hierarchy($node, $reverse) as $child) {
            $queue->push($child);
            $G[$node][] = $child;
        }
    }

    $graph = new Graph();
    foreach ($G as $key => $value) {
        foreach ($value as $node) {
            $graph->insert($key, $node);
        }
    }

    return $graph;
}

function suggest($prefix, $phrase)
{
    global $user;
    $phrases = [];
    try {
        // $sql = "select phrase from tbl_suggest_py where user = '$user' and prefix = '$prefix' order by usage";
        $sql = "select phrase from tbl_suggest_py where user = '$user' and prefix = '$prefix'";
        if ($phrase) {
            $sql .= " and phrase like '%$phrase%'";
        }

        // error_log("in suggest: " . $sql);

        foreach (select($sql) as list ($word,)) {
            $phrases[] = $word;
        }
    } catch (Exception $e) {
        return [];
    }

    if ($phrase) {
        $dict = [];

        foreach ($phrases as &$word) {
            $dict[$word] = \std\startsWith($word, $phrase);
        }

        arsort($dict);
        $phrases = array_keys($dict);
    }

    return $phrases;
}

function hint($prefix)
{
    global $user;
    $phrases = [];
    // error_log($prefix);
    try {
        // $sql = "select phrase from tbl_suggest_py where user = '$user' and prefix = '$prefix' order by usage";
        $sql = "select phrase from tbl_hint_py where prefix = binary'$prefix'";
        // error_log($sql);
        foreach (select($sql) as list ($phrase,)) {
            $phrases[] = $phrase;
        }
    } catch (Exception $e) {
        return [];
    }

    return $phrases;
}

function insert_into_suggest($theorem)
{
    global $user;
    $phrases = explode('.', $theorem);
    $size = count($phrases);
    $phrases[] = 'apply';

    $prefix = '';

    $data = [];
    foreach (\std\range(0, $size) as $i) {
        $prefix .= $phrases[$i] . ".";
        $data[] = [
            $user,
            $prefix,
            $phrases[$i + 1],
            1
        ];
    }

    $rows_affected = insertmany('tbl_suggest_py', $data);
}

function delete_from_suggest($theorem, $__init__ = false, $regex = false)
{
    global $user;
    preg_match('/(.+\.)(\w+)$/', $theorem, $m);

    $prefix = $m[1];
    $phrase = $m[2];

    if ($regex) {
        // using regex engine;
        if ($__init__) {

            $sql = "delete from tbl_suggest_py where user = '$user' and prefix = '$theorem.' and phrase = 'apply'";

            $rows_affected = execute($sql);
            if ($rows_affected != 1)
                error_log("error found in $sql");
            else
                error_log("executing: $sql");
        } else {
            $sql = "delete from tbl_suggest_py where user = '$user' and prefix = '$prefix.' and phrase = '$phrase'";

            $rows_affected = execute($sql);
            if (! $rows_affected)
                error_log("error found in $sql");
            else
                error_log("executing: $sql");

            $sql = "delete from tbl_suggest_py where user = '$user' and prefix regexp '^$theorem\..*'";

            $rows_affected = execute($sql);
            if (! $rows_affected)
                error_log("error found in $sql");
            else
                error_log("executing: $sql");
        }
    } else {

        if (! $__init__) {
            $sql = "delete from tbl_suggest_py where user = '$user' and prefix = '$prefix' and phrase = '$phrase'";

            $rows_affected = execute($sql);
            if (! $rows_affected)
                error_log("error found in $sql");
            else
                error_log("executing: $sql");
        }

        $sql = "delete from tbl_suggest_py where user = '$user' and prefix = '$theorem.' and phrase = 'apply'";

        $rows_affected = execute($sql);
        if (! $rows_affected)
            error_log("error found in $sql");
        else
            error_log("executing: $sql");
    }
}

function update_suggest($package, $old, $new, $is_folder = false)
{
    global $user;
    if ($new == null) {
        $sql = "delete from tbl_suggest_py where user = '$user' and prefix = '$package.' and phrase = '$old'";
    } else if ($is_folder) {
        $package_regex = str_replace(".", "\\.", $package);
        $sql = "update tbl_suggest_py set prefix = regexp_replace(prefix, '^$package_regex\\.$old\\.(.+)', '$package.$new.$1') where user = '$user' and prefix like '$package.$old.%'";
    } else
        $sql = "update tbl_suggest_py set phrase = '$new' where user = '$user' and prefix = '$package' and phrase = '$old'";

//     error_log("sql = $sql");

    $rows_affected = \mysql\execute($sql);
    if ($rows_affected < 1) {
        error_log("error found in $sql");
    }
}

function delete_from_axiom($old, $regex = false)
{
    global $user;

    if ($regex) {
        // using regex engine;
        $sql = "delete from tbl_axiom_py where user = '$user' and axiom regexp '^$old'";
        $rows_affected = \mysql\execute($sql);
    } else {
        $sql = "delete from tbl_axiom_py where user = '$user' and axiom = '$old'";
        $rows_affected = \mysql\execute($sql);
    }

    if (! $rows_affected) {
        error_log("$sql");
    }
}

function update_axiom($old, $new, $is_folder = false)
{
    global $user;

    if ($is_folder) {
        $old_regex = str_replace('.', "\\.", $old);
        $sql = "update tbl_axiom_py set axiom = regexp_replace(axiom, '^$old_regex\.(.+)', '$new.$1') where user = '$user' and axiom like '$old.%'";
    } else {
        $sql = "update tbl_axiom_py set axiom = '$new' where user = '$user' and axiom = '$old'";
    }

//     error_log("sql = $sql");
    $rows_affected = \mysql\execute($sql);
    if ($rows_affected < 1) {
        error_log("error found in $sql");
    }
}

function replace_with_callee($old, $new)
{
    $old_regex = str_replace('.', "\\.", $old);
    $old_regex_hierarchy = "$old_regex(?!\.)|$old_regex(?=\.apply\b)";
    global $user;
    foreach (\mysql\select("select caller from tbl_hierarchy_py where user = '$user' and callee = '$old'") as list ($caller,)) {
        $pyFile = module_to_py($caller);
        $pyFile = new Text($pyFile);

        $pyFile->preg_replace($old_regex_hierarchy, $new);
    }

    $old_regex = "(?<=from axiom\.)$old_regex(?= import \w+)";
    // php doesn't support variable-lenth looking-behind assertion
    // $old_regex = "(?<=^ *from axiom\.)$old_regex(?= import \w+)";
    foreach (\mysql\select("select caller from tbl_function_py where user = '$user' and callee = '$old'") as list ($caller,)) {
        $pyFile = module_to_py($caller);
        $pyFile = new Text($pyFile);

        $pyFile->preg_replace($old_regex, $new);
    }
}

function reaplce_axiom_in_hierarchy($old, $new)
{
    global $user;
    error_log("sql = update tbl_hierarchy_py set caller = '$new' where user = '$user' and caller = '$old'");
    $rows_affected = \mysql\execute("update tbl_hierarchy_py set caller = '$new' where user = '$user' and caller = '$old'");

    error_log("sql = update tbl_hierarchy_py set callee = '$new' where user = '$user' and callee = '$old'");
    $rows_affected = \mysql\execute("update tbl_hierarchy_py set callee = '$new' where user = '$user' and callee = '$old'");

    error_log("sql = update tbl_function_py set caller = '$new' where user = '$user' and caller = '$old'");
    $rows_affected = \mysql\execute("update tbl_function_py set caller = '$new' where user = '$user' and caller = '$old'");

    error_log("sql = update tbl_function_py set callee = '$new' where user = '$user' and callee = '$old'");
    $rows_affected = \mysql\execute("update tbl_function_py set callee = '$new' where user = '$user' and callee = '$old'");
}

function update_hierarchy($old, $new, $is_folder = false)
{
    global $user;
    if ($is_folder) {
        $old_regex = str_replace('.', "\\.", $old);

        $replaceDict = [];
        foreach (\mysql\select("select axiom from tbl_axiom_py where user = '$user' and axiom like '$old.%'") as list ($axiom,)) {
            $oldAxiom = $axiom;
            $newAxiom = preg_replace("/^$old_regex\.(.+)/", "$new.$1", $oldAxiom);

            $replaceDict[$oldAxiom] = $newAxiom;
            error_log("replace $oldAxiom with $newAxiom");
        }

        foreach ($replaceDict as $old => $new) {
            replace_with_callee($old, $new);
        }
        // these two for loop cannot be combined because results of replace_with_callee depend on reaplce_axiom_in_hierarchy
        foreach ($replaceDict as $old => $new) {
            reaplce_axiom_in_hierarchy($old, $new);
        }
    } else {
        // update the python files that contains $old theorem!
        $sql = "select caller from tbl_hierarchy_py where user = '$user' and callee = '$old'";

//         error_log("sql = $sql");

        replace_with_callee($old, $new);

        reaplce_axiom_in_hierarchy($old, $new);
    }
}
?>