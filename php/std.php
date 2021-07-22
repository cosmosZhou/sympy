<?php
namespace std;

// use the following regex to remove error_log prints:
// ^ *error_log
use Iterator, JsonSerializable, IteratorAggregate, RuntimeException;

// implement common collections like: Set, Queue, Graph
class QueueIterator implements Iterator
{

    private $_queue;

    private $_index;

    public function __construct($array)
    {
        $this->_queue = $array;
        $this->_index = 0;
    }

    // Rewind the Iterator to the first element
    public function rewind()
    {
        $this->_index = 0;
    }

    // Return the current element
    public function current()
    {
        return $this->_queue->get($this->_index);
    }

    // Return the key of the current element
    public function key()
    {
        return $this->_index;
    }

    // Move forward to next element
    public function next()
    {
        ++ $this->_index;
        return $this;
    }

    // Checks if current position is valid
    public function valid()
    {
        return $this->_index < $this->_queue->size();
    }
}

/**
 * Class Queue for FIFO
 */
class Queue implements JsonSerializable, IteratorAggregate
{

    /**
     *
     * @var int pointer to the front
     *     
     */
    private $_start;

    /**
     *
     * @var int pointer to the rear
     *     
     */
    private $_stop;

    /**
     *
     * @var array data
     *     
     */
    private $_array;

    /**
     *
     * @var int the actual capacity of queue;
     *     
     */
    private $_capacity;

    /**
     *
     * Queue constructor.
     *
     * @param int $capacity
     *
     */
    public function __construct($capacity = 4)

    {
        $this->_array = [];

        $this->_start = 0;

        $this->_stop = 0;

        $this->_capacity = $capacity;
    }

    /**
     * destructor
     */
    public function __destruct()
    {
        unset($this->_array);
    }

    /**
     *
     * @method enqueue
     *        
     * @param mixed $elem
     *
     * @return bool
     *
     */
    public function push($elem)
    {
        if ($this->size() == $this->_capacity) {
            $this->expand();
        }

        $this->_array[$this->_stop % $this->_capacity] = $elem;

        ++ $this->_stop;
    }

    private function expand()
    {
        $array = [];
        foreach ($this as $value) {
            $array[] = $value;
        }

        $this->_capacity *= 2;
        $this->_start = 0;
        $this->_stop = count($array);
        $this->_array = $array;
    }

    /**
     *
     * @method dequeue
     *        
     * @return mixed|null
     *
     */
    public function pop()
    {
        if ($this->isEmpty())
            return null;

        $elem = $this->_array[$this->_start];

        ++ $this->_start;

        if ($this->_start == $this->_capacity) {
            $this->_start = 0;
            $this->_stop -= $this->_capacity;
        }

        return $elem;
    }

    /**
     *
     * @method check whether the queue is empty
     *        
     * @return bool
     *
     */
    public function isEmpty()
    {
        return $this->size() === 0;
    }

    public function size()
    {
        assert($this->_stop >= $this->_start);
        return $this->_stop - $this->_start;
    }

    public function capacity()
    {
        return $this->_capacity;
    }

    public function get($index)
    {
        assert($index >= 0);
        assert($index < $this->size(), "index out of bound, index = $index, size = " . $this->size());

        $index += $this->_start;
        if ($index >= $this->_capacity) {
            $index -= $this->_capacity;
        }

        return $this->_array[$index];
    }

    // Required definition of interface IteratorAggregate
    public function getIterator()
    {
        return new QueueIterator($this);
    }

    /**
     *
     * @method clear the whole queue.
     *        
     */
    public function clear()
    {
        $this->_array = [];
        $this->_start = 0;
        $this->_stop = 0;
    }

    public function jsonSerialize()
    {
        $array = [];
        foreach ($this as $value) {
            $array[] = $value;
        }

        return $array;
    }
}

class SetIterator implements Iterator
{

    private $_array;

    private $_valid;

    public function __construct($array)
    {
        $this->_array = $array;
        $this->_valid = count($this->_array) ? true : false;
    }

    // Rewind the Iterator to the first element
    public function rewind()
    {
        reset($this->_array);
    }

    // Return the current element
    public function current()
    {
        return key($this->_array);
    }

    // Return the key of the current element
    public function key()
    {
        return key($this->_array);
    }

    // Move forward to next element
    public function next()
    {
        $this->_valid = next($this->_array) === false ? false : true;
        return $this;
    }

    // Checks if current position is valid
    public function valid()
    {
        return $this->_valid;
    }
}

class Set implements JsonSerializable, IteratorAggregate
{

    private $set;

    public function __construct($array = [])
    {
        $this->set = [];
        $this->addAll($array);
    }

    public function add($element)
    {
        $this->set[$element] = true;
    }

    public function addAll($elements)
    {
        foreach ($elements as $e) {
            $this->set[$e] = true;
        }
    }

    public function peek()
    {
        foreach ($this as $e) {
            return $e;
        }
    }

    public function complement($set)
    {
        $complement = new Set();
        foreach ($this as $e) {
            if (! $set->contains($e))
                $complement->add($e);
        }
        return $complement;
    }

    public function remove($element)
    {
        unset($this->set[$element]);
    }

    public function removeAll($elements)
    {
        foreach ($elements as $e) {
            unset($this->set[$e]);
        }
    }

    public function enumerate()
    {
        foreach ($this->set as $key => &$_) {
            yield $key;
        }
    }

    public function contains($element)
    {
        return array_key_exists($element, $this->set);
    }

    public function isEmpty()
    {
        return count($this->set) == 0;
    }

    // Required definition of interface IteratorAggregate
    public function getIterator()
    {
        return new SetIterator($this->set);
    }

    public function jsonSerialize()
    {
        $array = [];
        foreach ($this as $value) {
            $array[] = $value;
        }
        return $array;
    }

    public function __toString()
    {
        return jsonify($this->jsonSerialize());
    }
}

class Graph implements JsonSerializable, IteratorAggregate
{

    public $graph;

    private $permanent_mark;

    private $temporary_mark;

    function visit($n)
    {
        // error_log("visiting key = $n");
        if ($this->permanent_mark->contains($n))
            return null;

        if ($this->temporary_mark->contains($n))
            return $n;

        if (array_key_exists($n, $this->graph)) {

            $this->temporary_mark->add($n);
            // error_log("this->graph[n] = " . jsonify($this->graph[$n]));

            foreach ($this->graph[$n] as $m) {
                $node = $this->visit($m);
                if ($node != null)
                    return $node;
            }

            $this->temporary_mark->remove($n);
        }

        $this->permanent_mark->add($n);
        return null;
    }

    function visit_and_traceback($n, &$parent)
    {
        // error_log("visiting key = $n");
        if ($this->permanent_mark->contains($n))
            return null;

        if ($this->temporary_mark->contains($n)) {
            return $n;
        }

        if (array_key_exists($n, $this->graph)) {

            $this->temporary_mark->add($n);
            // error_log("this->graph[n] = " . jsonify($this->graph[$n]));

            foreach ($this->graph[$n] as $m) {
                $node = $this->visit_and_traceback($m, $parent);
                if ($node != null) {
                    $parent[] = $m;
                    return $node;
                }
            }

            $this->temporary_mark->remove($n);
        }

        $this->permanent_mark->add($n);
        return null;
    }

    function initialize_topology()
    {
        $this->permanent_mark = new Set();
        $this->temporary_mark = new Set();
    }

    function &topological_sort_depth_first()
    {
        $this->initialize_topology();
        foreach ($this->graph as $n => $_) {
            if ($this->visit($n))
                return null;
        }

        return $this->L;
    }

    function detect_cycle($key)
    {
        $this->initialize_topology();
        return $this->visit($key);
    }

    function detect_cycle_traceback($key, &$parent)
    {
        $this->initialize_topology();
        $this->visit_and_traceback($key, $parent);
    }

    public function __construct()
    {
        $this->graph = [];
    }

    function convert_set_to_list()
    {
        foreach ($this->graph as $key => &$value) {
            $this->graph[$key] = iterator_to_array($value->enumerate());
        }
    }

    function insert($from, $to)
    {
        if (! array_key_exists($from, $this->graph)) {
            $this->graph[$from] = new Set();
        }

        $this->graph[$from]->add($to);
    }

    // Required definition of interface IteratorAggregate
    public function getIterator()
    {
        return new GraphIterator($this->graph);
    }

    public function jsonSerialize()
    {
        return $this->graph;
    }
}

class GraphIterator implements Iterator
{

    private $_array;

    private $_valid;

    private $set_iterator;

    private $_key = 0;

    public function __construct($array)
    {
        $this->_array = $array;
        $this->_valid = count($this->_array) ? true : false;
    }

    // Rewind the Iterator to the first element
    public function rewind()
    {
        reset($this->_array);
        $this->set_iterator = current($this->_array)->getIterator();
    }

    // Return the current element
    public function current()
    {
        return [
            key($this->_array),
            $this->set_iterator->current()
        ];
    }

    // Return the key of the current element
    public function key()
    {
        return $this->_key;
    }

    // Move forward to next element
    public function next()
    {
        $this->set_iterator->next();
        if ($this->set_iterator->valid()) {
            $this->_valid = true;
        } else {
            $this->_valid = next($this->_array) === false ? false : true;
            if ($this->_valid) {
                $this->set_iterator = current($this->_array)->getIterator();
            }
        }
        ++ $this->_key;
        return $this;
    }

    // Checks if current position is valid
    public function valid()
    {
        return $this->_valid;
    }
}

function createDirectory($dir)
{
    if (! is_dir($dir)) {
        if (! mkdir($dir, 0777, true)) {
            throw new RuntimeException("fail to create directory $dir");
        }
    }
}

// delete a non-empty Directory recursively
function deleteDirectory($directory)
{
    if (! file_exists($directory)) {
        return;
    }

    if ($dir_handle = opendir($directory)) {

        while ($filename = readdir($dir_handle)) {

            if ($filename != '.' && $filename != '..') {

                $subFile = $directory . "/" . $filename;

                if (is_dir($subFile)) {
                    deleteDirectory($subFile);
                } elseif (is_file($subFile)) {
                    unlink($subFile);
                }
            }
        }

        closedir($dir_handle);

        rmdir($directory);
    }
}

// delete a non-empty Directory recursively
function renameDirectory($directory, $newDirectory)
{
    createDirectory($newDirectory);
    if (! file_exists($directory)) {
        return;
    }

    if ($dir_handle = opendir($directory)) {

        while ($filename = readdir($dir_handle)) {

            if ($filename != '.' && $filename != '..') {

                $subFile = $directory . "/" . $filename;
                $_subFile = $newDirectory . "/" . $filename;

                if (is_dir($subFile)) {
                    renameDirectory($subFile, $_subFile);
                } elseif (is_file($subFile)) {

                    rename($subFile, $_subFile);
                }
            }
        }

        closedir($dir_handle);

        rmdir($directory);
    }
}

function createNewFile($path)
{
    $dir = dirname($path);
    createDirectory($dir);

    $myfile = fopen($path, "w");
    if (! $myfile) {
        throw new RuntimeException("fail to create file $path");
    }

    fclose($myfile);
}

class Text implements IteratorAggregate
{

    private $file;

    public function __construct($path)
    {
        // error_log("path = " . $path);
        if (file_exists($path)) {
            $this->file = fopen($path, "r+");
        } else {
            createNewFile($path);
            $this->file = fopen($path, "w+");
        }

        if ($this->file === false) {
            createNewFile($path);
            $this->file = fopen($path, "w+");

            if ($this->file === false) {
                throw new RuntimeException("fail to open file $path");
            }
        }

        $this->rewind();
        // $this->strip = strip
    }

    public function __destruct()
    {
        fclose($this->file);
    }

    // Required definition of interface IteratorAggregate
    public function getIterator()
    {
        // error_log("public function getIterator()");
        return new TextIterator($this->file);
    }

    public function rewind()
    {
        // error_log("public function rewind()");
        \rewind($this->file);
        Text::skipByteOrderMark($this->file);
    }

    public function seek($offset, $pivot)
    {
        return fseek($this->file, $offset, $pivot);
    }

    public function end()
    {
        $this->seek(0, SEEK_END);
    }

    public static function skipByteOrderMark($file)
    {
        // error_log("public static function skipByteOrderMark(file)");
        $byteOrderMark = fread($file, 1);

        // error_log("byteOrderMark = " . jsonify($byteOrderMark));
        if ($byteOrderMark && ord($byteOrderMark) != 0xFEFF) {
            // error_log("rewind() is called again!");
            \rewind($file);
        }
    }

    public function append($s, $end_of_line = "\n")
    {
        $this->end();

        if (is_string($s)) {
            fwrite($this->file, $s . $end_of_line);
        } else {
            foreach ($s as $s) {
                fwrite($this->file, $s . $end_of_line);
            }
        }
    }

    public function flush()
    {
        fflush($this->file);
    }

    public function tell()
    {
        return ftell($this->file);
    }

    public function truncate()
    {
        $pos = $this->tell();

        ftruncate($this->file, $pos);
    }

    public function write($s)
    {
        fwrite($this->file, $s);
    }

    public function writelines($ss)
    {
        $this->rewind();
        fwrite($this->file, implode("\n", $ss));
        $this->truncate();
    }

    public function read($size)
    {
        return fread($this->file, $size);
    }

    public function readlines()
    {
        return iterator_to_array($this);
    }

    public function isEmpty()
    {
        foreach ($this as $line) {
            return False;
        }
        return true;
    }

    public function endsWith($end)
    {
        $this->end();
        $size = strlen($end);
        $offset = $this->tell() - $size;
        if ($offset < 0)
            return False;

        $this->seek($offset, SEEK_SET);

        return $this->read($size) == $end;
    }

    public function setitem($index, $newLine)
    {
        // $this->rewind();
        $i = 0;
        $lines = [];
        foreach ($this as $line) {
            if ($i == $index)
                $lines[] = $newLine;
            else
                $lines[] = $line;
            ++ $i;
        }

        $this->rewind();

        $this->write(implode("\n", $lines));
        $this->truncate();
    }

    public function insert($index, $newLine)
    {
        $i = 0;
        $lines = [];
        foreach ($this as $line) {
            if ($i == $index) {
                if (is_array($newLine)) {
                    array_push($lines, ...$newLine);
                } else {
                    $lines[] = $newLine;
                }
            }

            $lines[] = $line;
            ++ $i;
        }

        $this->rewind();
        $this->write(implode("\n", $lines));
        $this->truncate();
    }

    public function delitem($index)
    {
        error_log("index = $index");
        // $this->rewind();
        $i = 0;
        $lines = [];
        foreach ($this as $line) {
            if ($i != $index)
                $lines[] = $line;
            ++ $i;
        }

        $this->rewind();

        error_log("lines = " . jsonify($lines));
        $this->clear();
        $this->write(implode("\n", $lines));
        $this->truncate();
    }

    public function clear()
    {
        $this->rewind();
        $this->write('');
        $this->truncate();
        $this->flush();
    }

    public function search($regex)
    {
        $regex = "/$regex/";
        // $this->rewind();
        foreach ($this as $line) {
            if (preg_match($regex, $line, $m)) {
                return true;
            }
        }
        return false;
    }

    public function replace($old, $new)
    {
        // $this->rewind();
        $lines = [];
        foreach ($this as $line) {
            $lines[] = str_replace($old, $new, $line);
        }

        $this->rewind();

        $this->write(implode("\n", $lines));
        $this->truncate();
    }

    public function preg_replace($old, $new)
    {
        $old = "/$old/";
        $lines = [];
        foreach ($this as $line) {
            $lines[] = preg_replace($old, $new, $line);
        }

        $this->rewind();

        $this->write(implode("\n", $lines));
        $this->truncate();
    }

    public function preg_match($regex)
    {
        $regex = "/$regex/";
        $lines = [];
        foreach ($this as $line) {
            if (preg_match($regex, $line)) {
                $lines[] = $line;
            }
        }

        return $lines;
    }

    public function retain($regex)
    {
        $regex = "/$regex/";
        $lines = [];
        $linesRemoved = [];
        foreach ($this as $line) {
            if (preg_match($regex, $line)) {
                $lines[] = $line;
            } else {
                $linesRemoved[] = $line;
            }
        }
        $this->writelines($lines);
        return $linesRemoved;
    }
}

class TextIterator implements Iterator
{

    private $file;

    private $line = 0;

    public function __construct($file)
    {
        // error_log("public function TextIterator::__construct(file)");
        $this->file = $file;
    }

    // Rewind the Iterator to the first element
    public function rewind()
    {
        // error_log("public function TextIterator::rewind()");
        \rewind($this->file);
        Text::skipByteOrderMark($this->file);
    }

    // Return the current element
    public function current()
    {
        // error_log("public function current()");
        $line = fgets($this->file);
        // error_log("line = " . $line);
        return rtrim($line);
    }

    // Return the key of the current element
    public function key()
    {
        // error_log("public function key()");
        return $this->line;
    }

    // Move forward to next element
    public function next()
    {
        // error_log("public function next()");
        ++ $this->line;
        return $this;
    }

    // Checks if current position is valid
    public function valid()
    {
        // error_log("public function valid()");
        // if (is_bool($this->file)) {
        // return false;
        // }
        try {
            return ! feof($this->file);
        } catch (Exception $e) {
            return false;
        }
    }
}

function get_extension($file)
{
    return pathinfo($file, PATHINFO_EXTENSION);
}

function equals($lhs, $rhs)
{
    return ! strcmp($lhs, $rhs);
}

function startsWith($haystack, $needle)
{
    $length = strlen($needle);
    return substr($haystack, 0, $length) === $needle;
}

function endsWith($haystack, $needle)
{
    $length = strlen($needle);
    if ($length == 0) {
        return true;
    }

    return substr($haystack, - $length) === $needle;
}

function quote($param)
{
    if (strpos($param, "'") !== false) {
        $param = str_replace("'", "&apos;", $param);
    }

    return $param;
}

function jsonify($param)
{
    return json_encode($param, JSON_UNESCAPED_UNICODE);
}

function read_directory($dir)
{
    if (is_dir($dir)) {

        $handle = opendir($dir);

        if ($handle) {
            while (($fl = readdir($handle)) !== false) {
                $temp = $dir . DIRECTORY_SEPARATOR . $fl;

                if ($fl == '.' || $fl == '..') {
                    continue;
                }

                if (is_dir($temp)) {
                    yield $temp;
                }
            }
            closedir($handle);
        }
    }
}

function read_files($dir, $ext = null)
{
    if (is_dir($dir)) {

        $handle = opendir($dir);

        if ($handle) {
            while (($fl = readdir($handle)) !== false) {
                $temp = $dir . DIRECTORY_SEPARATOR . $fl;
                if ($fl == '.' || $fl == '..') {
                    continue;
                }

                if (! is_dir($temp)) {
                    if ($ext == null || equals(get_extension($temp), $ext)) {
                        yield $temp;
                    }
                }
            }
            closedir($handle);
        }
    }
}

function read_all_files($dir, $ext)
{
    if (is_dir($dir)) {

        $handle = opendir($dir);

        if ($handle) {
            while (($fl = readdir($handle)) !== false) {
                if ($fl == '.' || $fl == '..') {
                    continue;
                }

                $temp = $dir . DIRECTORY_SEPARATOR . $fl;

                if (is_dir($temp)) {
                    // echo 'directory : ' . $temp . '<br>';
                    yield from read_all_files($temp, $ext);
                } else {
                    if (equals(get_extension($temp), $ext)) {
                        yield $temp;
                    }
                }
            }
            closedir($handle);
        }
    }
}

function removedir($dir)
{
    foreach (read_files($dir) as $file) {
        unlink($file);
    }

    foreach (read_directory($dir) as $subdir) {
        removedir($subdir);
    }
    rmdir($dir);
}

function recursive_construct($parentheses, $depth)
{
    $mid = strlen($parentheses) / 2;
    $start = substr($parentheses, 0, $mid);
    $end = substr($parentheses, $mid);

    if (need_escape($start)) {
        $start = "\\" . $start;
        $end = "\\" . $end;
    }

    if ($depth == 1)
        return "${start}[^$parentheses]*$end";
    return "${start}[^$parentheses]*(?:" . recursive_construct($parentheses, $depth - 1) . "[^$parentheses]*)*$end";
}

function balancedGroups($parentheses, $depth, $multiple = true)
{
    $regex = recursive_construct($parentheses, $depth);
    if ($multiple)
        return "((?:$regex)*)";
    else
        return "(?:$regex)";
}

function balancedParentheses($depth, $multiple = false)
{
    return balancedGroups("()", $depth, $multiple);
}

function balancedBrackets($depth, $multiple = false)
{
    return balancedGroups("\[\]", $depth, $multiple);
}

function need_escape($s)
{
    switch ($s) {
        case "(":
        case ")":
        case "{":
        case "}":
            return true;
        default:
            return false;
    }
}

function preg_match_u($regex, $str, &$matches)
{
    return preg_match($regex . "u", $str, $matches);
}

function range($start, $stop, $step = 1)
{
    for ($i = $start; $i < $stop; $i += $step) {
        yield $i;
    }
}

function establish_hierarchy($node, $select_hierarchy)
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

        error_log("setProcessed = " . \std\jsonify($setProcessed));
        foreach ($select_hierarchy($node) as $child) {
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

function slice(&$s, $start, $stop = null)
{
    if ($stop == null)
        return substr($s, $start);
    return substr($s, $start, $stop - $start);
}

function println($s)
{
    print($s . "\n");
}

// function join($delimiter, $array)
// {
// $s = $array[0];
// foreach (range(1, count($array)) as $i) {
// $s .= $delimiter . $array[$i];
// }
// return $s;
// }
function get_utf8_char_len($byte)
{
    // for error: return 0
    // for valid results: return 1-6
    // never return other value

    // UTF8 encoding format：
    // 0 1 2 3 4 5
    // U-00000000 - U-0000007F: 0xxxxxxx
    // U-00000080 - U-000007FF: 110xxxxx 10xxxxxx
    // U-00000800 - U-0000FFFF: 1110xxxx 10xxxxxx 10xxxxxx
    // U-00010000 - U-001FFFFF: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
    // U-00200000 - U-03FFFFFF: 111110xx 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx
    // U-04000000 - U-7FFFFFFF: 1111110x 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx 10xxxxxx
    $len = 0;
    $mask = 0x80;
    while ($byte & $mask) {
        ++ $len;
        if ($len > 6) {
            println(__FUNCTION__);
            println("illegal char encountered" . $byte);
            // cerr << "The mask get len is over 6." << endl;
            return 0;
        }
        $mask >>= 1;
    }
    if (0 == $len) {
        return 1;
    }
    return $len;
}

function array_insert(&$array, $index, $value)
{
    $newArray = [
        $value
    ];

    if ($index < count($array)) {
        $newArray[] = $array[$index];
    }

    array_splice($array, $index, 1, $newArray);
}

function array_delete(&$array, $index)
{
    array_splice($array, $index, 1);
}

function is_linux()
{
    return DIRECTORY_SEPARATOR == '/';
}

function post($url, $data = null, $json = True)
{
    if ($data == null)
        $data = [];

    $postdata = http_build_query($data);

    $opts = [
        'http' => [
            'method' => 'POST',
            'header' => 'Content-type: application/x-www-form-urlencoded',
            'content' => $postdata,
            "timeout" => 3600
        ]
    ];

    $context = stream_context_create($opts);

    $result = file_get_contents($url, false, $context);

    if ($json)
        return json_decode($result, True);
    
    return $result;
}

?>
