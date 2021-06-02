<?php
namespace nlp;

require_once 'utility.php';

abstract class TreeNode
{

    abstract function append_left_brace();

    function replace($old, $new)
    {}

    function printf()
    {
        $caret = $this;
        while ($caret != null) {
            print($caret);
            $caret = $caret->parent;
        }
        print('\n');
    }

    abstract function append_lexeme($lexeme);

    abstract function __toString();

    abstract function rawtext();

    public $parent = null;
}

class TreeNodeCaret extends TreeNode
{

    function append_left_brace()
    {
        $caret = new TreeNodeCaret();
        $parenthesis = new TreeNodeBrace($caret, $this->parent);
        if ($this->parent != null) {
            $this->parent->replace($this, $parenthesis);
        }
        return $caret;
    }

    function append_lexeme($lexeme)
    {
        $caret = new TreeNodeLexeme($lexeme, $this->parent);
        if ($this->parent != null) {
            $this->parent->replace($this, $caret);
        }
        return $caret;
    }

    public function __toString()
    {
        return "";
    }

    public function rawtext()
    {
        return "";
    }
}

class TreeNodeBrace extends TreeNode
{

    protected $ptr;

    public function __construct($hNode, $parent = null)
    {
        $this->ptr = $hNode;
        $this->ptr->parent = $this;
        $this->parent = $parent;
    }

    function append_lexeme($lexeme)
    {
        if ($this->parent instanceof TreeNodeArray) {
            return $this->parent->append_lexeme($lexeme);
        }

        $parent = $this->parent;
        $suffix = new TreeNodeSuffix($lexeme, $this, $parent);
        if ($parent != null) {
            $parent->replace($this, $suffix);
        }
        return $suffix;
    }

    function append_left_brace()
    {
        if ($this->parent != null && $this->parent instanceof TreeNodeArray) {
            return $this->parent->append_left_brace();
        }

        $caret = new TreeNodeCaret();
        $array = [];
        $array[] = $this;
        $array[] = new TreeNodeBrace($caret);

        $parent = $this->parent;
        $mul = new TreeNodeArray($array, $parent);
        if ($parent != null) {
            $parent->replace($this, $mul);
        }
        return $caret;
    }

    public function __toString()
    {
        return '{' . $this->ptr->__toString() . '}';
    }

    public function rawtext()
    {
        return $this->ptr->rawtext();
    }

    function replace($old, $replacement)
    {
        if ($this->ptr !== $old)
            throw new RuntimeException("ptr != old");
        $this->ptr = $replacement;
    }
}

class TreeNodeLexeme extends TreeNode
{

    protected $lexeme;

    public function __construct($lexeme, $parent = null)
    {
        $this->lexeme = $lexeme;
        $this->parent = $parent;
    }

    function append_left_brace()
    {
        $caret = new TreeNodeCaret();
        $replacement = new TreeNodePrefix($this->lexeme, new TreeNodeBrace($caret), $this->parent);
        if ($this->parent != null) {
            $this->parent->replace($this, $replacement);
        }
        return $caret;
    }

    public function __toString()
    {
        return $this->lexeme;
    }

    public function rawtext()
    {
        return $this->lexeme;
    }

    function append_lexeme($lexeme)
    {
        return null;
    }
}

function search_for_nonbraces($infix, $i)
{
    $strlen = strlen($infix);
    for (; $i < $strlen; ++ $i) {
        switch ($infix[$i]) {
            case '{':
            case '}':
                return $i;
        }
    }
    return $i;
}

class TreeNodeSuffix extends TreeNodeLexeme
{

    public function __construct($lexeme, $ptr, $parent = null)
    {
        parent::__construct($lexeme, $parent);
        $this->ptr = $ptr;
        $this->ptr->parent = $this;
    }

    function append_left_brace()
    {
        $caret = new TreeNodeCaret();

        $replacement = new TreeNodeBinary($this->lexeme, $this->ptr, new TreeNodeBrace($caret), $this->parent);
        if ($this->parent != null) {
            $this->parent->replace($this, $replacement);
        }
        return $caret;
    }

    function append_lexeme($lexeme)
    {
        return null;
    }

    protected $ptr;

    public function __toString()
    {
        return $this->ptr->__toString() . parent::__toString();
    }

    public function rawtext()
    {
        return $this->ptr->rawtext() . $this->parent::rawtext();
    }

    function replace($old, $replacement)
    {
        if ($ptr !== $old)
            throw new RuntimeException("ptr != old");
        $this->ptr = $replacement;
    }
}

class TreeNodePrefix extends TreeNodeLexeme
{

    public function __construct($lexeme, $caret, $parent = null)
    {
        parent::__construct($lexeme, $parent);
        $this->ptr = $caret;
        $this->ptr->parent = $this;
    }

    function append_left_brace()
    {
        throw new RuntimeException("TreeNode append_left_parenthesis()");
    }

    function append_lexeme($lexeme)
    {
        return null;
    }

    protected $ptr;

    public function __toString()
    {
        return parent::__toString() . $this->ptr->__toString();
    }

    public function rawtext()
    {
        return parent::rawtext() . $this->ptr->rawtext();
    }

    function replace($old, $replacement)
    {
        if ($this->ptr !== $old)
            throw new RuntimeException("ptr != old");
        $this->ptr = $replacement;
    }
}

class TreeNodeBinary extends TreeNodeLexeme
{

    public function __construct($lexeme, $lhs, $rhs, $parent)
    {
        parent::__construct($lexeme, $parent);
        $this->lhs = $lhs;
        $this->rhs = $rhs;
        $lhs->parent = $rhs->parent = $this;
    }

    function append_left_brace()
    {
        throw new RuntimeException("TreeNode append_left_parenthesis()");
    }

    function append_lexeme($lexeme)
    {
        return null;
    }

    public $lhs;

    public $rhs;

    public function __toString()
    {
        return $this->lhs->__toString() . parent::__toString() . $this->rhs->__toString();
    }

    public function rawtext()
    {
        return $this->lhs->rawtext() . parent::rawtext() . $this->rhs->rawtext();
    }

    function replace($old, $replacement)
    {
        if ($this->lhs === $old) {
            $this->lhs = $replacement;
        } else if ($this->rhs === $old) {
            $this->rhs = $replacement;
        } else
            throw new RuntimeException("void replace(TreeNode old, TreeNode replacement) throws Exception");
    }
}

class TreeNodeArray extends TreeNode
{

    public function __construct($array, $parent)
    {
        $this->parent = $parent;
        $this->array = $array;
        foreach ($array as $ptr) {
            $ptr->parent = $this;
        }
    }

    function append_left_brace()
    {
        $caret = new TreeNodeCaret();
        $this->array[] = new TreeNodeBrace($caret, $this);
        return $caret;
    }

    function append_lexeme($lexeme)
    {
        $parent = $this->parent;
        $suffix = new TreeNodeSuffix($lexeme, $this, $parent);
        if ($parent != null) {
            $parent->replace($this, $suffix);
        }

        return $suffix;
    }

    public $array;

    public function __toString()
    {
        return implode("", array_map(fn ($node) => $node->__toString(), $this->array));
    }

    public function rawtext()
    {
        return implode("", array_map(fn ($node) => $node->rawtext(), $this->array));
    }

    function replace($old, $replacement)
    {
        $i = array_search($this->array, $old, true);
        if ($i === false)
            throw new RuntimeException("void replace(TreeNode old, TreeNode replacement) throws Exception");
        $this->array[$i] = $replacement;
    }
}

function compile($infix)
{
    $caret = new TreeNodeCaret();

    $strlen = strlen($infix);
    for ($i = 0; $i < $strlen; ++ $i) {
        switch ($infix[$i]) {
            // case ' ':
            // case ' ':
            // case '\t':
            // break;
            case '{':
                $caret = $caret->append_left_brace();
                break;
            case '}':
                $old = $caret;
                for (;;) {
                    if ($caret == null) {
                        \std\println(\std\slice($infix, 0, $i));
                        \std\println(\std\slice($infix, $i));
                        error_log("unnecessary right brace at position " . $i);
                        break;
                    }
                    $old = $caret;
                    $caret = $caret->parent;
                    if ($caret instanceof TreeNodeBrace) {
                        break;
                    }
                }

                if ($caret == null) {
                    $caret = $old;
                }

                break;
            default:

                $end = search_for_nonbraces($infix, $i);

                if ($end == $i) {
                    throw new RuntimeException("lexeme not found!");
                }

                // \std\println(\std\slice($infix, $i, $end));

                $caret = $caret->append_lexeme(\std\slice($infix, $i, $end));

                $i = $end - 1;
        }
    }

    for (;;) {
        if ($caret->parent != null)
            $caret = $caret->parent;
        else
            break;
    }

    return $caret;
}

require_once 'mysql.php';

function test()
{
    $line = 0;
    foreach (\mysql\select("select infix from corpus.tbl_syntax_cn limit 100000 offset $line") as list ($infix,)) {

        // \std\println($infix);

        // \std\println(++$line);
        $node = compile($infix);

        $nodeString = (string) $node;

        if (! \std\equals($nodeString, $infix)) {
            \std\println($infix);
        }
    }
}


?>
