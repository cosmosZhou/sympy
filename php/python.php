<?php
namespace python;

// use the following regex to remove error_log prints:
// ^ *error_log
use RuntimeException;

// set_exception_handler(function ($err) {
// // echo "<b>Exception:</b> ", $err->getMessage();
// throw new RuntimeException($err->getMessage());
// });
require_once 'utility.php';

abstract class PyObject
{

    function append_left_parenthesis()
    {
        $self = $this;
        $parent = $self->parent;

        $caret = new Caret();
        if ($parent instanceof Dot) {
            $self = $parent;
            $parent = $self->parent;
        }

        if ($parent instanceof Dot) {
            throw new RuntimeException("$parent instanceof Dot?");
        }

        $func = new FunctionCall($self, [
            $caret
        ], $parent);

        $parent->replace($self, $func);

        return $caret;
    }

    function append_colon($self)
    {
        $child = (function ($self) {
            do {
                $parent = $self->parent;
                if ($parent instanceof Indexed || $parent instanceof Set) {
                    return null;
                }

                if ($parent instanceof Lambda || $parent instanceof Colon) {
                    break;
                }
                $self = $parent;
            } while ($parent !== null);

            return $self;
        })($self);

        if ($child !== null) {
            return $child->parent->append_colon($child);
        }
        $caret = new Caret();

        $colon = new Colon([
            $self,
            $caret
        ], $this);
        $this->replace($self, $colon);

        return $caret;
    }

    function append_left_bracket()
    {
        $parent = $this->parent;

        $caret = new Caret();
        $func = new Indexed($this, [
            $caret
        ], $parent);

        $parent->replace($this, $func);

        return $caret;
    }

    function append_comma($obj)
    {
        return $this->parent->append_comma($this);
    }

    function append_semicolon($obj)
    {
        return $this->parent->append_semicolon($this);
    }

    function append_right_bracket()
    {
        if ($this->parent === null) {
            throw new RuntimeException("$this's parent is null!");
        }
        return $this->parent->append_right_bracket();
    }

    function append_right_brace()
    {
        if ($this->parent === null) {
            throw new RuntimeException("$this's parent is null!");
        }
        return $this->parent->append_right_brace();
    }

    function append_right_parenthesis()
    {
        if ($this->parent === null) {
            throw new RuntimeException("$this's parent is null!");
        }
        return $this->parent->append_right_parenthesis();
    }

    function append_binary_operator($InputType, $child)
    {
        if ($InputType::input_precedence() > $this->stack_precedence()) {
            $caret = new Caret();
            $new = new $InputType($child, $caret, $this);

            $this->replace($child, $new);
            return $caret;
        }

        if ($this->parent === null) {
            throw new RuntimeException("$this 's parent === null in append_binary_operator($InputType, $child)");
        }

        return $this->parent->append_binary_operator($InputType, $this);
    }

    function printf()
    {
        $caret = $this;
        while ($caret != null) {
            print($caret);
            $caret = $caret->parent;
        }
        print('\n');
    }

    function append_identifier($name)
    {
        switch ($name) {
            case "for":
                $self = $this;

                do {
                    $parent = $self->parent;
                    if ($parent instanceof Parenthesis || $parent instanceof FunctionCall || $parent instanceof ArrayList || $parent instanceof Set) {

                        $domain = new Caret();
                        $var = new Caret();
                        $generator = new Generator($self, $var, $domain, $parent);
                        $parent->replace($self, $generator);
                        return $var;
                    } else {
                        if ($parent === null) {
                            break;
                        }
                        $self = $parent;
                    }
                } while (true);

                break;
            case "in":
                $parent = $this->parent;
                while ($parent instanceof Comma || $parent instanceof Star) {
                    $parent = $parent->parent;
                }

                if ($parent instanceof Generator) {
                    if ($parent->domain instanceof Caret)
                        return $parent->domain;
                }

                $self = $this;

                for (;;) {
                    $parent = $self->parent;
                    if ($parent instanceof Dot) {
                        $self = $parent;
                        continue;
                    }

                    break;
                }
                $caret = new Caret();
                $contains = new Contains($self, $caret, $parent);
                $parent->replace($self, $contains);
                return $caret;
            case "and":
                $self = $this;

                for (;;) {
                    if ($self instanceof FunctionCall) {
                        break;
                    }

                    $parent = $self->parent;

                    if ($parent instanceof LessEqual || //
                    $parent instanceof Less || //
                    $parent instanceof Greater || //
                    $parent instanceof GreaterEqual || //
                    $parent instanceof Equal || //
                    $parent instanceof Unequal || //
                    $parent instanceof Contains || //
                    $parent instanceof NotContains || //
                    $parent instanceof LogicNot || //
                    $parent instanceof LogicAnd) {
                        $self = $parent;
                        break;
                    }

                    if ($parent instanceof LogicOr || //
                    $parent instanceof Sentence || //
                    $parent instanceof Parenthesis || //
                    $parent instanceof IfElse || //
                    $parent instanceof Set || //
                    $parent instanceof Tuple || //
                    $parent instanceof Indexed || //
                    $parent instanceof FunctionCall) {
                        break;
                    }

                    if ($parent instanceof GeneratorIf && $parent->cond === $self) {
                        break;
                    }

                    $self = $parent;
                }

                $caret = new Caret();
                $parent = $self->parent;
                $and = new LogicAnd($self, $caret, $parent);
                $parent->replace($self, $and);
                return $caret;
            case "or":
                $self = $this;

                for (;;) {
                    if ($self instanceof FunctionCall) {
                        break;
                    }

                    $parent = $self->parent;

                    if ($parent instanceof LessEqual || //
                    $parent instanceof Less || //
                    $parent instanceof Greater || //
                    $parent instanceof GreaterEqual || //
                    $parent instanceof Equal || //
                    $parent instanceof Unequal || //
                    $parent instanceof Contains || //
                    $parent instanceof NotContains || //
                    $parent instanceof LogicNot || //
                    $parent instanceof LogicAnd || //
                    $parent instanceof LogicOr) {
                        $self = $parent;
                        break;
                    }

                    if ($parent instanceof Sentence || //
                    $parent instanceof Parenthesis || //
                    $parent instanceof IfElse || //
                    $parent instanceof Set || //
                    $parent instanceof Tuple || //
                    $parent instanceof Indexed || //
                    $parent instanceof FunctionCall) {
                        break;
                    }

                    if ($parent instanceof GeneratorIf && $parent->cond === $self) {
                        break;
                    }

                    $self = $parent;
                }

                $caret = new Caret();
                $parent = $self->parent;
                $and = new LogicOr($self, $caret, $parent);
                $parent->replace($self, $and);
                return $caret;
            case "if":
                $self = $this;

                for (;;) {
                    $parent = $self->parent;
                    if ($parent instanceof Generator) {
                        $self = $parent;
                        $parent = $self->parent;
                        $caret = new Caret();

                        $class = get_class($self) . "If";
                        $new = new $class($self->expr, $self->var, $self->domain, $caret, $parent);
                        break;
                    }
                    // in the form {expr if cond else other}
                    if ($parent instanceof Set || //
                    $parent instanceof Parenthesis || //
                    $parent instanceof ArrayList || //
                    $parent instanceof Tuple || //
                    $parent instanceof FunctionCall || //
                    $parent instanceof Indexed || //
                    $parent instanceof Sentence) {
                        $caret = new Caret();
                        $other = new Caret();
                        $new = new IfElse($self, $caret, $other, $parent);
                        break;
                    }

                    if ($parent === null) {
                        throw new RuntimeException("illegal $this in if statement ");
                    }

                    $self = $parent;
                }

                $parent->replace($self, $new);
                return $caret;
            case "else":
                $self = $this;

                for (;;) {
                    $parent = $self->parent;
                    if ($parent instanceof IfElse) {
                        if ($self === $parent->cond) {
                            return $parent->other;
                        }
                        throw new RuntimeException("illegal $this in else statement ");
                    }

                    if ($parent === null) {
                        throw new RuntimeException("illegal $this in else statement ");
                    }

                    $self = $parent;
                }

                $parent->replace($self, $new);
                return $caret;
            case "is":
                $self = $this;

                for (;;) {
                    $parent = $self->parent;
                    if ($parent instanceof Dot) {
                        $self = $parent;
                        continue;
                    }

                    break;
                }
                $caret = new Caret();
                $is = new Is($self, $caret, $parent);
                $parent->replace($self, $is);
                return $caret;

            case "not":
                $self = $this;

                for (;;) {
                    $parent = $self->parent;
                    if ($parent instanceof Dot) {
                        $self = $parent;
                        continue;
                    }

                    break;
                }
                $caret = new Caret();
                $contains = new NotContains($self, $caret, $parent);
                $parent->replace($self, $contains);
                return $caret;

            case "async":
                $self = $this;

                do {
                    $parent = $self->parent;
                    if ($parent instanceof Parenthesis || $parent instanceof FunctionCall || $parent instanceof ArrayList || $parent instanceof Set) {

                        $domain = new Caret();
                        $var = new Caret();
                        $generator = new GeneratorAsync($self, $var, $domain, $parent);
                        $parent->replace($self, $generator);
                        return $var;
                    } else {
                        if ($parent === null) {
                            break;
                        }
                        $self = $parent;
                    }
                } while (true);

                break;

            default:
                if (Literal::is_literal_prefix($name)) {
                    $literal = new Literal($name);
                    $parent = $this->parent;
                    if ($parent instanceof Literals) {
                        $parent->args[] = $literal;
                        $literal->parent = $parent;
                    } else {

                        $new = new Literals([
                            $this,
                            $literal
                        ], $parent);

                        $parent->replace($this, $new);
                    }
                    return $literal;
                }

                break;
        }

        throw new RuntimeException("unrecognized keyword $name with " . get_class($this->parent) . " in " . __line__);
    }

    abstract function __toString();

    public $parent = null;
}

class Caret extends PyObject
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __construct($parent = null)
    {
        $this->parent = $parent;
    }

    function append_ellipsis()
    {
        $parent = $this->parent;
        $new = new Ellipsis($parent);
        $parent->replace($this, $new);
        return $new;
    }

    function append_literal(&$infix, &$i, $mark)
    {
        $end = search_for_mark($infix, $i, $mark);

        if ($end == $i) {
            throw new RuntimeException("digits not found!");
        }

        $string = \std\slice($infix, $i, $end);

        $parent = $this->parent;
        $caret = new Literal($string, $parent);
        $parent->replace($this, $caret);

        $i = $end - 1;
        return $caret;
    }

    function append_digit(&$infix, &$i)
    {
        $end = search_for_digits($infix, $i);

        if ($end == $i) {
            throw new RuntimeException("digits not found!");
        }

        $digits = \std\slice($infix, $i, $end);

        $parent = $this->parent;
        $caret = new Number($digits, $parent);
        $parent->replace($this, $caret);

        $i = $end - 1;
        return $caret;
    }

    function append_left_brace()
    {
        $caret = new Caret();

        $parent = $this->parent;
        $set = new Set([
            $caret
        ], $parent);
        $parent->replace($this, $set);

        return $caret;
    }

    function append_unary_operator($class)
    {
        $parent = $this->parent;

        $new = new $class($this, $parent);

        $parent->replace($this, $new);

        return $this;
    }

    function append_left_parenthesis()
    {
        $caret = new Caret();

        $parent = $this->parent;
        $parenthesis = new Parenthesis($caret, $parent);
        $parent->replace($this, $parenthesis);

        return $caret;
    }

    function append_identifier($name)
    {
        $parent = $this->parent;

        switch ($name) {
            case "lambda":
                $caret = new Caret();
                $expr = new Caret();

                $lambda = new Lambda($caret, $expr, $parent);
                $parent->replace($this, $lambda);
                break;
            case "not":
                $not = new LogicNot($this, $parent);
                $parent->replace($this, $not);
                $caret = $this;
                break;
            case "if":
                throw new RuntimeException('illegal if statement here');
                // $not = new LogicNot($this, $parent);
                // $parent->replace($this, $not);
                // $caret = $this;
                break;
            case "in":
                if ($parent instanceof NotContains) {
                    if ($parent->in_is_received) {
                        throw new RuntimeException('illegal in statement here in $parent');
                    }
                    $parent->in_is_received = true;
                } else {
                    throw new RuntimeException('illegal in statement here in $parent');
                }

                $caret = $this;
                break;

            case "await":
                $caret = $this;
                $new = new Await($caret, $parent);
                $parent->replace($this, $new);
                break;

            case "yield":
                $caret = $this;
                $new = new GeneratorYield($caret, $parent);
                $parent->replace($this, $new);
                break;

            case "from":
                $parent = $this->parent;
                if ($parent instanceof GeneratorYield) {
                    $forefather = $parent->parent;
                    $new = new GeneratorYieldFrom($this, $forefather);
                    $forefather->replace($parent, $new);
                } else {
                    throw new RuntimeException("illegal from statement of $this in $parent");
                }

                $caret = $this;
                break;

            case "for":
                $parent = $this->parent;
                if ($parent instanceof GeneratorAsync) {
                    if ($this !== $parent->var) {
                        throw new RuntimeException("illegal from statement of $this in $parent");
                    }
                } else {
                    throw new RuntimeException("illegal from statement of $this in $parent");
                }

                $caret = $this;
                break;

            default:
                $caret = new Identifier($name, $parent);
                $parent->replace($this, $caret);
        }

        return $caret;
    }

    public function __toString()
    {
        return "";
    }

    function append_left_bracket()
    {
        $parent = $this->parent;

        $func = new ArrayList([
            $this
        ], $parent);

        $parent->replace($this, $func);

        return $this;
    }
}

class Identifier extends PyObject
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    protected $name;

    public function __construct(string $name, $parent)
    {
        $this->name = $name;
        $this->parent = $parent;
    }

    function append_left_brace()
    {
        $caret = new Caret();
        $parent = $this->parent;
        $new = new TreeNodePrefix($this->name, new Set($caret), $parent);
        $parent->replace($this, $new);
        return $caret;
    }

    public function __toString()
    {
        return $this->name;
    }

    function append_literal(&$infix, &$i, $mark)
    {
        if (! Literal::is_literal_prefix($this->name)) {
            throw new RuntimeException("illegal prefix $this->name before literal");
        }

        $end = search_for_mark($infix, $i, $mark);

        if ($end == $i) {
            throw new RuntimeException("literal not found!");
        }

        $prefix_length = strlen($this->name);
        $i -= $prefix_length;

        if (! \std\equals(substr($infix, $i, $prefix_length), $this->name)) {

            throw new RuntimeException("illegal prefix $this->name before literal: $infix");
        }

        $string = \std\slice($infix, $i, $end);

        $parent = $this->parent;
        $caret = new Literal($string, $parent);
        $parent->replace($this, $caret);

        $i = $end - 1;
        return $caret;
    }
}

class Number extends PyObject
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    protected $digits;

    public function __construct(string $digits, $parent)
    {
        $this->digits = $digits;
        $this->parent = $parent;
    }

    public function __toString()
    {
        return $this->digits;
    }
}

class Ellipsis extends PyObject
{

    public function __construct($parent)
    {
        $this->parent = $parent;
    }

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return '...';
    }
}

class Literal extends PyObject
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 11;
    }

    protected $literal;

    public function __construct(string $literal, $parent = null)
    {
        $this->literal = $literal;
        $this->parent = $parent;
    }

    public function __toString()
    {
        return $this->literal;
    }

    static function is_literal_prefix($literal)
    {
        switch ($literal) {
            case 'r':
            case 'f':
            case 'u':
            case 'b':
            case 'R':
            case 'F':
            case 'U':
            case 'B':

            case 'rf':
            case 'rb':
            case 'rF':
            case 'rB':

            case 'Rf':
            case 'Rb':
            case 'RF':
            case 'RB':

            case 'fr':
            case 'br':
            case 'Fr':
            case 'Br':

            case 'fR':
            case 'bR':
            case 'FR':
            case 'BR':
                return true;
            default:
                return false;
        }
    }

    function append_literal(&$infix, &$i, $mark)
    {
        $end = search_for_mark($infix, $i, $mark);

        if ($end == $i) {
            throw new RuntimeException("literal not found!");
        }

        $string = \std\slice($infix, $i, $end);

        $parent = $this->parent;
        if ($parent instanceof Literals) {

            if (Literal::is_literal_prefix($this->literal)) {

                $this->literal .= $string;
                $caret = $this;
            } else {
                $caret = new Literal($string, $parent);
                $parent->args[] = $caret;
            }
        } else {
            $caret = new Literal($string);
            $new = new Literals([
                $this,
                $caret
            ], $parent);

            $parent->replace($this, $new);
        }

        $i = $end - 1;
        return $caret;
    }
}

class Literals extends MultiVariableOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return implode(" ", array_map(fn ($node) => $node->__toString(), $this->args));
    }

    function append_comma($child)
    {
        return $this->parent->append_comma($this);
    }
}

function search_for_identifier(&$infix, $i)
{
    static $_ = 95; // ord('_');
    static $a = 97; // ord('a');
    static $z = 122; // ord('z');

    static $A = 65; // ord('A');
    static $Z = 90; // ord('Z');

    static $_0 = 48; // ord('0');
    static $_9 = 57; // ord('9');

    $strlen = strlen($infix);
    for (; $i < $strlen; ++ $i) {
        $ch = ord($infix[$i]);
        if ($ch >= $a && $ch <= $z || $ch >= $A && $ch <= $Z || $ch >= $_0 && $ch <= $_9 || $ch == $_) {
            continue;
        } else if ($ch >= 128) {
            $i += \std\get_utf8_char_len($ch) - 1;
        } else
            return $i;
    }
    return $i;
}

function search_for_digits(&$infix, $i)
{
    static $_0 = 48; // ord('0');
    static $_9 = 57; // ord('9');

    $strlen = strlen($infix);
    if ($infix[$i] == '0') {
        if ($i + 1 < $strlen) {
            switch ($infix[$i + 1]) {
                case 'x':
                case 'X':

                    static $A = 65; // ord('A');
                    static $F = 70; // ord('F');

                    static $a = 97; // ord('a');
                    static $f = 102; // ord('f');

                    $i += 2;
                    for (; $i < $strlen; ++ $i) {
                        $ch = ord($infix[$i]);
                        if ($ch >= $_0 && $ch <= $_9 || $ch >= $a && $ch <= $f || $ch >= $A && $ch <= $F) {
                            continue;
                        } else
                            break;
                    }

                    return $i;
                case 'o':
                case 'O':
                    $i += 2;
                    static $_7 = 55; // ord('7');
                    for (; $i < $strlen; ++ $i) {
                        $ch = ord($infix[$i]);
                        if ($ch >= $_0 && $ch <= $_7) {
                            continue;
                        } else
                            break;
                    }

                    return $i;
            }
        }
    }

    for (; $i < $strlen; ++ $i) {
        $ch = ord($infix[$i]);
        if ($ch >= $_0 && $ch <= $_9) {
            continue;
        }

        switch ($infix[$i]) {
            case 'j':
            case 'J':
                ++ $i;
            default:
                return $i;
            case '.':
                break;
            case 'e':
            case 'E':

                ++ $i;
                switch ($infix[$i]) {
                    case '+':
                    case '-':
                        ++ $i;
                        break;
                    default:
                        break;
                }

                for (; $i < $strlen; ++ $i) {
                    $ch = ord($infix[$i]);
                    if ($ch >= $_0 && $ch <= $_9) {
                        continue;
                    }

                    switch ($infix[$i]) {
                        case 'j':
                        case 'J':
                            ++ $i;
                        default:
                            return $i;
                    }
                }

                break;
        }
    }
    return $i;
}

function search_for_mark(&$infix, $i, $mark)
{
    $strlen = strlen($infix);
    for (++ $i; $i < $strlen; ++ $i) {
        if ($infix[$i] == $mark) {
            if ($infix[$i - 1] == '\\') {
                if ($i >= 2 && $infix[$i - 2] == '\\') {
                    return $i + 1;
                }
            } else
                return $i + 1;
        }
    }
    return $i;
}

abstract class BinaryOperator extends PyObject
{

    public function __construct($lhs, $rhs, $parent)
    {
        $this->lhs = $lhs;
        $this->rhs = $rhs;
        $lhs->parent = $rhs->parent = $this;
        $this->parent = $parent;
    }

    public $lhs;

    public $rhs;

    function replace($old, $new)
    {
        if ($this->lhs === $old) {
            $this->lhs = $new;
        } else if ($this->rhs === $old) {
            $this->rhs = $new;
        } else
            throw new RuntimeException("void replace(TreeNode old, TreeNode replacement) throws Exception");
    }
}

class Dot extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 20;
    }

    public function __toString()
    {
        return "$this->lhs.$this->rhs";
    }
}

class Greater extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs > $this->rhs";
    }
}

class Less extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs < $this->rhs";
    }
}

class Contains extends BinaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs in $this->rhs";
    }
}

class NotContains extends BinaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public $in_is_received = false;

    public function __toString()
    {
        return "$this->lhs not in $this->rhs";
    }
}

class GreaterEqual extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs >= $this->rhs";
    }
}

class LessEqual extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs <= $this->rhs";
    }
}

class Unequal extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs != $this->rhs";
    }
}

class Equal extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs == $this->rhs";
    }
}

class Is extends BinaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs is $this->rhs";
    }
}

class Mul extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs * $this->rhs";
    }
}

class MatMul extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs @ $this->rhs";
    }
}

class MatMulAssignment extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs @= $this->rhs";
    }
}

class Add extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs + $this->rhs";
    }
}

class Sub extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs - $this->rhs";
    }
}

class Div extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs / $this->rhs";
    }
}

class FloorDiv extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs // $this->rhs";
    }
}

class FloorDivAssignment extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs //= $this->rhs";
    }
}

class Mod extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs % $this->rhs";
    }
}

class Pow extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs ** $this->rhs";
    }
}

class PowAssignment extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs **= $this->rhs";
    }
}

class ExclusiveOr extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs ^ $this->rhs";
    }
}

class BitwiseOr extends BinaryOperator
{

    public static function input_precedence()
    {
        return 12;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs | $this->rhs";
    }
}

class BitwiseAnd extends BinaryOperator
{

    public static function input_precedence()
    {
        return 12;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs & $this->rhs";
    }
}

class EqualAssignment extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs=$this->rhs";
    }
}

class LogicOr extends BinaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs or $this->rhs";
    }
}

class LogicAnd extends BinaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs and $this->rhs";
    }
}

class AddAssignment extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs += $this->rhs";
    }
}

class SubAssignment extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs -= $this->rhs";
    }
}

class MulAssignment extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs *= $this->rhs";
    }
}

class DivAssignment extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs /= $this->rhs";
    }
}

class ModAssignment extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs %= $this->rhs";
    }
}

class ExclusiveOrAssignment extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs ^= $this->rhs";
    }
}

class BitwiseOrAssignment extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs |= $this->rhs";
    }
}

class BitwiseAndAssignment extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs &= $this->rhs";
    }
}

class LeftShift extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs << $this->rhs";
    }
}

class RightShift extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs >> $this->rhs";
    }
}

class LeftShiftAssignment extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs <<= $this->rhs";
    }
}

class RightShiftAssignment extends BinaryOperator
{

    public static function input_precedence()
    {
        return 10;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "$this->lhs >>= $this->rhs";
    }
}

abstract class UnaryOperator extends PyObject
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __construct($arg, $parent)
    {
        $this->arg = $arg;
        $arg->parent = $this;
        $this->parent = $parent;
    }

    protected $arg;

    function replace($old, $new)
    {
        if ($this->arg === $old) {
            $this->arg = $new;
        } else
            throw new RuntimeException("void replace(TreeNode old, TreeNode replacement) throws Exception");
    }
}

class Star extends UnaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "*$this->arg";
    }
}

class DoubleStar extends UnaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "**$this->arg";
    }
}

class Neg extends UnaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "-$this->arg";
    }
}

class Plus extends UnaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "+$this->arg";
    }
}

class Invert extends UnaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "~$this->arg";
    }
}

class LogicNot extends UnaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "not $this->arg";
    }
}

class Await extends UnaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "await $this->arg";
    }
}

class Parenthesis extends UnaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    function append_right_parenthesis()
    {
        return $this;
    }

    public function __toString()
    {
        return "($this->arg)";
    }

    function append_comma($child)
    {
        $parent = $this->parent;
        $caret = new Caret();
        $tuple = new Tuple([
            $this->arg,
            $caret
        ], $parent);

        $parent->replace($this, $tuple);
        return $caret;
    }
}

abstract class MultiVariableOperator extends PyObject
{

    public function __construct(array $args, $parent)
    {
        $this->args = $args;
        foreach ($args as $arg) {
            $arg->parent = $this;
        }

        $this->parent = $parent;
    }

    public $args;

    function replace($old, $new)
    {
        $i = array_search($old, $this->args, true);
        if ($i === false)
            throw new RuntimeException("void replace(TreeNode old, TreeNode replacement) throws Exception");
        $this->args[$i] = $new;
    }

    function append_comma($child)
    {
        $caret = new Caret($this);
        $this->args[] = $caret;
        return $caret;
    }
}

class Set extends MultiVariableOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "{" . implode(", ", array_map(fn ($node) => $node->__toString(), $this->args)) . "}";
    }

    function append_right_brace()
    {
        return $this;
    }
}

// as in the form (x, y, z) or (x, y, z, ) or (x, )
class Tuple extends MultiVariableOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "(" . implode(", ", array_map(fn ($node) => $node->__toString(), $this->args)) . ")";
    }

    function append_right_parenthesis()
    {
        return $this;
    }
}

// as in the form x, y, z or x, y, z,
class Comma extends MultiVariableOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return implode(", ", array_map(fn ($node) => $node->__toString(), $this->args));
    }
}

// as in the form [x, y, z] or [x, y, z, ] or [x,]
class ArrayList extends MultiVariableOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "[" . implode(", ", array_map(fn ($node) => $node->__toString(), $this->args)) . "]";
    }

    function append_right_bracket()
    {
        return $this;
    }
}

class FunctionCall extends MultiVariableOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    protected $name;

    public function __construct(PyObject $name, $args, $parent)
    {
        parent::__construct($args, $parent);
        $this->name = $name;
        $name->parent = $this;
    }

    function append_right_parenthesis()
    {
        return $this;
    }

    public function __toString()
    {
        return "$this->name(" . implode(", ", array_map(fn ($obj) => $obj->__toString(), $this->args)) . ')';
    }

    function replace($old, $new)
    {
        if ($old === $this->name) {
            $this->name = $new;
        } else {
            parent::replace($old, $new);
        }
    }
}

class Indexed extends MultiVariableOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    protected $base;

    public function __construct(PyObject $base, $args, $parent)
    {
        parent::__construct($args, $parent);
        $this->base = $base;
        $base->parent = $this;
    }

    function append_right_bracket()
    {
        return $this;
    }

    public function __toString()
    {
        return "$this->base[" . implode(", ", array_map(fn ($obj) => $obj->__toString(), $this->args)) . ']';
    }

    function replace($old, $new)
    {
        if ($old === $this->base) {
            $this->base = $new;
        } else {
            parent::replace($old, $new);
        }
    }
}

// as in the form: i for i in (1, 2, 3)
class Generator extends PyObject
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    // must be an identifier, or a list of identifiers
    public $var;

    protected $domain;

    protected $expr;

    public function __construct($expr, $var, $domain, $parent)
    {
        $this->expr = $expr;
        $this->var = $var;
        $this->domain = $domain;

        $var->parent = $this;
        $expr->parent = $this;
        $domain->parent = $this;

        $this->parent = $parent;
    }

    function replace($old, $new)
    {
        if ($old === $this->expr) {
            $this->expr = $new;
        } else if ($old === $this->var) {
            $this->var = $new;
        } else if ($old === $this->domain) {
            $this->domain = $new;
        } else
            throw new RuntimeException("void replace(TreeNode old, TreeNode replacement) throws Exception");
    }

    public function __toString()
    {
        return "$this->expr for $this->var in $this->domain";
    }

    function append_comma($child)
    {
        if ($child === $this->var) {

            $caret = new Caret();
            $comma = new Comma([
                $this->var,
                $caret
            ], $this);
            $this->replace($this->var, $comma);
            return $caret;
        } else {
            throw new RuntimeException("illegal $child in $this for append_comma");
        }
    }
}

// as in the form: i for i in (1, 2, 3)
class GeneratorAsync extends Generator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __construct($expr, $var, $domain, $parent)
    {
        parent::__construct($expr, $var, $domain, $parent);
    }

    public function __toString()
    {
        return "$this->expr async for $this->var in $this->domain";
    }
}

// as in the form: i for i in (1, 2, 3)
class GeneratorIf extends Generator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    protected $cond;

    public function __construct($expr, $var, $domain, $cond, $parent)
    {
        parent::__construct($expr, $var, $domain, $parent);
        $this->cond = $cond;

        $cond->parent = $this;
    }

    function replace($old, $new)
    {
        if ($old === $this->cond) {
            $this->cond = $new;
        } else {
            parent::replace($old, $new);
        }
    }

    public function __toString()
    {
        return parent::__toString() . " if $this->cond";
    }
}

// as in the form: i for i in (1, 2, 3)
class GeneratorAsyncIf extends GeneratorAsync
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    protected $cond;

    public function __construct($expr, $var, $domain, $cond, $parent)
    {
        parent::__construct($expr, $var, $domain, $parent);
        $this->cond = $cond;

        $cond->parent = $this;
    }

    function replace($old, $new)
    {
        if ($old === $this->cond) {
            $this->cond = $new;
        } else {
            parent::replace($old, $new);
        }
    }

    public function __toString()
    {
        return parent::__toString() . " if $this->cond";
    }
}

// as in the form: return (yield x)
class GeneratorYield extends UnaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "yield $this->arg";
    }
}

// as in the form: return (yield x)
class GeneratorYieldFrom extends UnaryOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __toString()
    {
        return "yield from $this->arg";
    }
}

// as in the form: expr if cond else other
class IfElse extends PyObject
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    // must be an identifier, or a list of identifiers
    protected $expr;

    protected $cond;

    public $other;

    public function __construct($expr, $cond, $other, $parent)
    {
        $this->expr = $expr;
        $this->cond = $cond;
        $this->other = $other;

        $cond->parent = $this;
        $expr->parent = $this;
        $other->parent = $this;

        $this->parent = $parent;
    }

    function replace($old, $new)
    {
        if ($old === $this->expr) {
            $this->expr = $new;
        } else if ($old === $this->cond) {
            $this->cond = $new;
        } else if ($old === $this->other) {
            $this->other = $new;
        } else
            throw new RuntimeException("void replace(TreeNode old, TreeNode replacement) throws Exception");
    }

    public function __toString()
    {
        return "$this->expr if $this->cond else $this->other";
    }
}

// as in the form: lambda x, y : x + y
class Lambda extends PyObject
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    // must be an identifier, or a list of identifiers
    protected $var;

    protected $expr;

    public function __construct($var, $expr, $parent)
    {
        $this->expr = $expr;
        $this->var = $var;

        $var->parent = $this;
        $expr->parent = $this;

        $this->parent = $parent;
    }

    function replace($old, $new)
    {
        if ($old === $this->expr) {
            $this->expr = $new;
        } else if ($old === $this->var) {
            $this->var = $new;
        } else
            throw new RuntimeException("void replace(TreeNode old, TreeNode replacement) throws Exception");
    }

    public function __toString()
    {
        return "lambda $this->var : $this->expr";
    }

    function append_comma($child)
    {
        if ($child === $this->var) {
            $caret = new Caret();
            $comma = new Comma([
                $this->var,
                $caret
            ], $this);
            $this->replace($this->var, $comma);
            return $caret;
        } else if ($child === $this->expr) {
            return parent::append_comma($child);
        } else {
            throw new RuntimeException('illegal $child for lambda expression $this');
        }
    }

    function append_colon($self)
    {
        if ($self === $this->var) {
            return $this->expr;
        } else {
            throw new RuntimeException("$this could not accept more slice args!");
        }
    }
}

// as in the form start:stop:step, or as in the form {k:v, k1:v2}
class Colon extends MultiVariableOperator
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    function append_colon($self)
    {
        $caret = new Caret($this);
        $this->args[] = $caret;
        return $caret;
    }

    public function __toString()
    {
        return implode(":", array_map(fn ($node) => $node->__toString(), $this->args));
    }

    function append_comma($child)
    {
        return $this->parent->append_comma($this);
    }
}

class Sentence extends PyObject
{

    public static function input_precedence()
    {
        return 0;
    }

    public static function stack_precedence()
    {
        return 0;
    }

    public function __construct($args)
    {
        $this->args = $args;
        foreach ($args as $arg) {
            $arg->parent = $this;
        }
    }

    function append_left_brace()
    {
        $caret = new Caret();
        $this->args[] = new Set($caret, $this);
        return $caret;
    }

    function append_left_parenthesis()
    {
        $caret = new Caret();
        $this->args[] = new Set($caret, $this);
        return $caret;
    }

    function append_identifier($name)
    {
        $parent = $this->parent;
        $suffix = new TreeNodeSuffix($identifier, $this, $parent);
        $parent->replace($this, $suffix);

        return $suffix;
    }

    public $args;

    public function __toString()
    {
        return implode("; ", array_map(fn ($node) => $node->__toString(), $this->args));
    }

    function replace($old, $new)
    {
        $i = array_search($old, $this->args, true);
        if ($i === false)
            throw new RuntimeException("void replace(TreeNode old, TreeNode replacement) throws Exception");
        $this->args[$i] = $new;
    }

    function append_comma($child)
    {
        $obj = end($this->args);
        assert($obj == $child);

        $caret = new Caret();
        $comma = new Comma([
            $obj,
            $caret
        ], $this);
        $this->replace($obj, $comma);
        return $caret;
    }

    function append_semicolon($child)
    {
        $caret = new Caret($this);
        $this->args[] = $caret;
        return $caret;
    }
}

function append_identifier(&$caret, &$infix, &$i)
{
    $end = search_for_identifier($infix, $i);

    if ($end == $i) {
        throw new RuntimeException("lexeme not found!");
    }

    // \std\println(\std\slice($infix, $i, $end));

    $caret = $caret->append_identifier(\std\slice($infix, $i, $end));

    $i = $end - 1;
}

function compile(string &$infix, &$state, $caret = null)
{
    if ($caret === null) {
        $caret = new Caret();
        $sentence = new Sentence([
            $caret
        ]);
    }

    $strlen = strlen($infix);    
    for ($i = 0; $i < $strlen; ++ $i) {
        $ch = $infix[$i];
        switch ($ch) {
            case "\t": // = 9;
                break;
            case "\n": // 0x0a;
                break;
            case "\v": // = 0x0b;
                break;
            case "\f": // = 0x0c;
                break;
            case "\r": // 0x0d;
                break;
            case "\x1b":
                break;

            case ' ':
                break;

            case '!':
                // unicodedata.name('!')
                if ($i + 1 < $strlen && $infix[$i + 1] == '=') {
                    ++ $i;
                    // x != y
                    $caret = $caret->parent->append_binary_operator('python\Unequal', $caret);
                } else {
                    throw new RuntimeException('illegal character $ch after !');
                }

                break;
            case '"':
                // unicodedata.name('"')
                $caret = $caret->append_literal($infix, $i, $ch);
                break;
            case '#':
                $state['commentStart'] = $i;
                return $caret;
            case '$':
                // unicodedata.name("$")
                $caret = $caret->append_dollarSign();
                break;

            case '%':
                // unicodedata.name("%")
                if ($i + 1 < $strlen && $infix[$i + 1] == '=') {
                    ++ $i;
                    $class = 'python\ModAssignment';
                } else {
                    $class = 'python\Mod';
                }
                $caret = $caret->parent->append_binary_operator($class, $caret);
                break;

            case '&':
                // unicodedata.name("&")
                if ($i + 1 < $strlen && $infix[$i + 1] == '=') {
                    ++ $i;
                    // x &= y
                    $class = 'python\BitwiseAndAssignment';
                } else {
                    // x & y
                    $class = 'python\BitwiseAnd';
                }

                $caret = $caret->parent->append_binary_operator($class, $caret);
                break;

            case "'":
                // unicodedata.name("'")
                $caret = $caret->append_literal($infix, $i, $ch);
                break;
            case '(':
                $caret = $caret->append_left_parenthesis();
                break;
            case ')':
                $caret = $caret->parent->append_right_parenthesis();
                break;

            case '*':
                if ($caret instanceof Caret) {
                    if ($i + 1 < $strlen && $infix[$i + 1] == '*') {
                        ++ $i;
                        // **kwargs
                        $class = 'python\DoubleStar';
                    } else {
                        // **args
                        $class = 'python\Star';
                    }

                    $caret = $caret->append_unary_operator($class);
                } else {
                    if ($i + 1 < $strlen) {

                        switch ($infix[$i + 1]) {
                            case '=':
                                ++ $i;
                                // x *= y
                                $class = 'python\MulAssignment';
                                break;
                            case '*':
                                ++ $i;
                                if ($i + 1 < $strlen && $infix[$i + 1] == '=') {
                                    ++ $i;
                                    // x **= y
                                    $class = 'python\PowAssignment';
                                } else {
                                    $class = 'python\Pow';
                                }

                                break;
                            default:
                                // x * y
                                $class = 'python\Mul';
                                break;
                        }
                    } else {
                        // x * y
                        $class = 'python\Mul';
                    }

                    $caret = $caret->parent->append_binary_operator($class, $caret);
                }

                break;
            case '+':
                if ($caret instanceof Caret) {
                    $caret = $caret->append_unary_operator('python\Plus');
                } else {
                    if ($i + 1 < $strlen && $infix[$i + 1] == '=') {

                        ++ $i;
                        // x += y
                        $class = 'python\AddAssignment';
                    } else {
                        // x + y
                        $class = 'python\Add';
                    }

                    $caret = $caret->parent->append_binary_operator($class, $caret);
                }

                break;
            case ',':
                $caret = $caret->parent->append_comma($caret);
                break;
            case '-':
                if ($caret instanceof Caret) {
                    $caret = $caret->append_unary_operator('python\Neg');
                } else {
                    if ($i + 1 < $strlen && $infix[$i + 1] == '=') {

                        ++ $i;
                        // x -= y
                        $class = 'python\SubAssignment';
                    } else {
                        // x - y
                        $class = 'python\Sub';
                    }

                    $caret = $caret->parent->append_binary_operator($class, $caret);
                }

                break;
            case '.':
                if ($i + 2 < $strlen && \std\equals(substr($infix, $i, 3), '...')) {
                    $i += 2;
                    $caret = $caret->append_ellipsis();
                } else {
                    $caret = $caret->parent->append_binary_operator('python\Dot', $caret);
                }

                break;
            case '/':
                if ($i + 1 < $strlen) {

                    switch ($infix[$i + 1]) {
                        case '=':
                            ++ $i;
                            // x /= y
                            $class = 'python\DivAssignment';
                            break;
                        case '/':
                            ++ $i;
                            if ($i + 1 < $strlen && $infix[$i + 1] == '=') {
                                ++ $i;
                                // x //= y
                                $class = 'python\FloorDivAssignment';
                            } else {
                                // x // y
                                $class = 'python\FloorDiv';
                            }

                            break;
                        default:
                            // x / y
                            $class = 'python\Div';
                            break;
                    }
                } else {
                    // x / y
                    $class = 'python\Div';
                }

                $caret = $caret->parent->append_binary_operator($class, $caret);

                break;
            case '0':
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
            case '8':
            case '9':
                $caret = $caret->append_digit($infix, $i);
                break;

            case ':':
                $caret = $caret->parent->append_colon($caret);
                break;

            case ';':
                $caret = $caret->parent->append_semicolon($caret);
                break;

            case '<':
                if ($i + 1 < $strlen) {
                    switch ($infix[$i + 1]) {
                        case '=':
                            ++ $i;
                            // x <= y
                            $class = 'python\LessEqual';
                            break;
                        case '<':
                            ++ $i;
                            if ($i + 1 < $strlen) {
                                switch ($infix[$i + 1]) {
                                    case '=':
                                        ++ $i;
                                        // x <<= y
                                        $class = 'python\LeftShiftAssignment';
                                        break;
                                    default:
                                        // x << y
                                        $class = 'python\LeftShift';
                                        break;
                                }
                            } else {
                                // x << y
                                $class = 'python\LeftShift';
                            }
                            break;
                        default:
                            // x < y
                            $class = 'python\Less';
                            break;
                    }
                }

                $caret = $caret->parent->append_binary_operator($class, $caret);
                break;

            case '=':
                if ($i + 1 < $strlen && $infix[$i + 1] == '=') {
                    ++ $i;
                    // x == y
                    $class = 'python\Equal';
                } else
                    $class = 'python\EqualAssignment';

                $caret = $caret->parent->append_binary_operator($class, $caret);
                break;

            case '>':

                if ($i + 1 < $strlen) {
                    switch ($infix[$i + 1]) {
                        case '=':
                            ++ $i;
                            // x >= y
                            $class = 'python\GreaterEqual';
                            break;
                        case '>':
                            ++ $i;
                            if ($i + 1 < $strlen && $infix[$i + 1] == '=') {
                                ++ $i;
                                // x >>= y
                                $class = 'python\RightShiftAssignment';
                            } else
                                // x >> y
                                $class = 'python\RightShift';
                            break;
                        default:
                            // x > y
                            $class = 'python\Greater';
                            break;
                    }
                } else
                    // x > y
                    $class = 'python\Greater';

                $caret = $caret->parent->append_binary_operator($class, $caret);
                break;

            case '?':
                // unicodedata.name('?')
                $caret = $caret->append_QuestionMark();
                break;
            case '@':
                // unicodedata.name('@')
                if ($i + 1 < $strlen && $infix[$i + 1] == '=') {
                    ++ $i;
                    $class = 'python\MatMulAssignment';
                } else
                    $class = 'python\MatMul';

                $caret = $caret->parent->append_binary_operator($class, $caret);
                break;
            case 'A':
            case 'B':
            case 'C':
            case 'D':
            case 'E':
            case 'F':
            case 'G':
            case 'H':
            case 'I':
            case 'J':
            case 'K':
            case 'L':
            case 'M':
            case 'N':
            case 'O':
            case 'P':
            case 'Q':
            case 'R':
            case 'S':
            case 'T':
            case 'U':
            case 'V':
            case 'W':
            case 'X':
            case 'Y':
            case 'Z':
                append_identifier($caret, $infix, $i);

                break;
            case '[':
                $caret = $caret->append_left_bracket();
                break;
            case '\\':
                // unicodedata.name('\\')
                if ($i < $strlen - 1){
                    switch(\std\slice($infix, $i + 1)){
                        case "\r\n":
                        case "\n":
                            break;
                        default:
                            throw new RuntimeException("illegal characters after ReverseSolidus: " . \std\slice($infix, $i));
                    } 
                }                    

                $state['ReverseSolidus'] = true;
                break;
            case ']':
                $caret = $caret->parent->append_right_bracket();
                break;

            case '^':
                if ($i + 1 < $strlen && $infix[$i + 1] == '=') {
                    ++ $i;
                    $class = 'python\ExclusiveOrAssignment';
                } else
                    $class = 'python\ExclusiveOr';

                $caret = $caret->parent->append_binary_operator($class, $caret);
                break;

            case '_':
                append_identifier($caret, $infix, $i);
                break;
            case '`':
                // unicodedata.name('`')
                $caret = $caret->append_GraveAccent();
                break;
            case 'a':
            case 'b':
            case 'c':
            case 'd':
            case 'e':
            case 'f':
            case 'g':
            case 'h':
            case 'i':
            case 'j':
            case 'k':
            case 'l':
            case 'm':
            case 'n':
            case 'o':
            case 'p':
            case 'q':
            case 'r':
            case 's':
            case 't':
            case 'u':
            case 'v':
            case 'w':
            case 'x':
            case 'y':
            case 'z':
                append_identifier($caret, $infix, $i);
                break;

            case '{':
                $caret = $caret->append_left_brace();
                break;

            case '|':
                if ($i + 1 < $strlen && $infix[$i + 1] == "=") {
                    ++ $i;
                    $class = 'python\BitwiseOrAssignment';
                } else
                    $class = 'python\BitwiseOr';

                $caret = $caret->parent->append_binary_operator($class, $caret);
                break;
            case '}':
                $caret = $caret->parent->append_right_brace();
                break;

            case '~':
                $caret = $caret->append_unary_operator('python\Invert');
                break;
            default:
                if (ord($ch) >= 128) {
                    append_identifier($caret, $infix, $i);
                } else {
                    \std\println("unrecognized character: " . ord($ch));
                }

                break;
        }
    }

    return $caret;
}

function fetch_whole_sentence($caret)
{
    for (;;) {
        if ($caret->parent !== null)
            $caret = $caret->parent;
        else
            break;
    }
    return $caret;
}

function len_args(&$statement, $caret = null)
{
    // error_log("in " . __function__);
    // error_log("statement = $statement");
    // error_log("caret = $caret");
    $state = [];
    
    $caret = compile($statement, $state, $caret);
    if ($state) {
        if (array_key_exists('ReverseSolidus', $state)) {
//             $statement = substr($statement, 0, - 1);
            unset($state['ReverseSolidus']);
            return $caret;
        }

        if (array_key_exists('commentStart', $state)) {
//             $commentStart = $state['commentStart'];
//             $charDeleted = strlen($line) - $commentStart;
//             $statement = substr($statement, 0, - $charDeleted);
            unset($state['commentStart']);
            return $caret;
        }
    }

    if ((function ($self) {
        for (;;) {
            $parent = $self->parent;
            if (is_unfinished($parent, $self)) {
                return true;
            }
            $self = $parent;
            if ($parent === null) {
                return false;
            }
        }
    })($caret)) {
        return $caret;
    }

    $sentence = fetch_whole_sentence($caret);
    list ($caret,) = $sentence->args;

    if ($caret instanceof Comma || $caret instanceof ArrayList || $caret instanceof Tuple) {
        $count = count($caret->args);
        $last = end($caret->args);
        if ($last instanceof Caret) {
            -- $count;
        }

        return $count;
    }

    return 1;
}

require_once 'std.php';

function is_unfinished($parent, $self)
{
    if ($parent instanceof FunctionCall || //
    $parent instanceof ArrayList || //
    $parent instanceof Tuple || //
    $parent instanceof Parenthesis || //
    $parent instanceof Indexed || //
    $parent instanceof Set)
        return true;

    if ($parent instanceof IfElse) {
        return $self !== $parent->other;
    }

    return false;
}

function main($offset = 0)
{
    // $py = "All(Any(cond._subs(x, y), *limits_e), *limits_f)";
    // $offset = 0;
    $count = 0;
    $caret = null;
    $folder = dirname(dirname(dirname(__file__)));
    // $folder = 'D:\Program Files\Python\Python36';
    // $folder = dirname(dirname(__file__));
    // $folder = dirname(__file__);
    foreach (\std\read_all_files($folder, 'py') as $py) {

        // \std\println("processing:\n" . $py);
        try {
            $py = new \std\Text($py);
        } catch (RuntimeException $e) {
            continue;
        }

        $paragraphCommentDoubleQuote = false;
        $paragraphCommentSingleQuote = false;
        // $history = [];
        foreach ($py as $line) {
            // $history[] = $line;
            $comment = false;
            if (! preg_match('/""".*"""/', $line, $m) && preg_match('/"""/', $line, $m)) {
                $paragraphCommentDoubleQuote = ! $paragraphCommentDoubleQuote;
                $comment = true;
            }

            if (! preg_match("/'''.*'''/", $line, $m) && preg_match("/'''/", $line, $m)) {
                $paragraphCommentSingleQuote = ! $paragraphCommentSingleQuote;
                $comment = true;
            }

            if ($caret === null) {
                if (preg_match('/^ +return(?=\W) *(.+)/', $line, $m)) {
                    // \std\println($line);
                    ++ $count;

                    if ($count + 1 <= $offset)
                        continue;

                    $statement = $m[1];

                    $line = $statement;
                } else
                    continue;
            } else {

                $statement .= $line;
            }

            if ($paragraphCommentDoubleQuote || $paragraphCommentSingleQuote || $comment) {
                continue;
            }

            \std\println($statement);

            try {
                $caret = compile($line, $state, $caret);
            } catch (RuntimeException $e) {
                \std\println($e->getMessage());
                \std\println("count = " . $count);
                \std\println($statement);
                $caret = null;
                $caret = compile($line, $state, $caret);

                $nodeString = (string) $caret;

                \std\println($nodeString);
                throw $e;
            }

            if ($state) {
                if (array_key_exists('ReverseSolidus', $state)) {
                    $statement = substr($statement, 0, - 1);
                    unset($state['ReverseSolidus']);
                    continue;
                }

                if (array_key_exists('commentStart', $state)) {
                    $commentStart = $state['commentStart'];
                    $charDeleted = strlen($line) - $commentStart;
                    $statement = substr($statement, 0, - $charDeleted);
                    unset($state['commentStart']);
                }
            }

            if ((function ($self) {
                for (;;) {
                    $parent = $self->parent;
                    if (is_unfinished($parent, $self)) {
                        return true;
                    }
                    $self = $parent;
                    if ($parent === null) {
                        return false;
                    }
                }
            })($caret)) {
                continue;
            }

            $nodeString = (string) fetch_whole_sentence($caret);
            if (! \std\equals(str_replace(' ', '', $nodeString), str_replace(' ', '', $statement))) {
                \std\println("count = " . $count);
                \std\println("caret = " . $caret);
                \std\println("original    = " . $statement);
                \std\println("transformed = " . $nodeString);
                throw new RuntimeException("mismatch detected");
            }
            $caret = null;
        }
    }

    \std\println("count = " . $count);
}

// main();

?>
