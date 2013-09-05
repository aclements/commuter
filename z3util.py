import collections
import z3
import simsym

def predicates(expr):
    """Return a list of Z3 predicate names satisfied by expr.

    If expr is an application, the list will include the Z3_OP_* that
    expr is an application of.

    This is for debugging purposes.  Real code should use the
    appropriate predicate functions directly.
    """

    res = set()
    for pred_name in dir(z3):
        if not pred_name.startswith("is_"):
            continue
        if pred_name == "is_app_of":
            continue
        pred = getattr(z3, pred_name)
        if pred(expr):
            res.add(pred_name)

    if z3.is_app(expr):
        for op_name in dir(z3):
            if not op_name.startswith("Z3_OP_"):
                continue
            if z3.is_app_of(expr, getattr(z3, op_name)):
                res.add(op_name)

    return res

class HashableAst(object):
    """Wrapper for simsym/Z3 ASTs for Python hashing and equality.

    HashableAsts implement Python's hashing and equality operation
    using structural hashing and equality of simsym and Z3 ASTs.  Both
    types of ASTs overload == to construct equality expressions.  This
    is good for building expressions, but makes ASTs unsuitable for
    direct use in dictionaries and sets.  Z3 ASTs additionally use
    default object hashing, making them further unsuitable.
    """

    def __init__(self, ast):
        self.ast = ast
        if z3.is_ast(ast):
            self.__type = "z3"
        elif isinstance(ast, simsym.Symbolic):
            self.__type = "simsym"
        else:
            self.__type = "value"

    def __str__(self):
        return "HashableAst(%s)" % self.ast

    def __repr__(self):
        return "HashableAst(%r)" % self.ast

    def __eq__(self, o):
        if self.__type != o.__type:
            # We could return False here, but it's way too easy to try
            # to compare Python values with things like z3.IntNumRef.
            raise TypeError("Cannot compare different HashableAst types")
        if self.__type == "z3" or self.__type == "simsym":
            return self.ast.eq(o.ast)
        else:
            return self.ast == o.ast

    def __hash__(self):
        if self.__type == "z3":
            return self.ast.hash()
        return hash(self.ast)

class AstSet(object):
    """A set of z3.AstRef/Symbolic objects."""

    def __init__(self):
        self.__set = set()

    def __str__(self):
        return "{" + ",".join(map(str, self)) + "}"

    def __contains__(self, ast):
        if not isinstance(ast, (z3.AstRef, simsym.Symbolic)):
            raise TypeError("Expected instance of z3.AstRef, got %r" % ast)
        return HashableAst(ast) in self.__set

    def __len__(self):
        return len(self.__set)

    def add(self, ast):
        if not isinstance(ast, (z3.AstRef, simsym.Symbolic)):
            raise TypeError("Expected instance of z3.AstRef, got %r" % ast)
        self.__set.add(HashableAst(ast))

    def __iter__(self):
        return (x.ast for x in self.__set)

    def issubset(self, o):
        return self.__set.issubset(o.__set)

    def issuperset(self, o):
        return self.__set.issuperset(o.__set)

    def isdisjoint(self, o):
        return self.__set.isdisjoint(o.__set)
