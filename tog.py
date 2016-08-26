#original code from http://smallshire.org.uk/sufficientlysmall/2010/04/11/a-hindley-milner-type-inference-implementation-in-python/
from __future__ import print_function
import gast
import itertools
from collections import defaultdict
import unittest
from textwrap import dedent

class InferenceError(Exception):
    """Raised if the type inference algorithm cannot infer types successfully"""
    def __init__(self, message):
        self.__message = message
    message = property(lambda self: self.__message)
    def __str__(self):
        return str(self.message)

# =======================================================#
# Types and type constructors

class TypeVariable(object):
    """A type variable standing for an arbitrary type.

    All type variables have a unique id, but names are only assigned lazily,
    when required.
    """

    next_variable_id = 0

    def __init__(self):
        self.id = TypeVariable.next_variable_id
        TypeVariable.next_variable_id += 1
        self.instance = None
        self.__name = None

    next_variable_name = 'a'

    @property
    def name(self):
        """Names are allocated to TypeVariables lazily, so that only TypeVariables
        present
        """
        if self.__name is None:
            self.__name = TypeVariable.next_variable_name
            if TypeVariable.next_variable_name[-1] != 'z':
                TypeVariable.next_variable_name = TypeVariable.next_variable_name[:-1] + chr(ord(TypeVariable.next_variable_name) + 1)
            else:
                TypeVariable.next_variable_name = TypeVariable.next_variable_name[:-1] + 'a'
        return "'" + self.__name

    def __str__(self):
        if self.instance is not None:
            return str(self.instance)
        else:
            return self.name

    def __repr__(self):
        return "TypeVariable(id = {0})".format(self.id)

    @staticmethod
    def reset():
        TypeVariable.next_variable_name = 'a'
        TypeVariable.next_variable_id = 0


class TypeOperator(object):
    """An n-ary type constructor which builds a new type from old"""

    def __init__(self, name, types):
        self.name = name
        self.types = types

    def __str__(self):
        num_types = len(self.types)
        if num_types == 0:
            return self.name
        else:
            return "({0} {1})" .format(self.name, ' -> '.join(map(str, self.types)))


class Collection(TypeOperator):

    def __init__(self, holder_type, key_type, value_type):
        super(Collection, self).__init__("collection", [holder_type, key_type, value_type])

    def __str__(self):
        if isinstance(self.types[0], TypeVariable):
            return '(collection {} -> {})'.format(self.types[1], self.types[2])
        if isinstance(self.types[0].types[0], ListCollection):
            return '(list {})'.format(self.types[2])
        if isinstance(self.types[0].types[0], SetCollection):
            return '(set {})'.format(self.types[2])
        if isinstance(self.types[0].types[0], DictCollection):
            return '(dict {} -> {})'.format(self.types[1], self.types[2])
        if isinstance(self.types[0].types[0], StrCollection):
            return 'str'
        if isinstance(self.types[0].types[0], GenerableCollection):
            return '(gen {})'.format(self.types[2])
        assert False

class ListCollection(TypeOperator):
    def __init__(self):
        super(ListCollection, self).__init__("list", [])
class SetCollection(TypeOperator):
    def __init__(self):
        super(SetCollection, self).__init__("set", [])
class DictCollection(TypeOperator):
    def __init__(self):
        super(DictCollection, self).__init__("dict", [])
class StrCollection(TypeOperator):
    def __init__(self):
        super(StrCollection, self).__init__("str", [])
class GenerableCollection(TypeOperator):
    def __init__(self):
        super(GenerableCollection, self).__init__("gen", [])

LenTrait = TypeOperator("len", [])
NoLenTrait = TypeOperator("no_len", [])

class List(Collection):

    def __init__(self, of_type):
        super(List, self).__init__(Traits([ListCollection(), LenTrait]), Integer, of_type)

class Set(Collection):

    def __init__(self, of_type):
        super(Set, self).__init__(Traits([SetCollection(), LenTrait]), InvalidKey, of_type)

class Dict(Collection):

    def __init__(self, key_type, value_type):
        super(Dict, self).__init__(Traits([DictCollection(), LenTrait]), key_type, value_type)

class Str(Collection):

    def __init__(self, rec=True):
        super(Str, self).__init__(Traits([StrCollection(), LenTrait]), Integer, Str(rec=False) if rec else InvalidKey)

class Generator(Collection):

    def __init__(self, of_type):
        super(Generator, self).__init__(Traits([GenerableCollection(), NoLenTrait]), InvalidKey, of_type)

ExceptionType = TypeOperator("exception", [])

class Tuple(TypeOperator):

    def __init__(self, of_types):
        super(Tuple, self).__init__("tuple", of_types)

Traits = Tuple


class Function(TypeOperator):
    """A binary type constructor which builds function types"""

    def __init__(self, from_types, to_type):
        super(Function, self).__init__('fun', list(from_types) + [to_type])

    @property
    def arity(self):
        return len(self.types) - 1

class UnionType(object):
    """A binary type constructor which builds function types"""

    def __init__(self, types):
        self.types = types

    def __str__(self):
        return '(' + ' | '.join(sorted(map(str, self.types))) + ')'

class NoneOperator(TypeOperator):

    def __init__(self):
        super(NoneOperator, self).__init__('none', [])

# Basic types are constructed with a nullary type constructor
Integer = TypeOperator("int", [])  # Basic integer
Float = TypeOperator("float", [])  # Double precision float
Bool = TypeOperator("bool", [])  # Basic bool
InvalidKey = TypeOperator("invalid-key", [])  # invalid key - for non-indexable collection
NoneType = NoneOperator()


####

def analyse_body(body, env, non_generic):
    #first step to gather global symbols
    for stmt in body:
        if isinstance(stmt, gast.FunctionDef):
            new_type = TypeVariable()
            env[stmt.name] = new_type
    # second to perform local inference
    for stmt in body:
        analyse(stmt, env, non_generic)
    # then to complete types
    # FIXME: why is this needed?
    for stmt in body:
        analyse(stmt, env, non_generic)

class HasYield(gast.NodeVisitor):

    def __init__(self):
        super(HasYield, self).__init__()
        self.has_yield = False

    def visit_FunctionDef(self, node):
        pass

    def visit_Yield(self, node):
        self.has_yield = True


def analyse(node, env, non_generic=None):
    """Computes the type of the expression given by node.

    The type of the node is computed in the context of the context of the
    supplied type environment env. Data types can be introduced into the
    language simply by having a predefined set of identifiers in the initial
    environment. environment; this way there is no need to change the syntax or, more
    importantly, the type-checking program when extending the language.

    Args:
        node: The root of the abstract syntax tree.
        env: The type environment is a mapping of expression identifier names
            to type assignments.
            to type assignments.
        non_generic: A set of non-generic variables, or None

    Returns:
        The computed type of the expression.

    Raises:
        InferenceError: The type of the expression could not be inferred, for example
            if it is not possible to unify two types such as Integer and Bool
        ParseError: The abstract syntax tree rooted at node could not be parsed
    """

    if non_generic is None:
        non_generic = set()

    # expr
    if isinstance(node, gast.Name):
        if isinstance(node.ctx, (gast.Store, gast.AugStore)):
            new_type = TypeVariable()
            non_generic.add(new_type)
            if node.id in env:
                unify(env[node.id], new_type)
            else:
                env[node.id] = new_type
        return get_type(node.id, env, non_generic)
    elif isinstance(node, gast.Num):
        if isinstance(node.n, int):
            return Integer
        elif isinstance(node.n, float):
            return Float
        else:
            raise NotImplementedError
    elif isinstance(node, gast.Str):
        return Str()
    elif isinstance(node, gast.Call):
        fun_type = analyse(node.func, env, non_generic)
        arg_types = [analyse(arg, env, non_generic) for arg in node.args]
        result_type = TypeVariable()
        unify(Function(arg_types, result_type), fun_type)
        return result_type
    elif isinstance(node, gast.Lambda):
        new_env = env.copy()
        new_non_generic = non_generic.copy()

        arg_types = []
        for arg in node.args.args:
            arg_type = TypeVariable()
            new_env[arg.id] = arg_type
            new_non_generic.add(arg_type)
            arg_types.append(arg_type)

        result_type = analyse(node.body, new_env, new_non_generic)
        return Function(arg_types, result_type)
    elif isinstance(node, gast.IfExp):
        body_type = analyse(node.body, env, non_generic)
        orelse_type = analyse(node.orelse, env, non_generic)
        return merge_type(body_type, orelse_type)
    elif isinstance(node, gast.BinOp):
        left_type = analyse(node.left, env, non_generic)
        op_type = analyse(node.op, env, non_generic)
        right_type = analyse(node.right, env, non_generic)
        result_type = TypeVariable()
        unify(Function([left_type, right_type], result_type), op_type)
        return result_type
    elif isinstance(node, gast.Sub):
        var = TypeVariable()
        return Function([var, var], var)
    elif isinstance(node, gast.Add):
        var = TypeVariable()
        return Function([var, var], var)
    elif isinstance(node, gast.Mult):
        var = TypeVariable()
        return UnionType([
            Function([Integer, Integer], Integer),
            Function([Float, Float], Float),
        ]
        )
    elif isinstance(node, gast.List):
        new_type = TypeVariable()
        for elt in node.elts:
            elt_type = analyse(elt, env, non_generic)
            unify(new_type, elt_type)
        return List(new_type)
    elif isinstance(node, gast.Set):
        new_type = TypeVariable()
        for elt in node.elts:
            elt_type = analyse(elt, env, non_generic)
            unify(new_type, elt_type)
        return Set(new_type)
    elif isinstance(node, gast.Dict):
        new_key_type = TypeVariable()
        for key in node.keys:
            key_type = analyse(key, env, non_generic)
            unify(new_key_type, key_type)
        new_value_type = TypeVariable()
        for value in node.values:
            value_type = analyse(value, env, non_generic)
            unify(new_value_type, value_type)
        return Dict(new_key_type, new_value_type)
    elif isinstance(node, gast.Tuple):
        return Tuple([analyse(elt, env, non_generic) for elt in node.elts])
    elif isinstance(node, gast.ListComp):
        # create new env, as in Python3
        new_env = env.copy()
        new_non_generic = non_generic.copy()
        for generator in node.generators:
            analyse(generator, new_env, new_non_generic)
        elt_type = analyse(node.elt, new_env, new_non_generic)
        return List(elt_type)
    elif isinstance(node, gast.SetComp):
        # create new env, as in Python3
        new_env = env.copy()
        new_non_generic = non_generic.copy()
        for generator in node.generators:
            analyse(generator, new_env, new_non_generic)
        elt_type = analyse(node.elt, new_env, new_non_generic)
        return Set(elt_type)
    elif isinstance(node, gast.DictComp):
        # create new env, as in Python3
        new_env = env.copy()
        new_non_generic = non_generic.copy()
        for generator in node.generators:
            analyse(generator, new_env, new_non_generic)
        key_type = analyse(node.key, new_env, new_non_generic)
        value_type = analyse(node.value, new_env, new_non_generic)
        return Dict(key_type, value_type)
    elif isinstance(node, gast.GeneratorExp):
        # create new env, as in Python3
        new_env = env.copy()
        new_non_generic = non_generic.copy()
        for generator in node.generators:
            analyse(generator, new_env, new_non_generic)
        elt_type = analyse(node.elt, new_env, new_non_generic)
        return Generator(elt_type)
    elif isinstance(node, gast.comprehension):
        target_type = analyse(node.target, env, non_generic)
        iter_type = analyse(node.iter, env, non_generic)
        new_type = Collection(TypeVariable(), TypeVariable(), target_type)
        unify(new_type, iter_type)
        return new_type
    elif isinstance(node, gast.Index):
        return analyse(node.value, env, non_generic)
    elif isinstance(node, gast.NameConstant):
        if node.value is None:
            return env['None']
    elif isinstance(node, gast.Subscript):
        new_type = TypeVariable()
        value_type = analyse(node.value, env, non_generic)
        index_type = analyse(node.slice, env, non_generic)
        if isinstance(node.slice, gast.Index):
            unify(Collection(TypeVariable(), index_type, new_type), value_type)
        else:
            raise NotImplementedError()
        return new_type
    # stmt
    elif isinstance(node, gast.ImportFrom):
        if node.module not in Modules:
            raise NotImplementedError("unknown module: %s" % node.module)
        for alias in node.names:
            if alias.name not in Modules[node.module]:
                raise NotImplementedError("unknown function: %s in %s" % (alias.name, node.module))
            if alias.asname is None:
                target = alias.name
            else:
                target = alias.asname
            env[target] = Modules[node.module][alias.name]
        return env
    elif isinstance(node, gast.FunctionDef):
        old_type = env[node.name]
        new_env = env.copy()
        new_non_generic = non_generic.copy()

        # reset return special variables
        new_env.pop('@ret', None)
        new_env.pop('@gen', None)

        hy = HasYield()
        for stmt in node.body:
            hy.visit(stmt)
        new_env['@gen'] = hy.has_yield

        arg_types = []
        for arg in node.args.args:
            arg_type = TypeVariable()
            new_env[arg.id] = arg_type
            new_non_generic.add(arg_type)
            arg_types.append(arg_type)

        analyse_body(node.body, new_env, new_non_generic)

        # TODO: need a CFG analyse here to check if we need to add a return None
        result_type = new_env.get('@ret', NoneType)

        if new_env['@gen']:
            result_type = Generator(result_type)

        ftype = Function(arg_types, result_type)
        unify(old_type, ftype)
        return env
    elif isinstance(node, gast.Module):
        analyse_body(node.body, env, non_generic)
        return env
    elif isinstance(node, (gast.Pass, gast.Break, gast.Continue)):
        return env
    elif isinstance(node, gast.Expr):
        analyse(node.value, env, non_generic)
        return env
    elif isinstance(node, gast.Delete):
        for target in node.target:
            if isinstance(target, gast.Name):
                del env[target.id]
            else:
                analyse(target, env, non_generic)
    elif isinstance(node, gast.Print):
        if node.dest is not None:
            analyse(node.dest, env, non_generic)
        for value in node.values:
            analyse(value, env, non_generic)
        return env
    elif isinstance(node, gast.Assign):
        defn_type = analyse(node.value, env, non_generic)
        for target in node.targets:
            target_type = analyse(target, env, non_generic)
            unify(target_type, defn_type)
        return env
    elif isinstance(node, gast.AugAssign):
        defn_type = analyse(node.value, env, non_generic)
        target_type = analyse(node.target, env, non_generic)
        unify(target_type, defn_type)
        return env
    elif isinstance(node, gast.Return):
        if env['@gen']:
            return env

        if node.value is None:
            ret_type = NoneType
        else:
            ret_type = analyse(node.value, env, non_generic)

        if '@ret' in env:
            env['@ret'] = merge_type(env['@ret'], ret_type)
        else:
            env['@ret'] = ret_type
        return env
    elif isinstance(node, gast.Yield):
        assert env['@gen']
        assert node.value is not None

        ret_type = analyse(node.value, env, non_generic)

        if '@ret' in env:
            env['@ret'] = merge_type(env['@ret'], ret_type)
        else:
            env['@ret'] = ret_type
        return env
    elif isinstance(node, gast.For):
        iter_type = analyse(node.iter, env, non_generic)
        target_type = analyse(node.target, env, non_generic)
        unify(Collection(TypeVariable(), TypeVariable(), target_type), iter_type)
        analyse_body(node.body, env, non_generic)
        analyse_body(node.orelse, env, non_generic)
        return env
    elif isinstance(node, gast.If):
        test_type = analyse(node.test, env, non_generic)

        body_env = env.copy()
        body_non_generic = non_generic.copy()
        analyse_body(node.body, body_env, body_non_generic)

        orelse_env = env.copy()
        orelse_non_generic = non_generic.copy()
        analyse_body(node.orelse, orelse_env, orelse_non_generic)

        for var in body_env:
            if var not in env:
                if var in orelse_env:
                    new_type = merge_type(body_env[var], orelse_env[var])
                else:
                    new_type = body_env[var]
                env[var] = new_type

        for var in orelse_env:
            if var not in env:
                # may not be unified by the prev loop if a del occured
                if var in body_env:
                    new_type = merge_type(orelse_env[var], body_env[var])
                else:
                    new_type = orelse_env[var]
                env[var] = new_type

        return env
    elif isinstance(node, gast.While):
        analyse(node.test, env, non_generic)
        analyse_body(node.body, env, non_generic)
        analyse_body(node.orelse, env, non_generic)
        return env
    elif isinstance(node, gast.Try):
        analyse_body(node.body, env, non_generic)
        for handler in node.handlers:
            analyse(handler, env, non_generic)
        analyse_body(node.orelse, env, non_generic)
        analyse_body(node.finalbody, env, non_generic)
        return env
    elif isinstance(node, gast.ExceptHandler):
        if(node.name):
            new_type = ExceptionType
            non_generic.add(new_type)
            if node.name.id in env:
                unify(env[node.name.id], new_type)
            else:
                env[node.name.id] = new_type
        analyse_body(node.body, env, non_generic)
        return env
    raise RuntimeError("Unhandled syntax node {0}".format(type(node)))

def get_type(name, env, non_generic):
    """Get the type of identifier name from the type environment env.

    Args:
        name: The identifier name
        env: The type environment mapping from identifier names to types
        non_generic: A set of non-generic TypeVariables

    Raises:
        ParseError: Raised if name is an undefined symbol in the type
            environment.
    """
    if name in env:
        return fresh(env[name], non_generic)
    elif is_integer_literal(name):
        return Integer
    else:
        raise RuntimeError("Undefined symbol {0}".format(name))


def fresh(t, non_generic):
    """Makes a copy of a type expression.

    The type t is copied. The generic variables are duplicated and the
    non_generic variables are shared.

    Args:
        t: A type to be copied.
        non_generic: A set of non-generic TypeVariables
    """

    mappings = {}  # A mapping of TypeVariables to TypeVariables

    def freshrec(tp):
        p = prune(tp)
        if isinstance(p, TypeVariable):
            if is_generic(p, non_generic):
                if p not in mappings:
                    mappings[p] = TypeVariable()
                return mappings[p]
            else:
                return p
        elif isinstance(p, NoneOperator):
            return p  # FIXME
        elif isinstance(p, StrCollection):
            return StrCollection()
        elif isinstance(p, ListCollection):
            return ListCollection()
        elif isinstance(p, SetCollection):
            return SetCollection()
        elif isinstance(p, DictCollection):
            return DictCollection()
        elif isinstance(p, GenerableCollection):
            return GenerableCollection()
        elif isinstance(p, Collection):
            return Collection(*[freshrec(x) for x in p.types])
        elif isinstance(p, TypeOperator):
            return TypeOperator(p.name, [freshrec(x) for x in p.types])
        elif isinstance(p, UnionType):
            return UnionType([freshrec(x) for x in p.types])
        else:
            assert False, "missing freshrec case {}".format(type(p))

    return freshrec(t)

def unify(t1, t2):
    """Unify the two types t1 and t2.

    Makes the types t1 and t2 the same.

    Args:
        t1: The first type to be made equivalent
        t2: The second type to be be equivalent

    Returns:
        None

    Raises:
        InferenceError: Raised if the types cannot be unified.
    """

    a = prune(t1)
    b = prune(t2)
    if isinstance(a, TypeVariable):
        if a != b:
            if occurs_in_type(a, b):
                raise InferenceError("recursive unification")
            a.instance = b
    elif isinstance(b, TypeVariable):
        unify(b, a)
    elif isinstance(a, TypeOperator) and isinstance(b, TypeOperator):
        if len(a.types) != len(b.types):
            raise InferenceError("Type mismatch: {0} != {1}".format(str(a), str(b)))
        else:
            if a.name != b.name:
                raise InferenceError("Type mismatch: {0} != {1}".format(str(a), str(b)))
        for p, q in zip(a.types, b.types):
            unify(p, q)
    elif isinstance(a, UnionType) and isinstance(b, UnionType):
        if len(a.types) != len(b.types):
            raise InferenceError("Type mismatch: {0} != {1}".format(str(a), str(b)))
        for p, q in zip(a.types, b.types):
            unify(p, q)
    elif isinstance(b, UnionType):
        return unify(b, a)
    elif isinstance(a, UnionType):
        for t in a.types:
            try:
                t_clone = fresh(t, {})
                b_clone = fresh(b, {})
                unify(t_clone, b_clone)
            except InferenceError as e:
                pass
            else:
                t_clone = fresh(t, {})
                unify(t_clone, b)
                return
        raise RuntimeError("Not unified {} and {}, no overload found".format(type(a), type(b)))
    else:
        raise RuntimeError("Not unified {} and {}".format(type(a), type(b)))

def merge_type(t1, t2):
    '''
    Similar to unify, but handles option types
    '''
    if isinstance(t1, TypeVariable) and isinstance(t2, NoneOperator):
        t = UnionType(t1, t2)
        unify(t, t1)
        unify(t, t2)
        return t

    if isinstance(t2, TypeVariable) and isinstance(t1, NoneOperator):
        return merge_type(t2, t1)

    if isinstance(t1, NoneOperator) and isinstance(t2, NoneOperator):
        return t1

    unify(t1, t2)
    return t1



def prune(t):
    """Returns the currently defining instance of t.

    As a side effect, collapses the list of type instances. The function Prune
    is used whenever a type expression has to be inspected: it will always
    return a type expression which is either an uninstantiated type variable or
    a type operator; i.e. it will skip instantiated variables, and will
    actually prune them from expressions to remove long chains of instantiated
    variables.

    Args:
        t: The type to be pruned

    Returns:
        An uninstantiated TypeVariable or a TypeOperator
    """
    if isinstance(t, TypeVariable):
        if t.instance is not None:
            t.instance = prune(t.instance)
            return t.instance
    return t


def is_generic(v, non_generic):
    """Checks whether a given variable occurs in a list of non-generic variables

    Note that a variables in such a list may be instantiated to a type term,
    in which case the variables contained in the type term are considered
    non-generic.

    Note: Must be called with v pre-pruned

    Args:
        v: The TypeVariable to be tested for genericity
        non_generic: A set of non-generic TypeVariables

    Returns:
        True if v is a generic variable, otherwise False
    """
    return not occurs_in(v, non_generic)


def occurs_in_type(v, type2):
    """Checks whether a type variable occurs in a type expression.

    Note: Must be called with v pre-pruned

    Args:
        v:  The TypeVariable to be tested for
        type2: The type in which to search

    Returns:
        True if v occurs in type2, otherwise False
    """
    pruned_type2 = prune(type2)
    if pruned_type2 == v:
        return True
    elif isinstance(pruned_type2, TypeOperator):
        return occurs_in(v, pruned_type2.types)
    return False


def occurs_in(t, types):
    """Checks whether a types variable occurs in any other types.

    Args:
        t:  The TypeVariable to be tested for
        types: The sequence of types in which to search

    Returns:
        True if t occurs in any of types, otherwise False
    """
    return any(occurs_in_type(t, t2) for t2 in types)


def is_integer_literal(name):
    """Checks whether name is an integer literal string.

    Args:
        name: The identifier to check

    Returns:
        True if name is an integer literal, otherwise False
    """
    result = True
    try:
        int(name)
    except ValueError:
        result = False
    return result

def pp(env):
    for key, value in env.items():
        print(key, ':', value)

def make_zip_function(n):
    candidates = []
    for arity in range(n):
       new_holder_types = [TypeVariable() for _ in range(arity)]
       new_index_types = [TypeVariable() for _ in range(arity)]
       new_value_types = [TypeVariable() for _ in range(arity)]
       candidates.append(Function([Collection(h, i, v) for h, i, v in zip(new_holder_types, new_index_types, new_value_types)],
                        List(Tuple(new_value_types))))
    return UnionType(candidates)

ZipFunction = make_zip_function(4)



def make_map_function(n):
    candidates = []
    for arity in range(n):
        f_arg_types0 = [TypeVariable() for _ in range(arity - 1)]
        f_ret_type = TypeVariable()
        arg_types0 = [Collection(TypeVariable(), TypeVariable(), f_arg_type) for f_arg_type in f_arg_types0]

        f_arg_types1 = [TypeVariable() for _ in range(arity - 1)]
        arg_types1 = [Collection(TypeVariable(), TypeVariable(), f_arg_type) for f_arg_type in f_arg_types1]
        candidates.extend( [Function([Function(arg_types0, f_ret_type)] + arg_types0, List(f_ret_type)),
                Function([NoneType] + arg_types1, List(Tuple(f_arg_types1)))
               ])
    return UnionType(candidates)

MapFunction = make_map_function(4)


def make_partial_function(n):
    candidates = []
    for arity in range(n):
        for nb_placeholders in range(arity):
            f_args = [TypeVariable() for _ in range(arity)]
            f_res = TypeVariable()
            candidates.append(Function([Function(f_args, f_res)] + f_args[:nb_placeholders],
                                       Function(f_args[nb_placeholders:], f_res)))
    return UnionType(candidates)

PartialFunction = make_partial_function(4)


builtins = {
    'len': Function([Collection(TypeVariable(), TypeVariable(), TypeVariable())], Integer),
    'zip': ZipFunction,
    'map': MapFunction,
    'None': NoneType,
    'print': UnionType([Function([TypeVariable() for _ in range(i)], NoneType) for i in range(5)]),
}

Modules = {
    'functools': {
        'partial': PartialFunction,
    },
    'math': {
        'cos': Function([Float], Float),
        'sin': Function([Float], Float),
    },
}

class TestTypeInference(unittest.TestCase):

    def check(self, code, ref):
        TypeVariable.reset()
        node = gast.parse(dedent(code))

        env = builtins.copy()
        types = analyse(node, env)
        out = ''
        new_env = {k: v for k, v in env.items() if len(k) == 1}
        for key, value in sorted(new_env.items()):
            out += '{}: {}\n'.format(key, value)
        self.assertEqual(out.strip(), dedent(ref).strip())

    def test_retun_int(self):
        self.check('def f(): return 0',
                   'f: (fun int)')

    def test_retun_float(self):
        self.check('def f(): return 0.',
                   'f: (fun float)')

    def test_identity(self):
        self.check('def f(x): return x',
                   "f: (fun 'a -> 'a)")

    def test_call(self):
        self.check('''
            def f(x, y): return y
            def g(x): return f(x, 1)
            ''',
            '''
            f: (fun 'a -> 'b -> 'b)
            g: (fun 'c -> int)
            ''')

    def test_fw_call(self):
        self.check('''
            def g(x): return f(x, 1)
            def f(x, y): return y
            ''',
            '''
            f: (fun 'a -> 'b -> 'b)
            g: (fun 'c -> int)
            ''')

    def test_simple_rec(self):
        self.check('def f(x): return f(x-1) + f(x-2) if x > 2 else x',
                   'f: (fun int -> int)')

    def test_empty_list(self):
        self.check('def f(): return []',
                   "f: (fun (list 'a))")

    def test_list_of(self):
        self.check('def f(x): return [x]',
                   "f: (fun 'a -> (list 'a))")

    def test_assign_list_content(self):
        self.check('def f(x): a = [x] ; a[0] = 1 ; return a',
                   "f: (fun int -> (list int))")

    def test_assign_change_content(self):
        self.check('def f(x): x[0] = 1 ; return x',
                   "f: (fun (collection int -> int) -> (collection int -> int))")

    def test_nested_function(self):
        self.check('''
                def f(x):
                   y = 1
                   def g(x): return y
                   return g''',
                   "f: (fun 'a -> (fun 'b -> int))")

    def test_overload(self):
        self.check('def f(x, y): a, b = x * 1, y * 1.; return b, a',
                   "f: (fun int -> float -> (tuple float -> int))")

    def test_listcomp(self):
        self.check('def f(x): return [1 for _ in x]',
                   "f: (fun (collection 'a -> 'b) -> (list int))")

    def test_upcasting(self):
        self.check('''
                def g(y): return y
                def f(x):
                    a = [x]
                    r = g(a[0])
                    a[0] = 1.
                    s = a[1]
                    return s
                ''',
                '''
                f: (fun float -> float)
                g: (fun 'a -> 'a)
                ''')

    def test_for(self):
        self.check('''
                def f(x):
                   s = x[0]
                   for y in x:
                      s += y
                   return s
                ''',
                '''
                f: (fun (collection int -> 'a) -> 'a)
                ''')

    def test_while(self):
        self.check('''
                def f(x):
                   while x:
                      x -= 1
                   return x
                ''',
                '''
                f: (fun int -> int)
                ''')

    def test_tuple(self):
        self.check('def f(x, y): return x, y',
                   "f: (fun 'a -> 'b -> (tuple 'a -> 'b))")

    def test_type_destructuring_assign(self):
        self.check('def f(x, y): y, x =  x, y; return x',
                   "f: (fun 'a -> 'a -> 'a)")

    def test_type_destructuring_loop_comp(self):
        self.check('def f(x): return [a + b for a, b in x]',
                   "f: (fun (collection 'a -> (tuple 'b -> 'b)) -> (list 'b))")

    def test_type_destructuring_loop(self):
        self.check('def f(x):\n for i, j in x: return i',
                   "f: (fun (collection 'a -> (tuple 'b -> 'c)) -> 'b)")

    def test_set(self):
        self.check('def f(x): return {x}',
                   "f: (fun 'a -> (set 'a))")

    def test_setcomp(self):
        self.check('def f(x): return {1 for _ in x}',
                   "f: (fun (collection 'a -> 'b) -> (set int))")

    def test_dict(self):
        self.check('def f(x): return {x:1}',
                   "f: (fun 'a -> (dict 'a -> int))")

    def test_dictcomp(self):
        self.check('def f(x): return {v: 1 for v in x}',
                   "f: (fun (collection 'a -> 'b) -> (dict 'b -> int))")

    def test_str(self):
        self.check('def f(x): return "hello"',
                  "f: (fun 'a -> str)")

    def test_pass(self):
        self.check('def f(): pass; return 1',
                   'f: (fun int)')

    def test_break(self):
        self.check('def f():\n while 1: break; return 1',
                   'f: (fun int)')

    def test_continue(self):
        self.check('def f():\n while 0: continue; return 1',
                   'f: (fun int)')

    def test_expr(self):
        self.check('def f(): 1; return 1',
                   'f: (fun int)')

    def test_print(self):
        self.check('def f(): print(1); return 1',
                   'f: (fun int)')

    def test_no_return(self):
        self.check('def f(): print()',
                   "f: (fun none)")

    def test_return_none(self):
        self.check('def f(): return',
                   "f: (fun none)")

#    def test_return_opt(self):
#        self.check('def f(x):\n if x: return x\n else: return',
#                   "f: (fun 'a -> ('a | none))")
#
#
    def test_string_iteration(self):
        self.check('def f(): a = "er"; return [x for x in a]',
                   'f: (fun (list str))')

    def test_lambda(self):
        self.check('def f(x): return (lambda x: x[0])([y for y in x])',
                   "f: (fun (collection 'a -> 'b) -> 'b)")

    def test_return_lambda(self):
        self.check('def f(x): return (lambda x: x[0])',
                   "f: (fun 'a -> (fun (collection int -> 'b) -> 'b))")

    def test_len(self):
        self.check('def f(x): a = "er"; return len(a), len(x)',
                   "f: (fun (collection 'a -> 'b) -> (tuple int -> int))")

    def test_zip(self):
        self.check('def f(x, y): return zip(x, y)',
                   "f: (fun (collection 'o -> 'p) -> (collection 'q -> 'r) -> (list (tuple 'p -> 'r)))")

    def test_map(self):
        self.check('def f(x, y): return map(None, x, y), map(len, x)',
                   "f: (fun (collection 'y -> 'z) -> (collection 'a -> 'b) -> (tuple (list (tuple 'z -> 'b)) -> (list int)))")

    def test_union_type(self):
        self.check('def f(x, y): return map(x, y)',
                   "f: (fun (fun (collection 'm -> 'n) -> 'o) -> (collection 'm -> 'n) -> (list 'o))")

    def test_import_from(self):
        self.check('''
                   from math import cos as c, sin
                   def f(x): return c(x), sin(x)
                   ''',
                   '''
                   c: (fun float -> float)
                   f: (fun float -> (tuple float -> float))
                   ''')



    def test_partial(self):
        self.check('''
                   from functools import partial
                   def f(x, y, z): return x + y + z
                   def g(x): return partial(f, x, 1)
                   def h(x):
                        def foo(w):
                            return f(x, 1, w)
                        return foo
                   ''',
                   '''
                   f: (fun 'k -> 'k -> 'k -> 'k)
                   g: (fun int -> (fun int -> int))
                   h: (fun int -> (fun int -> int))
                   ''')

    def test_generatorexp(self):
        self.check('def f(x, y): return (z + y for z in x)',
                   "f: (fun (collection 'a -> 'b) -> 'b -> (gen 'b))"
                  )

    def test_generator(self):
        self.check('def f(x): yield x ; return',
                   "f: (fun 'a -> (gen 'a))"
                  )

    def test_except(self):
        self.check("""
                   def f(x, y):
                       try:
                           return y
                       except RuntimeError:
                           return x
                   """,
                   "f: (fun 'a -> 'a -> 'a)")

    def test_multi_except(self):
        self.check("""
                   def f(x, y):
                       try:
                           return y
                       except RuntimeError:
                           return x
                       except:
                           return 4
                   """,
                   "f: (fun int -> int -> int)")

    def test_except_orelse(self):
        self.check("""
                   def f(x, y):
                       try:
                           return y
                       except RuntimeError:
                           return x
                       else:
                           return 4
                   """,
                   "f: (fun int -> int -> int)")

    def test_except_finally(self):
        self.check("""
                   def f(x, y):
                       try:
                           return y
                       except RuntimeError:
                           return x
                       finally:
                           return 4.
                   """,
                   "f: (fun float -> float -> float)")

    def test_except_def_name(self):
        self.check("""
                   def f(x, y):
                       try:
                           return y
                       except RuntimeError as e:
                           return e
                   """,
                   "f: (fun 'a -> exception -> exception)")

    def test_except_redef_name(self):
        self.check("""
                   def f(e, y):
                       try:
                           return y
                       except RuntimeError as e:
                           return 1
                   """,
                   "f: (fun exception -> int -> int)")


if __name__ == '__main__':
    unittest.main()
