#original code from http://smallshire.org.uk/sufficientlysmall/2010/04/11/a-hindley-milner-type-inference-implementation-in-python/
from __future__ import print_function
import gast
import itertools
from collections import defaultdict
from functools import reduce
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
        t0 = prune(self.types[0])
        if isinstance(t0, TypeVariable):
            return '(collection {} -> {})'.format(self.types[1], self.types[2])
        if isinstance(t0, TypeOperator) and t0.name == 'traits' and all(isinstance(prune(t), TypeVariable) for t in t0.types):
            return '(collection {} -> {})'.format(self.types[1], self.types[2])
        t00 = prune(t0.types[0])
        if isinstance(t00, TypeOperator):
            type_trait = t00.name
            if type_trait == 'list':
                return '(list {})'.format(self.types[2])
            if type_trait == 'set':
                return '(set {})'.format(self.types[2])
            if type_trait == 'dict':
                return '(dict {} -> {})'.format(self.types[1], self.types[2])
            if type_trait == 'str':
                return 'str'
            if type_trait == 'tuple':
                return str(t00)
            if type_trait == 'array':
                t01 = prune(t0.types[1])
                if isinstance(t01, TypeOperator) and t01.name == NoLenTrait.name:
                    return str(self.types[2])
                def rec(n):
                    pn = prune(n)
                    if isinstance(pn, Collection):
                        traits = prune(pn.types[0])
                        # a scalar or array?
                        if isinstance(traits, TypeVariable):
                            return pn.types[2], 0
                        len_trait = prune(traits.types[1])
                        # an array?
                        if isinstance(len_trait, TypeOperator) and len_trait.name == LenTrait.name:
                            t, n = rec(pn.types[2])
                            return t, n + 1
                        # a scalar or array?
                        else:
                            return pn.types[2], 0
                    else:
                        return pn, 0
                t, n = rec(self)
                if isinstance(t, TypeVariable):
                    return '({}d+ array {})'.format(n, t)
                else:
                    return '({}d array {})'.format(n, t)
            if type_trait == 'gen':
                return '(gen {})'.format(self.types[2])
        return super(Collection, self).__str__()

def TupleTrait(of_types):
    return TypeOperator('tuple', of_types)
ListTrait = TypeOperator('list', [])
SetTrait = TypeOperator('set', [])
DictTrait = TypeOperator('dict', [])
StrTrait = TypeOperator('str', [])
ArrayTrait = TypeOperator('array', [])
GenerableTrait = TypeOperator('gen', [])

LenTrait = TypeOperator("len", [])
NoLenTrait = TypeOperator("no_len", [])
SliceTrait = TypeOperator("slice", [])
NoSliceTrait = TypeOperator("no_slice", [])

def List(of_type):
    return Collection(Traits([ListTrait, LenTrait, SliceTrait]), Integer(), of_type)

def Set(of_type):
    return Collection(Traits([SetTrait, LenTrait, NoSliceTrait]), InvalidKey, of_type)

def Dict(key_type, value_type):
    return Collection(Traits([DictTrait, LenTrait, NoSliceTrait]), key_type, value_type)

def Str(rec=True):
    return Collection(Traits([StrTrait, LenTrait, SliceTrait]), Integer(), Str(rec=False) if rec else InvalidKey)

def Array(of_type, dim):
    return Collection(Traits([ArrayTrait, LenTrait, SliceTrait]), Integer(), Array(of_type, dim - 1) if dim > 1 else of_type)

def Generator(of_type):
    return Collection(Traits([GenerableTrait, NoLenTrait, NoSliceTrait]), InvalidKey, of_type)

def Tuple(of_types):
    return Collection(Traits([TupleTrait(of_types), LenTrait, SliceTrait]), Integer(), TypeVariable())


class Scalar(TypeOperator):
    def __init__(self, types=None):
        if not isinstance(types, list):
            dtype = types
            if dtype == 'float':
                types = [    FloatTrait, TypeVariable(), TypeVariable()]
            elif dtype == 'int':
                types = [TypeVariable(),   IntegerTrait, TypeVariable()]
            elif dtype == 'bool':
                types = [TypeVariable(), TypeVariable(),      BoolTrait]
            else:
                assert dtype is None
                types = [TypeVariable(), TypeVariable(), TypeVariable()]
        super(Scalar, self).__init__('scalar', types)

    def __str__(self):
        if isinstance(prune(self.types[0]), TypeOperator):
            return 'float'
        if isinstance(prune(self.types[1]), TypeOperator):
            return 'int'
        if isinstance(prune(self.types[2]), TypeOperator):
            return 'bool'
        return 'scalar {}'.format(self.types[0].name)

def Float():
    return Collection(Traits([ArrayTrait, NoLenTrait, NoSliceTrait]), InvalidKey, Scalar('float'))

def Integer():
    return Collection(Traits([ArrayTrait, NoLenTrait, NoSliceTrait]), InvalidKey, Scalar('int'))

def Bool():
    return Collection(Traits([ArrayTrait, NoLenTrait, NoSliceTrait]), InvalidKey, Scalar('bool'))

def DType():
    return Collection(Traits([ArrayTrait, NoLenTrait, NoSliceTrait]), InvalidKey, Scalar())

def Function(from_types, to_type):
    """A binary type constructor which builds function types"""
    return TypeOperator('fun', list(from_types) + [to_type])

def OptionType(of_type):
    return TypeOperator("option", [of_type])

def Traits(of_types):
    return TypeOperator("traits", of_types)

ExceptionType = TypeOperator("exception", [])

# Basic types are constructed with a nullary type constructor
IntegerTrait = TypeOperator("int", [])  # Basic integer
FloatTrait = TypeOperator("float", [])  # Double precision float
BoolTrait = TypeOperator("bool", [])  # Basic bool
InvalidKey = TypeOperator("invalid-key", [])  # invalid key - for non-indexable collection
NoneType = TypeOperator("none", [])
InvalidType = TypeOperator("invalid-type", [])
Slice = TypeOperator("slice", [])  # slice

def is_none(t):
    pt = prune(t)
    return isinstance(pt, TypeOperator) and pt.name == "none"

def is_option_type(t):
    pt = prune(t)
    return isinstance(pt, TypeOperator) and pt.name == "option"

def is_tuple_type(t):
    pt = prune(t)
    if isinstance(pt, TypeOperator) and pt.name == "collection":
        st = prune(pt.types[0])
        if isinstance(st, TypeOperator) and st.name == "traits":
            tt = prune(st.types[0])
            return isinstance(tt, TypeOperator) and tt.name == "tuple"
    return False

class MultiType(object):
    """A binary type constructor which builds function types"""

    def __init__(self, types):
        self.types = types

    def __str__(self):
        return '(' + ' ; '.join(sorted(map(str, self.types))) + ')'

class MakeNumpyUnaryOp(object):
    types = []
    types.append(Function([Integer()], Integer()))
    types.append(Function([Float()], Float()))
    n = 4
    for i in range(n):
        types.append(Function([Array(Integer(), i)], Array(Integer(),i)))
        types.append(Function([Array(Float(), i)], Array(Float(),i)))
    instance = MultiType(types)

    def __call__(self):
        return MakeNumpyUnaryOp.instance

NumpyUnaryOp = MakeNumpyUnaryOp()

class MakeNumpyBinOp(object):
    types = []
    types.append(Function([Integer(), Integer()], Integer()))
    types.append(Function([Float(), Float()], Float()))
    types.append(Function([Integer(), Float()], Float()))
    types.append(Function([Float(), Integer()], Float()))
    n = 4
    for i in range(n):
        types.append(Function([Array(Integer(), i), Integer()], Array(Integer(),i)))
        types.append(Function([Array(Float(), i),   Float()],   Array(Float(),i)))
        types.append(Function([Array(Integer(), i), Float()],   Array(Float(),i)))
        types.append(Function([Array(Float(), i),   Integer()], Array(Float(),i)))

        types.append(Function([Integer(), Array(Integer(), i)], Array(Integer(),i)))
        types.append(Function([  Float(), Array(  Float(), i)], Array(  Float(),i)))
        types.append(Function([  Float(), Array(Integer(), i)], Array(  Float(),i)))
        types.append(Function([Integer(), Array(  Float(), i)], Array(  Float(),i)))

        for j in range(i + 1):
            types.append(Function([Array(Integer(),j), Array(Integer(), i)],
                                  Array(Integer(),i)))
            types.append(Function([Array(Float(),j),   Array(Float(), i)],
                                  Array(Float(),i)))
            types.append(Function([Array(Float(),j),   Array(Integer(), i)],
                                  Array(Float(),i)))
            types.append(Function([Array(Integer(),j), Array(Float(), i)],
                                  Array(Float(),i)))

            types.append(Function([Array(Integer(),i), Array(Integer(), j)],
                                  Array(Integer(),i)))
            types.append(Function([Array(Float(),i),   Array(Float(), j)],
                                  Array(Float(),i)))
            types.append(Function([Array(Float(),i),   Array(Integer(), j)],
                                  Array(Float(),i)))
            types.append(Function([Array(Integer(),i), Array(Float(), j)],
                                  Array(Float(),i)))


    instance = MultiType(types)

    def __call__(self):
        return MakeNumpyBinOp.instance

NumpyBinOp = MakeNumpyBinOp()

class MakeAddOp(object):
    instance = MultiType(list(NumpyBinOp.types))
    instance.types.append(Function([Str(), Str()], Str()))
    tv = TypeVariable()
    instance.types.append(Function([List(tv), List(tv)], List(tv)))
    for i in range(4):
        for j in range(4):
            ti = [TypeVariable() for _ in range(i)]
            tj = [TypeVariable() for _ in range(j)]
            instance.types.append(Function([Tuple(ti), Tuple(tj)], Tuple(ti + tj)))

    def __call__(self):
        return instance


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
            return Integer()
        elif isinstance(node.n, float):
            return Float()
        else:
            raise NotImplementedError
    elif isinstance(node, gast.Str):
        return Str()
    elif isinstance(node, gast.Compare):
        left_type = analyse(node.left, env, non_generic)
        comparators_type = [analyse(comparator, env, non_generic)
                            for comparator in node.comparators]
        ops_type = [analyse(op, env, non_generic)
                    for op in node.ops]
        prev_type = left_type
        for op_type, comparator_type in zip(ops_type, comparators_type):
            unify(Function([prev_type, comparator_type], TypeVariable()),
                  op_type)
        return Bool()
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
        test_type = analyse(node.test, env, non_generic)
        unify(Function([test_type], Bool()), builtins['bool'])
        body_type = analyse(node.body, env, non_generic)
        orelse_type = analyse(node.orelse, env, non_generic)
        return merge_unify(body_type, orelse_type)
    elif isinstance(node, gast.UnaryOp):
        operand_type = analyse(node.operand, env, non_generic)
        op_type = analyse(node.op, env, non_generic)
        result_type = TypeVariable()
        unify(Function([operand_type], result_type), op_type)
        return result_type
    elif isinstance(node, gast.BinOp):
        left_type = analyse(node.left, env, non_generic)
        op_type = analyse(node.op, env, non_generic)
        right_type = analyse(node.right, env, non_generic)
        result_type = TypeVariable()
        unify(Function([left_type, right_type], result_type), op_type)
        return result_type
    elif isinstance(node, gast.Pow):
        return NumpyBinOp()
    elif isinstance(node, gast.Sub):
        return NumpyBinOp()
    elif isinstance(node, (gast.USub, gast.UAdd)):
        return NumpyUnaryOp()
    elif isinstance(node, (gast.Eq, gast.NotEq, gast.Lt, gast.LtE, gast.Gt,
                           gast.GtE, gast.Is, gast.IsNot)):
        var = TypeVariable()
        return Function([var, var], Bool())
    elif isinstance(node, (gast.In, gast.NotIn)):
        var = TypeVariable()
        return Function([var, Collection(TypeVariable(), TypeVariable(), var)], Bool())
    elif isinstance(node, gast.Add):
        return MakeAddOp.instance
    elif isinstance(node, gast.Mult):
        return MakeNumpyBinOp.instance
    elif isinstance(node, gast.Div):
        return MakeNumpyBinOp.instance
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
    elif isinstance(node, gast.Slice):
        if node.lower:
            lower_type = analyse(node.lower, env, non_generic)
            unify(lower_type, Integer())
        else:
            lower_type = Integer()
        if node.upper:
            upper_type = analyse(node.upper, env, non_generic)
            unify(upper_type, Integer())
        else:
            upper_type = Integer()
        if node.step:
            step_type = analyse(node.step, env, non_generic)
            unify(step_type, Integer())
        else:
            step_type = Integer()
        return Slice
    elif isinstance(node, gast.ExtSlice):
        return [analyse(dim, env, non_generic) for dim in node.dims]
    elif isinstance(node, gast.NameConstant):
        if node.value is None:
            return env['None']
    elif isinstance(node, gast.Subscript):
        new_type = TypeVariable()
        value_type = analyse(node.value, env, non_generic)
        slice_type = analyse(node.slice, env, non_generic)
        if isinstance(node.slice, gast.Index):
            st = prune(slice_type)
            if is_tuple_type(slice_type):
                nbindex = len(prune(prune(st.types[0]).types[0]).types)
                dtype = TypeVariable()
                unify(Array(dtype, nbindex) , value_type)
                new_type = dtype
            elif isinstance(node.slice.value, gast.Num):
                vt = prune(value_type)
                if is_tuple_type(vt):
                    unify(prune(prune(vt.types[0]).types[0]).types[node.slice.value.n], new_type)
                else:
                    unify(Collection(Traits([TypeVariable(), TypeVariable(), TypeVariable()]), slice_type, new_type), value_type)
            else:
                unify(Collection(Traits([TypeVariable(), TypeVariable(), TypeVariable()]), slice_type, new_type), value_type)
        elif isinstance(node.slice, gast.Slice):
            unify(Collection(Traits([TypeVariable(), TypeVariable(), SliceTrait]), Integer(), TypeVariable()), value_type)
            new_type = value_type
        elif isinstance(node.slice, gast.ExtSlice):
            nbslice = len(node.slice.dims)
            dtype = TypeVariable()
            unify(Array(dtype, nbslice), value_type)
            new_type = Array(dtype, sum(1 for s in slice_type if s is Slice))
        else:
            raise NotImplementedError()
        return new_type
    elif isinstance(node, gast.Attribute):
        value_type = analyse(node.value, env, non_generic)
        if isinstance(value_type, dict):  # that's an import
            return value_type[node.attr]
        elif node.attr in Attrs:
            result_type = TypeVariable()
            ft = Function([value_type], result_type)
            unify(ft, fresh(Attrs[node.attr], non_generic))
            return result_type
        raise NotImplementedError("Unknown attribute: %s" % node.attr)
    # stmt
    elif isinstance(node, gast.Import):
        for alias in node.names:
            if alias.name not in Modules:
                raise NotImplementedError("unknown module: %s " % alias.name)
            if alias.asname is None:
                target = alias.name
            else:
                target = alias.asname
            env[target] = clone(Modules[alias.name])
        return env
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
            env[target] = clone(Modules[node.module][alias.name])
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
            ret_type = merge_unify(env['@ret'], ret_type)
        env['@ret'] = ret_type
        return env
    elif isinstance(node, gast.Yield):
        assert env['@gen']
        assert node.value is not None

        ret_type = analyse(node.value, env, non_generic)

        if '@ret' in env:
            unify(env['@ret'], ret_type)
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
        unify(Function([test_type], Bool()), builtins['bool'])

        body_env = env.copy()
        body_non_generic = non_generic.copy()
        analyse_body(node.body, body_env, body_non_generic)

        orelse_env = env.copy()
        orelse_non_generic = non_generic.copy()
        analyse_body(node.orelse, orelse_env, orelse_non_generic)

        for var in body_env:
            if var not in env:
                if var in orelse_env:
                    new_type = merge_unify(body_env[var], orelse_env[var])
                else:
                    new_type = body_env[var]
                env[var] = new_type

        for var in orelse_env:
            if var not in env:
                # may not be unified by the prev loop if a del occured
                if var in body_env:
                    new_type = merge_unify(orelse_env[var], body_env[var])
                else:
                    new_type = orelse_env[var]
                env[var] = new_type

        return env
    elif isinstance(node, gast.While):
        test_type = analyse(node.test, env, non_generic)
        unify(Function([test_type], Bool()), builtins['bool'])

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
    elif isinstance(node, gast.Assert):
        if node.msg:
            analyse(node.msg, env, non_generic)
        analyse(node.test, env, non_generic)
        return env
    elif isinstance(node, gast.UnaryOp):
        operand_type = analyse(node.operand, env, non_generic)
        return_type = TypeVariable()
        op_type = analyse(node.op, env, non_generic)
        unify(Function([operand_type], return_type), op_type)
        return return_type
    elif isinstance(node, gast.Invert):
        return MultiType([Function([Bool()], Integer()),
                          Function([Integer()], Integer())])
    elif isinstance(node, gast.Not):
        return builtins['bool']
    elif isinstance(node, gast.BoolOp):
        op_type = analyse(node.op, env, non_generic)
        init_type = analyse(node.values[0], env, non_generic)
        for n in node.values[1:]:
            unify(Function([init_type, analyse(n, env, non_generic)], init_type), op_type)
        return init_type
    elif isinstance(node, (gast.And, gast.Or)):
        x_type = TypeVariable()
        return Function([x_type, x_type], x_type)

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
        if isinstance(env[name], MultiType):
            return clone(env[name])
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
        elif isinstance(p, dict):
            return p  # module
        elif isinstance(p, Collection):
            return Collection(*[freshrec(x) for x in p.types])
        elif isinstance(p, Scalar):
            return Scalar([freshrec(x) for x in p.types])
        elif isinstance(p, TypeOperator):
            return TypeOperator(p.name, [freshrec(x) for x in p.types])
        elif isinstance(p, MultiType):
            return MultiType([freshrec(x) for x in p.types])
        else:
            assert False, "missing freshrec case {}".format(type(p))

    return freshrec(t)

def clone(t):
    if isinstance(t, MultiType):
        return MultiType([clone(tp) for tp in t.types])
    else:
        return fresh(t, {})

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
            raise InferenceError("Type mismatch: {0} != {1}".format(type(a), type(b)))
        else:
            if a.name != b.name:
                raise InferenceError("Type mismatch: {0} != {1}".format(a.name, b.name))
        try:
            for p, q in zip(a.types, b.types):
                unify(p, q)
        except InferenceError:
            raise
    elif isinstance(a, MultiType) and isinstance(b, MultiType):
        if len(a.types) != len(b.types):
            raise InferenceError("Type mismatch: {0} != {1}".format(type(a), type(b)))
        for p, q in zip(a.types, b.types):
            unify(p, q)
    elif isinstance(b, MultiType):
        return unify(b, a)
    elif isinstance(a, MultiType):
        types = []
        for t in a.types:
            try:
                t_clone = fresh(t, {})
                b_clone = fresh(b, {})
                unify(t_clone, b_clone)
                types.append(t)
            except InferenceError as e:
                pass
        if types:
            if len(types) == 1:
                a.instance = types[0]
                unify(a.instance, b)
            else:
                # too many overloads are found, so extract as many information as we can, and leave the remaining
                # over-approximated
                def try_unify(t, ts):
                    if isinstance(t, TypeVariable):
                        return
                    if any(isinstance(tp, TypeVariable) for tp in ts):
                        return
                    for i, tt in enumerate(t.types):
                        its = [prune(tp.types[i]) for tp in ts]
                        if any(isinstance(it, TypeVariable) for it in its):
                            continue
                        it0 = its[0]
                        it0ntypes = len(it0.types)
                        if all(((it.name == it0.name) and (len(it.types) == it0ntypes)) for it in its):
                            ntypes = [TypeVariable() for _ in range(it0ntypes)]
                            new_tt = TypeOperator(it0.name, ntypes)
                            new_tt.__class__ = it0.__class__
                            unify(tt, new_tt)
                            try_unify(prune(tt), [prune(it) for it in its])
                try_unify(b, types)
        else:
            #print("while unifying:")
            #print("-", str(a))
            #print("-", str(b))
            raise InferenceError("Not unified {} and {}, no overload found".format(type(a), type(b)))
    else:
        raise RuntimeError("Not unified {} and {}".format(type(a), type(b)))

def merge_unify(t1, t2):
    p1 = prune(t1)
    p2 = prune(t2)
    if is_none(p1) and is_none(p2):
        return p1
    if is_none(p1):
        if is_option_type(p2):
            return p2
        else:
            return OptionType(p2)
    if is_none(p2):
        return merge_unify(p2, p1)
    if is_option_type(p1) and is_option_type(p2):
        unify(p1.types[0], p2.types[0])
        return p1
    if is_option_type(p1):
        unify(p1.types[0], p2)
        return p1
    if is_option_type(p2):
        return merge_unify(p2, p1)
    unify(p1, p2)
    return p1


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
    return MultiType(candidates)

ZipFunction = make_zip_function(4)



def make_map_function(n):
    candidates = []
    for arity in range(1, n):
        f_arg_types0 = [TypeVariable() for _ in range(arity)]
        f_ret_type = TypeVariable()
        arg_types0 = [Collection(TypeVariable(), TypeVariable(), f_arg_type) for f_arg_type in f_arg_types0]
        candidates.append(Function([Function(f_arg_types0, f_ret_type)] + arg_types0, List(f_ret_type)))

        arg_types1 = [Collection(TypeVariable(), TypeVariable(), TypeVariable()) for _ in range(arity)]
        candidates.append(Function([NoneType] + arg_types1, List(Tuple(arg_types1)) if arity > 1 else arg_types1[0]))
    return MultiType(candidates)

MapFunction = make_map_function(3)


def make_partial_function(n):
    candidates = []
    for arity in range(n):
        for nb_placeholders in range(arity):
            f_args = [TypeVariable() for _ in range(arity)]
            f_res = TypeVariable()
            candidates.append(Function([Function(f_args, f_res)] + f_args[:nb_placeholders],
                                       Function(f_args[nb_placeholders:], f_res)))
    return MultiType(candidates)

PartialFunction = make_partial_function(4)

def make_numpy_array(n):
    candidates = []

    array_type = Array(TypeVariable(), 0)
    candidates.append(Function([array_type], array_type))
    for i in range(1, n):
        dtype = DType()
        candidates.append(Function([reduce(lambda x, y: List(x), range(i), dtype)], Array(dtype, i)))

    return MultiType(candidates)

ArrayFunction = make_numpy_array(4)

def make_numpy_ones(n):
    candidates = []
    # with an integer as shape
    candidates.append(Function([Integer()], Array(Float(), 1)))
    dtype_from = TypeVariable()
    dtype = TypeVariable()
    candidates.append(Function([Integer(), Function([dtype_from], dtype)], Array(dtype, 1)))

    for i in range(1, n):
        candidates.append(Function([Tuple([Integer() for _ in range(i)])], Array(Float(), i)))

        dtype_from = TypeVariable()
        dtype = TypeVariable()
        candidates.append(Function([Tuple([Integer() for _ in range(i)]), Function([dtype_from], dtype)], Array(dtype, i)))

    return MultiType(candidates)

OnesFunction = make_numpy_ones(4)

def make_numpy_sum(n):
    candidates = []
    for i in range(1, n):
        dtype = DType()
        candidates.append(Function([Array(dtype, i)], dtype))

    return MultiType(candidates)

SumFunction = make_numpy_sum(4)

def make_list_append():
    tv = TypeVariable()
    return Function([List(tv)], Function([tv], NoneType))

def make_array_shape(n):
    candidates = []
    for i in  range(1, n):
        candidates.append(Function([Array(DType(), i)], Tuple([Integer() for _ in range(i)])))
    return MultiType(candidates)

def make_array_dtype(n):
    candidates = []
    for i in  range(1, n):
        dtype = DType()
        candidates.append(Function([Array(dtype, i)], Function([TypeVariable()], dtype)))
    return MultiType(candidates)

def make_array_reshape(n):
    candidates = []
    for i in  range(1, n):
        for j in  range(1, n):
            dtype = DType()
            candidates.append(Function([Array(dtype, i)], Function([Tuple([Integer() for _ in range(j)])], Array(dtype, j))))
    return MultiType(candidates)

def make_numpy_arange():
    candidates = []
    dtype = DType()
    candidates.append(Function([dtype], Array(dtype, 1)))
    dtype = DType()
    candidates.append(Function([dtype, dtype], Array(dtype, 1)))
    dtype = DType()
    candidates.append(Function([dtype, dtype, dtype], Array(dtype, 1)))
    dtype0 = DType()
    dtype1 = DType()
    candidates.append(Function([dtype0, dtype0, dtype0, Function([TypeVariable()], dtype1)], Array(dtype1, 1)))
    return MultiType(candidates)

ArangeFunction = make_numpy_arange()

def make_list():
    value_type = Collection(TypeVariable(), TypeVariable(), TypeVariable())
    return MultiType([
        Function([Collection(Traits([TypeVariable(), TypeVariable(), TypeVariable()]), TypeVariable(), value_type)], List(value_type)),
        Function([], List(TypeVariable())),
    ])

_Builtins = {
    'id': Function([TypeVariable()], Integer()),
    'len': Function([Collection(Traits([TypeVariable(), LenTrait, TypeVariable()]), TypeVariable(), TypeVariable())], Integer()),
    'zip': ZipFunction,
    'map': MapFunction,
    'None': NoneType,
    'print': MultiType([Function([TypeVariable() for _ in range(i)], NoneType) for i in range(5)]),
    'int': Function([TypeVariable()], Integer()),
    'float': Function([TypeVariable()], Float()),
    'bool': MultiType([
        Function([Collection(Traits([TypeVariable(), LenTrait, TypeVariable()]), TypeVariable(), TypeVariable())], Bool()),
        Function([Collection(Traits([ArrayTrait, NoLenTrait, TypeVariable()]), TypeVariable(), TypeVariable())], Bool()),
    ]),
    'xrange': MultiType([
        Function([Integer()], Generator(Integer())),
        Function([Integer(), Integer()], Generator(Integer())),
        Function([Integer(), Integer(), Integer()], Generator(Integer())),
    ]),
    'range': MultiType([
        Function([Integer()], List(Integer())),
        Function([Integer(), Integer()], List(Integer())),
        Function([Integer(), Integer(), Integer()], List(Integer())),
    ]),
    'list': make_list(),
    'True': Bool(),
    'False': Bool(),
}

_Attrs = {
    'append': make_list_append(),
    'shape': make_array_shape(4),
    'dtype': make_array_dtype(4),
    'reshape': make_array_reshape(4),
}

_Modules = {
    'functools': {
        'partial': PartialFunction,
    },
    'math': {
        'cos': Function([Float()], Float()),
        'sin': Function([Float()], Float()),
    },
    'numpy': {
        'array': ArrayFunction ,
        'arange': ArangeFunction ,
        'ones': OnesFunction ,
        'zeros': OnesFunction ,
        'sum': SumFunction ,
    },
}

_Modules['__builtin__'] = _Builtins.copy()

builtins, Attrs, Modules = _Builtins, _Attrs, _Modules
def reset():
    # FIMXE: this prevents some side effect on the tables, better find where it comes from
    TypeVariable.reset()

reset()

class TestTypeInference(unittest.TestCase):

    def check(self, code, ref):
        reset()
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

    def test_return_none(self):
        self.check('def f(): return ',
                   'f: (fun none)')

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
                   "f: (fun (0d+ array 'a) -> (0d+ array 'b) -> (tuple (0d+ array 'c) -> (0d+ array 'd)))")

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
        self.check('def f(x): return [a for a, b in x]',
                   "f: (fun (collection 'a -> (tuple 'b -> 'c)) -> (list 'b))")

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
                   "f: (fun (collection (traits 'a -> len -> 'b) -> 'c -> 'd) -> (tuple int -> int))"
                   )

    def test_zip(self):
        self.check('def f(x, y): return zip(x, y)',
                   "f: (fun (collection 'a -> 'b) -> (collection 'c -> 'd) -> (list (tuple 'b -> 'd)))")

    def test_map_none(self):
        self.check('def f(x): return map(None, x)',
                   "f: (fun (collection 'a -> 'b) -> (collection 'a -> 'b))")

    def test_map_none_again(self):
        self.check('def f(x): return map(None, x, x)',
                   "f: (fun (collection 'a -> 'b) -> (list (tuple (collection 'a -> 'b) -> (collection 'a -> 'b))))")

    def test_map_id(self):
        self.check('def f(x): return map(id, x)',
                   "f: (fun (collection 'a -> 'b) -> (list int))")

    def test_union_type(self):
        self.check('def f(x, y): return map(x, y)',
                   "f: (fun 'a -> (collection 'b -> 'c) -> (collection 'd -> 'e))")

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
                   def f(x, y, z): return [x, y, z]
                   def g(x): return partial(f, x, 1)
                   ''',
                   '''
                   f: (fun 'a -> 'a -> 'a -> (list 'a))
                   g: (fun int -> (fun int -> (list int)))
                   ''')

    def test_generatorexp(self):
        self.check('def f(x, y): return ((z, y) for z in x)',
                   "f: (fun (collection 'a -> 'b) -> 'c -> (gen (tuple 'b -> 'c)))"
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

    def test_list_append(self):
        self.check('def f(x, y): x.append(y)',
                   "f: (fun (list 'a) -> 'a -> none)")

    def test_numpy_ones(self):
        self.check("""
                   def f(x):
                       import numpy as np
                       return np.ones((x,))
                   """,
                   "f: (fun int -> (1d array float))")

    def test_numpy_ones_dtype(self):
        self.check("""
                   def f(x):
                       import numpy as np
                       return np.ones((x, x), int)
                   """,
                   "f: (fun int -> (2d array int))")

    def test_assert(self):
        self.check("""
                   def f(x):
                       assert(x, x)
                   """,
                   "f: (fun 'a -> none)")

    def test_if_len(self):
        self.check('''
            def f(x):
                if x:
                    return len(x)
                else:
                    return 1
                ''',
                "f: (fun (collection (traits 'a -> len -> 'b) -> 'c -> 'd) -> int)")

    def test_multimap(self):
        self.check('''
            def f(x, y):
                return len(map(x, y))
                ''',
                # WARN: over approximation
                "f: (fun 'a -> (collection 'b -> 'c) -> int)")

    def test_map_from_builtin(self):
        self.check('def f(x): from __builtin__ import map; return map(None, x)',
                   "f: (fun (collection 'a -> 'b) -> (collection 'a -> 'b))")

    def test_if_none(self):
        self.check('''
                   def f(x):
                       if 1: return x
                       else: return None
                   ''',
                   "f: (fun 'a -> (option 'a))"
                  )

    def test_subscript_slice(self):
        self.check('def f(x): x[0] = 1; return x[1:2]',
                   "f: (fun (collection (traits 'a -> 'b -> slice) -> int -> int) -> (collection (traits 'a -> 'b -> slice) -> int -> int))")

    def test_subscript_extslice(self):
        self.check('def f(x): return x[1:2,3]',
                   "f: (fun (2d+ array 'a) -> (1d+ array 'a))")

    def test_subscript_extslice_twice(self):
        self.check('''
                   import numpy as np
                   def f(x):
                    arr = np.ones((x,x,x))
                    return arr[1:2,3, 0:1][1:1, 2:-1]
                   ''',
                   "f: (fun int -> (2d array float))")


    def test_rosen(self):
        self.check('''
                   import numpy as np
                   def f(x):
                    t0 = 100 * (x[1:] - x[:-1] ** 2) ** 2
                    t1 = (1 - x[:-1]) ** 2
                    return np.sum(t0 + t1)
                   ''',
                   "f: (fun (1d+ array 'a) -> scalar 'b)")

    def test_add_to_none(self):
        code = '''
            def f(x): return None if 0 else 1
            def g(x): return f(x)
        '''
        self.check(code,
                   '''
                   f: (fun 'a -> (option int))
                   g: (fun 'b -> (option int))
                   ''')
        code += '''
            def h(x): return g(x) + 1
        '''
        with self.assertRaises(InferenceError):
            self.check(code, "any")

    def test_compare(self):
        self.check(
            """
                def f(x, l):
                    if 2 <= x < 6:
                        return x, x == 3
                    elif 2 > x >= 0:
                        return x, x is 5
                    elif x in l:
                        return x, x is not 6
                    elif x not in l:
                        return x, x is not 6
                    else:
                        return x, x != 4
            """,
            "f: (fun int -> (collection 'a -> int) -> (tuple int -> bool))")

    def test_unop(self):
        self.check("""
                   def f(x):
                       return ~x, -x, not x, +x
                   """,
                   "f: (fun int -> (tuple int -> scalar 'a -> bool -> scalar 'b))")

    def test_boolop(self):
        self.check("""
                   def f(x, y):
                       while x < 2 and x > 0:
                           x += 1
                       return (x and (x or 1) and y) or y
                   """,
                   "f: (fun int -> int -> int)")

    def test_numpy_array_0(self):
        self.check("""
                   def f():
                     from numpy import array
                     return array([[1],[1]])
                   """,
                   "f: (fun (2d array int))")

    def test_numpy_array_1(self):
        self.check("""
                   def f():
                     from numpy import array, ones
                     return array(ones(1))
                   """,
                   "f: (fun (1d array float))")

    def test_tuple_indexing(self):
        self.check('def f(x): a = (x, 1, 2) ; return a[0], a[2]',
                   "f: (fun 'a -> (tuple 'a -> int))")

    def test_collection_inferring(self):
        self.check('def f(x): return x[0]',
                   "f: (fun (collection int -> 'a) -> 'a)")

    def test_builtin_list(self):
        self.check('def f(x): return list([1]), list({"1"}), list()',
                   "f: (fun 'a -> (tuple (list int) -> (list str) -> (list 'b)))")




if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(
        description='type a .py program')
    parser.add_argument(
        'file', type=argparse.FileType(),
        help='path to input Python file')
    args = parser.parse_args()

    node = gast.parse(args.file.read())
    env = builtins.copy()
    types = analyse(node, env)
    new_env = {k: v for k, v in env.items()}

    out = []
    for key, value in sorted(new_env.items()):
        if key not in builtins:
            out.append('{}: {}\n'.format(key, value))
    print("\n".join(out))
