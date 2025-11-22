module InterfaceDispatch
using SumTypes
import SumTypes: isvariant
import Base: ==, PersistentDict

macro ignore(e...)
    return :()
end


# -------------------------------------------------------------------------------------
# Utilities
begin
    macro swap(e1, e2)
        _e1, _e2 = esc.((e1, e2))
        quote
            tmp = $_e1
            $_e1 = $_e2
            $_e2 = tmp
        end
    end

    on(f, g) = (args...) -> f(g.(args)...)
    const ⊚ = on

    macro guarded(expr)
        quote
            try
                $(esc(expr))
            catch e 
                println("caught: ", e)
            end
        end
    end

    # for the sumtypes
    insert(d :: PersistentDict, k, v) = PersistentDict(d, k => v)
    isvariant(x, t :: Tuple) = any(isvariant(x, v) for v in t)
end





# -------------------------------------------------------------------------------------
# Types
begin


    mutable struct TypeParam
        const name::String
    end
    t::TypeParam == w::TypeParam = (t === w)
    Base.show(io::IO, t::TypeParam) = print(io, "'$(t.name)")




    _extracttype(::Type{Type{T}}) where T = T
    typeparameters(t :: Type) = t.parameters
    typebase(t :: Type) = _extracttype(t.name.Typeofwrapper)
    

    const TypeParameterValue = Union{DataType,Int,String,Symbol}

    struct ParametrizedType
        base::Union{DataType,UnionAll,TypeParam}
        parameters::Vector{Union{TypeParameterValue, ParametrizedType,TypeParam}}
    end

    typeparameters(t :: ParametrizedType) = t.parameters
    typebase(t :: ParametrizedType) = t.base

    const ConcreteOrParametrizedType = Union{DataType,ParametrizedType}
    const TypeLike = Union{DataType, ParametrizedType, TypeParam}
    # Base.convert(::Type{TypeLike}, t::Type) = convert(DataType, T)

    Base.show(io::IO, t::ParametrizedType) = begin
        print(io, "<", t.base, ">")
        length(t.parameters) == 0 && return
        print(io, "{")
        join(io, t.parameters, ", ")
        print(io, "}")
    end


    (p1::ParametrizedType == p2::ParametrizedType) =
        ((==) ⊚ typebase)(p1, p2) &&
        ((==) ⊚ (length ∘ typeparameters))(p1, p2) &&
        all(t == w for (t, w) in zip(typeparameters(p1), typeparameters(p2)))

    parameterType(::Type{ParametrizedType}) = Union{TypeParameterValue, ParametrizedType, TypeParam}
    parametrizedType(base, params...) = ParametrizedType(base, collect(parameterType(ParametrizedType), params ))
    
    isparametric(thing) = thing isa TypeParam || thing isa ParametrizedType
    to_type(base, params...) = if isparametric(base) || any(isparametric(p) for p in params)
            return parametrizedType(base, params...)
        else
            return Core.apply_type(base, params...)
        end
end


# -------------------------------------------------------------------------------------
# Context
begin
    const TypeContext = PersistentDict{TypeParam, Union{TypeParameterValue, TypeLike}}
    const empty_context = TypeContext()
    Base.typeinfo_prefix(io :: IO, ::Type{TypeContext}) = sprint(print, "TypeContext"; context = io), false
end

# -------------------------------------------------------------------------------------
# InterfaceSignatures
begin
    struct InterfaceSignature
        callable :: Any 
        args :: Vector{TypeLike}
        retval :: TypeLike
    end

    interfacesig(callable, args...) = begin
        isempty(args) && throw("need at least a return value")
        retval = last(args)
        InterfaceSignature(callable, collect(TypeLike, args[1:end-1]), retval)
    end
end


# -------------------------------------------------------------------------------------
# Interfaces 
begin
    struct Interface 
        vars :: Vector{TypeParam}
        signatures :: Vector{InterfaceSignature}

        name :: String 
    end

    is_empty_interface(i :: Interface) = isempty(i.signatures)

end


# -------------------------------------------------------------------------------------
# IFunction
begin
    struct MethodSignature
        args :: Vector{TypeLike}
        restriction :: Interface 
    end
    MethodSignature(args, i) = MethodSignature(collect(TypeLike, args), i)
    Base.show(io :: IO, m :: MethodSignature) = begin
        print(io, "MSig: (")
        join(io, m.args, ", ")
        print(io, ")--", m.restriction.name)
    end


    struct MTableNode
        implementation :: Any
        methodsig :: MethodSignature
    end

    struct IFunction
        name :: String
        methodtable :: Vector{MTableNode}
    end

    IFunction(name :: String) = IFunction(name, MTableNode[])

    fetch_nodes(signature :: Vector{DataType}, table :: Vector{MTableNode}) = begin
        candidates = MTableNode[]
        for sig in table
            more_specific(signature, sig.methodsig) === none && continue
            if !isempty(candidates) && all(isvariant(more_specific(other.methodsig, sig.methodsig), :higher) for other in candidates)
                continue
            end

            if all(isvariant(more_specific(sig.methodsig, other.methodsig), :higher) for other in candidates)
                empty!(candidates)
            end
            push!(candidates, sig)
        end
        candidates
    end

    inject_node(signature :: MTableNode, table :: Vector{MTableNode}) = begin
        for i in eachindex(table)
            if isvariant(more_specific(signature.methodsig, table[i].methodsig), :equal)
                table[i] = signature
                return 
            end
        end
        push!(table, signature)
    end

    register_method(f :: IFunction, ms :: MethodSignature, impl :: Any) = begin
        node = MTableNode(impl, ms)
        inject_node(node, f.methodtable)
        f
    end
    # Prototype was in python, and I am too lazy to think up a more julian way
    # I'm sorry
    const Id = Ptr{Nothing}
    id(x) = Base.pointer_from_objref(x)


    function fetch_node_old(signature :: Vector{DataType}, table :: Vector{MTableNode}, visited = Dict{Id, Union{MTableNode, Nothing}}) :: Union{MTableNode, Nothing}
        candidate = nothing
        for node in table
            haskey(visited, id(node)) && return visited[id(node)]
            
            @cases more_specific(signature, node.methodsig) begin
                equal(_) => begin
                    visited[id(node)] = node
                    return node
                end
                higher(_) => begin
                    new_candidate = fetch_node(signature, node.children, visited)
                    if new_candidate === nothing
                        new_candidate = node 
                    end
                    if candidate !== nothing && new_candidate !== candidate
                        throw("Multiple candidates found.")
                    end
                    candidate = new_candidate
                end
                none => nothing
            end
        end

        for node in table
            visited[id(node)] = candidate
        end
        return candidate
    end


    inject_node_old(node :: MTableNode, table :: Vector{MTableNode}; parent = nothing) = begin
        was_injected_here = was_injected = false
        i = 1
        while i ≤ length(table)
            othernode = table[i]
            othernode === node && return nothing
            @cases more_specific(othernode.methodsig, node.methodsig) begin
                equal(_) => begin
                    node.children = othernode.children
                    println("swapping nodes: ", othernode.methodsig, " => ", node.methodsig)
                    table[i] = node 
                    return nothing
                end
                higher(_) => begin
                    push!(node.children, othernode)
                    if !was_injected_here
                        table[i] = node
                        was_injected = was_injected_here = true
                    else
                        deleteat!(table, i)
                        continue
                    end
                end
                none => if isvariant(more_specific(node.methodsig, othernode.methodsig), (:higher, :equal))
                    inject_node(node, othernode.children; parent = othernode)
                    was_injected = true
                end
            end
            i += 1
        end
        if !was_injected
            push!(table, node)
        end
    end

    function register_method_old(f :: IFunction, msig :: MethodSignature, callable :: Any) :: IFunction
        node = MTableNode(callable, msig, MTableNode[])
        nargs = length(msig.args)
        mtable = get!(f.methodtable, nargs) do; MTableNode[] end
        inject_node(node, mtable)
        f
    end
    function (f :: IFunction)(args...)
        _typeof(x) = x isa DataType ? Type{x} : typeof(x)
        argtypes = [_typeof(a) for a in args]

        nodes = fetch_nodes(argtypes, f.methodtable)
        isempty(nodes) && throw("No methods found for signature $(argtypes)")
        length(nodes) > 1 && throw("Found competing candidates for function $(f.name) with signature $(argtypes)")
        return nodes[1].implementation(args...)

    end

    function Base.show(io :: IO, f :: IFunction) 
        print(io, "IFun<", f.name, '(', length(f.methodtable), " methods)>")
    end

    function print_method_hierarchy_old(f :: IFunction, i :: Int)
        mtable = get(f.methodtable, i, MTableNode[])
        labels = Dict{Id, Int}()
        todo = copy(mtable)
        curr_id = 0
        for t :: MTableNode in todo
            t_id = get!(labels, id(t)) do; curr_id += 1 end 
            # println("($t_id): ", t.methodsig.args, " -- ", t.methodsig.restriction.name)
            println("($t_id): ", t.methodsig)
            for c in t.children
                c_id = get!(labels, id(c)) do 
                    push!(todo, c)
                    curr_id += 1
                end
                println(" - ", c_id)
            end
        end
    end
end

# -------------------------------------------------------------------------------------
# infer_returntype
begin
    function infer_returntype(f :: Any, argtypes :: Vector{DataType}) :: Union{Nothing, DataType}
        t = Base.infer_return_type(f, argtypes)
        # t == Union{} means no method found
        return t === Union{}  ? nothing : t 
    end

    function  infer_returntype(f :: IFunction, argtypes :: Vector{DataType}) :: Union{Nothing, DataType}
        nodes = fetch_nodes( argtypes, f.methodtable)
        length(nodes) != 1 && return nothing 
        
        inferred = Base.infer_return_type(nodes[1].implementation, argtypes)
        return inferred === Union{} ? nothing : inferred
    end
end

# -------------------------------------------------------------------------------------
# apply_context
begin
    @sum_type ApplicationResult begin
        applicationresolved(::TypeContext)
        applicationincomplete
        applicationfailed
    end
    
    # this is basically the same as regular `nothing`, but we cannot use 
    # nothing itself as it is a valid parameter for parametric types.
    # we thus invent our own version of it, to differentiate the cases
    # "there is a parameter and it is nothing" and "there is no parameter"
    struct NoValue end 
    const novalue = NoValue()

    """
    essentially just `apply_context.(itr, context)`, but if any of the individual applications fail
    to return a ConcreteType, return `nothing` instead of failing.
    always return a `Vector{ConcreteType}` or `nothing`
    """
    function reduce_application(itr, context :: TypeContext) :: Union{Vector{TypeParameterValue}, NoValue}
        res = Vector{TypeParameterValue}(undef, length(itr))
        for (i, el) in enumerate(itr)
            t = apply_context(el, context)
            t === novalue && return novalue 
            res[i] = t 
        end
        return res 
    end
            
    apply_context(:: NoValue, context) = novalue
    apply_context(t :: TypeParameterValue, context :: TypeContext) = t
    apply_context(v :: TypeParam, context :: TypeContext) :: Union{TypeParameterValue, NoValue} =  
        if haskey(context, v) && context[v] isa TypeParameterValue
            context[v]
        else
            novalue
        end

    apply_context(t :: ParametrizedType, context :: TypeContext) :: Union{DataType, NoValue} = begin
        new_base = if t.base isa TypeParam 
            haskey(context, t.base) || return novalue
            context[t.base]
        else
            t.base
        end
        new_params = reduce_application(t.parameters, context)
        new_params === novalue && return novalue
        return Core.apply_type(new_base, new_params...)
    end

    function apply_context(s :: InterfaceSignature, context :: TypeContext) :: ApplicationResult

        concrete_args = reduce_application(s.args, context)
        concrete_args === novalue && return applicationincomplete

        inferred = infer_returntype(s.callable, collect(DataType, concrete_args))
        inferred === nothing && return applicationfailed

        new_context = match_specificity(inferred, s.retval, context)
        return new_context === nothing ? applicationfailed : applicationresolved(new_context)
    end

    function apply_context(i :: Interface, context :: TypeContext) :: ApplicationResult

        done = 0
        sigs_to_check = copy(i.signatures)
        curr_context = context

        @label restart_algorithm

        original_context = curr_context

        for i in (done + 1) : length(sigs_to_check)

            @cases apply_context(sigs_to_check[i], curr_context) begin
                applicationfailed =>  return applicationfailed
                applicationincomplete => continue 
                applicationresolved(new_context) => begin
                   curr_context = new_context 
                   done += 1 
                    @swap sigs_to_check[done] sigs_to_check[i]
                end 
            end
        end

        if done < length(sigs_to_check)
            if !(original_context === curr_context)
                @goto restart_algorithm
            else
                return applicationincomplete
            end
        else
            return applicationresolved(curr_context)
        end

    end

end

# -------------------------------------------------------------------------------------
# merge_interfaces
function merge_interfaces(
        i1 :: Interface,
        i2 :: Interface,
        context :: TypeContext = empty_context,
        new_name :: String = "<merge $(i1.name), $(i2.name)>",
    ) :: Interface
    #= TODO: this
        This would be easier if I had made the apply_context methods in a way that when the result is a 
        applicationincomplete, the variant carries the new, partially applied object. 
        Should I instead make a new apply_partial_context function?
        
        Also, if context mapps a Variable T' from any of the interfaces to something like Foo{A', B'},
        then we need to add both A', B' to the varlist, and replace all occurrences of T' in i1, i2 
        with Foo{A', B'}

    =#

    #
    curr_context = context
    new_sigs = InterfaceSignature[]
    for sig in i1.signatures
        new_sig = apply_context_partial(sig, curr_context)

    end


end

# -------------------------------------------------------------------------------------
# more_specific
begin
    @sum_type Specificity begin
        higher(::TypeContext)
        equal(::TypeContext)
        none
    end
    
    """
    `more_specific(thing1, thing2, context = empty_context_parametric)`
    Signifies whether the first argument is a more specific definition than the second.
    It can be more specific, equally specific, less specific or incompatible.
    the last two (less specific and incompatible) are combined into the `none` value, since
    they typically are handled identically.

    The `context` map helps to keep a "memory" of what happened, and what definitions have been seen.
    For example, if at one point we ask (Int more_specific than 'T?), the answer is yes.
    If we later ask (String more_specific than 'T?), the answer would also be "yes", but since the 
    context has captured that 'T => Int, we cannot have 'T => String now, and realize that the current 
    comparison should fail.
    """
    more_specific(a, b) = more_specific(a, b, empty_context)


    "shallow wrapper around `more_specific`, that just returns `nothing` in case of specificity `none`, and the wrapped context otherwise"
    function match_specificity(args...) 
        @cases more_specific(args...) begin
            none => nothing 
            [higher, equal](context) => context
        end
    end


    """
    Combines to specificities into one, for the purpose of reduction.
    `none` beats all else, since when in an iterator one element is not compatible whit its correspondent, 
        then the entire iterator is not compatible 

    `equal` acts as the neutral element, since when all comparisons have been neutral and the next is higher/equal/none,
    then the current state of the comparison should be regarded higher/equal/none 

    | current(down)\next(right) | higher | equal  | none |
    |---------------------------|--------|--------|------|
    | higher                    | higher | higher | none |
    | equal                     | higher | equal  | none |
    | none                      | none   | none   | none |

    """
    merge_specificity(current :: Specificity, next :: Specificity) ::Specificity =
        @cases current begin
            equal(_) => next 
            none => none
            higher(_) => @cases next begin
                [higher, equal](new_context) => higher(new_context)
                none => none
            end
        end
    merge_specificity(current :: Specificity, a, b) :: Specificity =
        @cases current begin
            none => return none
            [higher, equal](new_context) => return merge_specificity(current, more_specific(a, b, new_context))
        end


    function reduce_over_specificity(itr1, itr2, context :: TypeContext) :: Specificity
        length(itr1) == length(itr2) || return none
        specificity = equal(context)
        # println("reduce_init", (itr1, itr2))
        for (el1, el2) in zip(itr1, itr2)
            # @show specificity el1 el2
            specificity = merge_specificity(specificity, el1, el2)
            # @show specificity
            specificity == none && return none
        end
        # println()
        return specificity
    end
    # ---------------Concrete and Parametric Types and TypeVars --------------------------------------------------------

    more_specific(t1 :: DataType, t2 :: DataType, context :: TypeContext) = 
        t1 == t2    ? equal(context) :
        t1 <: t2    ? higher(context) :
                      none
    more_specific(t1 :: Any, t2 :: Any, context :: TypeContext) :: Specificity = 
        t1 == t2 ? equal(context) : none

    more_specific(var :: TypeParam, other :: TypeParam, context :: TypeContext) :: Specificity = 
        if haskey(context, other)
            context[other] == var ? equal(context) : none
        elseif any(v === var for v in values(context)) 
            higher(insert(context, other, var))
        else
            equal(insert(context, other, var))
        end
        # other === var                           ?   equal(context) :
        # haskey(context, other)                  ?   more_specific(var, context[other], context) : 
        # any(v === var for v in values(context)) ?   higher(insert(context, other, var)) :
        #                                             equal(insert(context, other, var))
        # the last check in this list is nessecary because Tuple{T, T} is more specific than Tuple{X, Y}


    more_specific(:: TypeParam, :: Any, context :: TypeContext) :: Specificity = none
    more_specific(t1 :: ParametrizedType, t2 :: TypeParameterValue, context ::TypeContext ) :: Specificity = none

    function more_specific(t1 :: ParametrizedType, t2 :: ParametrizedType, context :: TypeContext) :: Specificity 
        specificity = reduce_over_specificity(t1.parameters, t2.parameters, context)
        return merge_specificity(specificity, t1.base, t2.base)
    end
    
    more_specific(x :: Any, var :: TypeParam, context :: TypeContext) :: Specificity = 
        if haskey(context, var) 
            res = more_specific(x, context[var], context)
            @cases  res begin
                equal(new_context) => higher(new_context)
                _ => res
            end
        else
            higher(insert(context, var, x))
        end

    function more_specific(t :: DataType, t2 :: ParametrizedType, context :: TypeContext) :: Specificity
        specificity = reduce_over_specificity(t.parameters, t2.parameters, context)
        return merge_specificity(specificity, typebase(t), t2.base)
    end

    # ---------------InterfaceSignature-----------------------------------------------------------
    function more_specific(s1 :: InterfaceSignature, s2 :: InterfaceSignature, context :: TypeContext) :: Specificity
        s1.callable === s2.callable || return none
        specificity = reduce_over_specificity(s1.args, s2.args, context)
        return merge_specificity(specificity, s1.retval, s2.retval)
    end

    # ---------------Interfaces ------------------------------------------------------
    function more_specific(i1 :: Interface, i2 :: Interface, context :: TypeContext) :: Specificity
        
        specificity_higher = false

        done = 0
        sigs_to_check = copy(i2.signatures)
        curr_context = context

        @label restart_algorithm

        original_context = curr_context

        for i in (done + 1) : length(sigs_to_check)
            other_sig = sigs_to_check[i]
            best_match :: Specificity = none

            # for every sig in the other interface, look for a matching sig in this interface
            for this_sig in i1.signatures
                comparison = more_specific(this_sig, other_sig, curr_context)
                @cases  comparison begin
                    [higher, equal](new_context) => begin
                        curr_context = new_context
                        best_match = comparison
                        done += 1
                        @swap sigs_to_check[done] sigs_to_check[i]
                    end
                    none => nothing
                end
            end
            if isvariant(best_match, :higher) 
                specificity_higher = true
                break
            end

            if best_match == none
                # the signature does not appear in the left interface
                # this is ok if the relevant TypeParams are all mapped to 
                # concrete types, since we can then check if the signature holds statically
                applied = apply_context(other_sig, curr_context)
                @cases applied begin
                    applicationresolved(new_context) => begin
                        curr_context = new_context 
                        specificity_higher = true
                        done += 1
                        @swap sigs_to_check[done] sigs_to_check[i]
                    end
                    applicationfailed => return none
                    applicationincomplete => nothing
                end
            end
        end

        if done < length(sigs_to_check)
            # if not everything could be resolved, check if we found new information during processing
            # if yes, retry the incomplete ones with the new information. If no, we could not match everything
            if curr_context !== original_context
                @goto restart_algorithm
            else
                return none
            end
        end
        
        # if there is an element in this interface for which there is no correspondent in the other interface,
        # then we are more specific
        specificity_higher = specificity_higher || any(all(more_specific(other_sig, this_sig, curr_context) == none 
                for other_sig in i2.signatures) 
                for this_sig in i1.signatures)

        # none should have been sorted out by now
        return specificity_higher ? higher(curr_context) : equal(curr_context)

    end

    # --------------- MethodSignatures and Concrete Callsignatures ------------------------------------------------------

    #=
        Problem: if I ask `foo(Int, Int) <: foo(T, T) where Add[T]` then this mechanism
        should already be able to detect that the left is more specific, since it should 
        check statically that Int requires the Add[Int] Interface.

        However, `foo(Vector{T}) <: foo(Iterable[&T])` would not be statically checked,
        since Vector{T} is not concrete yet.

        julia can do `Base.infer_return_type(length, (Vector{T} where T))`, so can I do something similar
        with my functions?

        Do I even want this? Do I need this? Clarification needed.
    =#
    function more_specific(m :: MethodSignature, m2 :: MethodSignature, context :: TypeContext) :: Specificity
        specificity = reduce_over_specificity(m.args, m2.args, context) 
        return merge_specificity(specificity, m.restriction, m2.restriction)
    end

    function more_specific(args :: Vector{DataType}, m :: MethodSignature, context :: TypeContext) :: Specificity
        @cases reduce_over_specificity(args, m.args, context) begin
            none => return none
            equal(new_context) => if is_empty_interface(m.restriction)
                    return equal(new_context)
                else
                    (context = new_context)
                end
            higher(new_context) => (context = new_context)
        end

        return @cases apply_context(m.restriction, context) begin
            applicationresolved(new_context) => higher(new_context)
            [applicationincomplete, applicationfailed] => none
        end
    end

end

end

