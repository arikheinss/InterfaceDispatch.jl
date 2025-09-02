import HashArrayMappedTries as hm
import HashArrayMappedTries: HAMT

# mutable with only const fields so we 
# can use identity to compare these
mutable struct TypeParam
    const name :: String
end
t::TypeParam == w::TypeParam = t === w
Base.show(io::IO, t::TypeParam) = print(io, "'$(t.name)")



const List{T} = Memory{T}

tolist(T, args) = begin 
    m = Memory{T}(undef, length(args))
    for i in 1:length(args) 
        m[i] = args[i]
    end
    m
end
tolist(args) = tolist(eltype(args), args)

# No other Datatypes exist in this model!!! Only ParametricType will be used for simplicity
struct ParametricType
    basetype :: Union{DataType, UnionAll, TypeParam}
    parameters :: List{Union{TypeParam, ParametricType}}
end

_extractType(::Type{Type{T}}) where T = T
ParametricType(::Type{T}) where T = ParametricType(
    _extractType(T.name.Typeofwrapper), 
    tolist(Union{TypeParam, ParametricType}, T.parameters)
)

Base.show(io::IO, p::ParametricType) = begin
    Base.show(io, p.basetype)
    print(io, "[")
    join(io, p.parameters, ", ")
    print(io, "]")
end
(p1 :: ParametricType == p2 :: ParametricType) = p1.basetype == p2.basetype  && 
    ((==) ⊚ length)(p1.parameters, p2.parameters) &&
    all(v1 isa TypeParam ? v1 === v2 : v1 == v2 for (v1, v2) in zip(p1.parameters, p2.parameters))


Base.convert(::Type{ParametricType}, ::Type{T}) where T = if T isa UnionAll
    throw("Cannot convert incomplete parametrised type to ParametricType")
else
    ParametricType(T, tolist(Union{TypeParam, ParametricType}, T.parameters))
end

Base.convert(::Type{Union{ParametricType, T}}, ::Type{W}) where {W, T} = convert(ParametricType, W)

parametrictype(base, params...) = ParametricType(base, tolist(Union{TypeParam, ParametricType}, params))
(t1 :: ParametricType == ::Type{T}) where T = T.name == t1.basetype.body.name



const SignatureType = Union{TypeParam, ParametricType}
struct Signature
    callable ::  Any
    args :: List{SignatureType}
    retval :: SignatureType
end

signature(f, args...; retval) = Signature(f, tolist(SignatureType, args), retval)

Base.show(io::IO, s::Signature) = begin
    print(io, s.callable, "(")
    join(io, s.args, ", ")
    print(io, ")")
    println(io, " :: ", s.retval)
end




struct Interface
    name::String
    variables :: List{TypeParam}
    implicitVars :: List{TypeParam}
     signatures :: List{Signature}
end

interface(params, sigs)  = Interface("", tolist(TypeParam, params), tolist(TypeParam, ()), tolist(Signature, sigs),) 

Base.show(io::IO, i::Interface) = begin
    print(io, "Interface $(i.name){")
    join(io, i.variables, ", ")
    println("} ($(length(i.signatures)) signatures)")
    for s in i.signatures
        print("\t")
        Base.show(io, s)
    end
end

const IAny = interface((),())
struct CallSig
    callsignature :: List{Union{ParametricType, TypeParam}}
    requirements :: Interface
end
callsig(types... ; req = IAny) = CallSig(tolist(Union{ParametricType, TypeParam}, types), req)


include("IFunctions.jl")





function applyReplacements end


applyReplacements(i::Interface, _replacements) = begin
    replacements = copy(_replacements)
    new_vars = TypeParam[]
    for v in i.variables
        if haskey(replacements, v) 
            if replacements[v] isa TypeParam
                push!(new_vars, replacements[v])
            end
        else
            new_var = TypeParam(v.name)
            replacements[v] = new_var
            push!(new_vars, new_var)
        end
    end
    new_vars = tolist(TypeParam, filter!(x -> x isa TypeParam, new_vars))

    new_implicits = TypeParam[]
    for v in i.implicitVars
        if haskey(replacements, v) 
            if replacements[v] isa TypeParam
                push!(new_implicits, replacements[v])
            end
        else
            new_var = TypeParam(v.name)
            replacements[v] = new_var
            push!(new_implicits, new_var)
        end
    end
    new_implicits = tolist(TypeParam, filter!(x -> x isa TypeParam, new_implicits))

    new_signatures = applyReplacements(i.signatures, replacements)
    return Interface(i.name, new_vars, new_implicits, new_signatures)
end


fully_applied(t::TypeParam) = false
# unionAll is used here as a base for homemade ParametricTypes, 
# it does not carry its own parameter list. So it is practically
# equivalent to DataType, which is considered concrete and fully applied
fully_applied(t::Union{DataType, UnionAll}) = true
fully_applied(p::ParametricType) = fully_applied(p.basetype) && all(fully_applied, p.parameters)

fully_applied(sig::Signature) = fully_applied(sig.retval) && all(fully_applied, sig.args)

@enum Inferrables Match NoMatch Indecidable
inferrable(sig::Signature; replacement_rules) = begin
    all(fully_applied, sig.args) || return Indecidable
    # for the type signature of fetch_node
    _types = tolist(ParametricType, sig.args)
    rettype = infer_returntype(sig.callable, _types)
    rettype == nothing && return NoMatch
    if more_specific(rettype, sig.retval)
        return Match 
    else
        return NoMatch
    end
end
check_signature(sig::Signature) =
    # TODO: something meaningfull here
    true

@enum ProcessResult::UInt8 Complete Incomplete ExitTrue ExitFalse
check_interface(i::Interface, types :: _replacement_rules) = begin
    replacement_rules = copy(_replacement_rules)

    signaturevec = copy(i.signatures)
    return process_nodes(signaturevec) do sig 
        applied_sig = applyReplacements(sig, replacements)

        inferred = inferrable(applied_sig)
        if inferred == Match 
            return Complete
        elseif inferred == Indecidable
            return Incomplete
        else # NoMatch
            return ExitFalse
        end
        
    end
end

function process_nodes(process::Function, lst::Vector)
    """applies process to all elements of lst. It is assumed that this operation
    may fail, or be incomplete on any single element, but maybe processing another 
    element of lst will change some internal state that makes it possible for this element
    to be processed again. Will thus shuffle elements around untill either all elements are
    processed or it is proven that the operation cannot complete 
        """
    frontidx = 1
    backidx = length(lst) + 1
    while frontidx ≤ length(lst)
        if frontidx == backidx
            return false
        end
        x = lst[frontidx]
        processresult = process(x)
        if processresult == Complete
            frontidx += 1 
            backidx = length(lst)
        elseif processresult == Incomplete
            backidx -= 1
            tmp = lst[backidx]
            lst[backidx] = x
            lst[frontidx] = tmp
        elseif processresult == ExitTrue
            return true
        elseif processresult == ExitFalse
            return false
        end
    end
end



applyReplacements(l::List{Signature}, replacements) = begin
    new_sigs = Signature[]
    for old_sig in l
        new_sig = applyReplacements(old_sig, replacements)
        if fully_applied(new_sig)
            if !check_signature(new_sig)
                # TODO: what is supposed to happen here? Raise an exception?
                # return the 'invalid_interface' somehow? 
                # need to think of a concept here
                throw("Interface was invalidly applied")
            end
        else
            push!(new_sigs, new_sig)
        end
    end
    return new_sigs
end

applyReplacements(s::Signature, replacements) = begin
    new_args = replace(s.args ) do a 
        applyReplacements(a, replacements)
    end

    return Signature(s.callable, new_args, applyReplacements(s.retval, replacements))
end
applyReplacements(p::ParametricType, replacements) =  ParametricType(p.basetype, applyReplacements.(p.parameters, replacements))

applyReplacements(t::TypeParam, replacements) = get(replacements, t) do 
     TypeParam(t.name) 
end





function more_specific end
const <-- = more_specific

more_specific(t::ParametricType, t2::ParametricType; replacement_rules = Dict()) = t.basetype == t2.basetype &&
    ((==) ⊚ length)(t.parameters, t2.parameters) &&
    all(more_specific(k1, k2; replacement_rules) for (k1, k2) in zip(t.parameters, t2.parameters))

more_specific(v1 :: TypeParam, v2 :: TypeParam; replacement_rules = Dict()) = begin
    v1 === v2 && return true
    if haskey(replacement_rules, v2)
        return replacement_rules[v2] === v1
    else
        replacement_rules[v2] = v1
        return true
    end
end

more_specific(::TypeParam, ::ParametricType; replacement_rules = nothing) = false

# more_specific(::Type{T}, t::TypeParam; replacement_rules = Dict()) where T = get!(replacement_rules, t, T) === T
more_specific(p::ParametricType, t::TypeParam; replacement_rules = Dict()) =
     if haskey(replacement_rules, t) 
        if more_specific(p, replacement_rules[t])
            replacement_rules[t] = p
            return true
        end
        return false
    else
            replacement_rules[t] = p
            return true
    end


 more_specific(s1 :: Signature, s2 :: Signature; replacement_rules = Dict()) = begin
    ret = s1.callable === s2.callable && 
        more_specific(s1.retval, s2.retval; replacement_rules) &&
        length(s1.args) == length(s2.args) &&
        all(more_specific(arg1, arg2; replacement_rules) for (arg1, arg2) in zip(s1.args, s2.args))
    ret
 end

 more_specific(this :: Interface, other :: Interface; replacement_rules = Dict()) = begin
    for sig in other.signatures
        # idx = findfirst(sig2 -> more_specific(sig2, sig; replacement_rules = copy(replacement_rules)), this.signatures) 
        idx = findfirst(this.signatures) do sig2
            more_specific(sig2, sig; replacement_rules = copy(replacement_rules))
        end
        if idx === nothing 
            # the signature does not appear in the left interface
            # this is ok if the relevant TypeParams are all mapped to 
            # concrete types, since we can then check if the signature holds statically
            applied_sig = applyReplacements(sig, replacement_rules)
            if fully_applied(applied_sig) && check_signature(applied_sig)
                continue
            else
                return false
            end
        end

        # execute again to update replacement_rules
        # TODO: make replacement_rules an immutable dict to avoid this nonsense
        more_specific(this.signatures[idx], sig; replacement_rules)
    end
    return true
end


more_specific(s1 :: CallSig, s2 :: CallSig; replacement_rules = Dict()) = begin
    all(more_specific(k1, k2; replacement_rules) for (k1, k2) in zip(s1.callsignature, s2.callsignature)) &&
    more_specific(s1.requirements, s2.requirements; replacement_rules)
end
more_specific(types :: List{ParametricType}, sig::CallSig; replacement_rules = Dict()) = begin
    length(sig.callsignature) == length(types) || return false
    all(more_specific(t1, t2; replacement_rules) for (t1, t2) in zip(types, sig.callsignature)) &&
        check_interface(sig.requirements, replacement_rules)
end