
using MacroTools


macro ignore(exprs...)
    return :()
end

# m = include("InterfaceDispatch.jl")
# using Main.m

parse_signature(sigexpr, typevars, implicitvars) = begin
    @capture sigexpr (fname_(args__) :: rettype_)

    map_arg(arg) = 
        if arg isa Symbol
            idx = findfirst(v -> v == arg, typevars)
            if idx !== nothing 
                # This is a Typeparam from the interface header
                # We need to interpolate it directly into the 
                # signature, because TypeParams are compared via 
                # identity
                return :(typeparams[$idx])
            end
            idx = findfirst(v -> v == arg, implicitvars)
            if idx !== nothing 
                return :(implicits[$idx])
            end
                

            # this is not one of the typevars, so it is probably
            # from the surrounding context/a regular Type.
            # return as is
            return arg
               
        elseif @capture arg typename_{typeparams__}
            return :(parametrctype(map_arg(typename), map_arg.(typeparams)...))
        else
            throw("Unknown signature element: $arg")
        end


    return :(signature($fname,  $(map_arg.(args)...); retval = $(map_arg(rettype))))
end

find_implicit_vars(signatures) = begin
    positional_implicits = Bool[]
    arbitrariy_implicits = Ref(0)
    for sig in signatures
        (@capture sig fname_(vars__) :: rettype_) || throw("no valid signature: $sig")

        for v in vars
            find_implicit_vars(v, positional_implicits, arbitrariy_implicits)
        end
        find_implicit_vars(rettype, positional_implicits, arbitrariy_implicits)
        find_implicit_vars(fname, positional_implicits, arbitrariy_implicits)
    end
    n_max = length(positional_implicits)
    return append!(
        [Symbol("_$i") for (i, exists) in enumerate(positional_implicits) if exists],
        (Symbol("_$i") for i in n_max+1:n_max+arbitrariy_implicits[])
        )
end
find_implicit_vars(s::Symbol, positional_implicits, arbitrariy_implicits) = begin
    if s == :_ 
        arbitrariy_implicits[] += 1
        return 
    end
    m = match(r"_([\d]+)", string(s))
    if m !== nothing
        n = parse(Int, m.captures[1])
        while length(positional_implicits) < n 
            push!(positional_implicits, false)
        end

        positional_implicits[n] = true
    end
    nothing
end

find_implicit_vars(e::Expr, positional_implicits, arbitrariy_implicits) = begin
    (@capture e fname_{args__}) || throw("unknown Signature element $e")
    find_implicit_vars(fname, positional_implicits, arbitrariy_implicits)
    all(find_implicit_vars(v, positional_implicits, arbitrariy_implicits) for v in args)
    nothing
end

macro interface(int_def, args...)
    @capture  int_def interface_name_{vars__}
    println((interface_name, vars))
    if length(args) > 0
        used_exps = if @capture args[1] extends(super_interfaces__)
            1
        else
            super_interfaces = []
            0
        end
    end
    if length(args) == used_exps
        body = :(begin end)
    else
        body = args[used_exps + 1]
        used_exps += 1
    end
    if length(args) > used_exps
        throw("More arguments to @interface than expected")
    end
    (@capture body begin signature_exprs__ end) ||
        throw("body of interface must be a begin ... end block")

    implicitvars = find_implicit_vars(signature_exprs)
    signatures = parse_signature.(signature_exprs, Ref(vars), Ref(implicitvars))
    println((super_interfaces, signatures))

    typeparams = [:(TypeParam($(string(var)))) for var in vars]
    implicitparams = [:(TypeParam($(string(var)))) for var in implicitvars]
    quote
        const $(esc(interface_name)) = let typeparams = tolist(TypeParam, ($(typeparams...),))
            implicits = tolist(TypeParam, ($(implicitparams...),))
            signatures = tolist(Signature, ($(signatures...),))
             Interface($(string(interface_name)), typeparams, implicits, signatures)
        end
    end

end


macro IFunction(name)
    return :(const $(esc(name)) = IFunction($(string(name))))
end


_replace(s::Symbol, replacements) = get(replacements, s, s)
_replace(e::Expr, replacements) = 
    if e.head == :curly
        :(parametrictype($(_replace(e.args, replacements)...)))
    else
        Expr(e.head, _replace(e.args, replacements)...)
    end
_replace(a::Array, replacements) = _replace.(a, Ref(replacements))
_replace(x, rep) = x


macro callsig(varsexp, sig)
    (@capture varsexp (vars__,)) || throw("unknown variable spec: $varsexp")
    println(vars)
    params = [Symbol("typeparam$i") for i in 1:length(vars)]
    paramdefs = [:($(Symbol("typeparam$i")) = TypeParam($(string(v)))) for (i, v) in enumerate(vars)]
    (@capture sig fname_(args__)) || throw("wrong callsig spec: $sig")
    replacements = Dict{Symbol, Symbol}(v => e for (v, e) in zip(vars, params))
    args = _replace(args, replacements)

    quote
        let 
            $(paramdefs...)
            callsig($(args...))
        end
    end
end
begin
    
    println("CallSignature: ",(@callsig (A, B) f(Vector{A }, B)))
    expr = quote
        init_iteration(I) :: _1
        has_next(I, _1) :: Bool
        next(I, _1) :: T
        foo(I, _) :: Int 
        bar() :: _
        baz(_5) :: _1
    end |> Base.remove_linenums!
    @assert find_implicit_vars(expr.args) == [:_1, :_5, :_6, :_7]

    println(@macroexpand @interface Iterate{I, T} begin
        init_iteration(I) :: _1
        has_next(I, _1) :: Bool
        next(I, _1) :: T
    end)


    # println("")
    # println("-------")
    # println("")

    # println(@macroexpand @interface SizedIterate{I, T} extends(Iterate{I, T}) begin
    #     length(I) :: Int
    # end)

    @IFunction init_iteration
    @IFunction has_next 
    @IFunction next 
    @interface Iterator{I, T} begin
        init_iteration(I) :: _1
        has_next(I, _1) :: Bool
        next(I, _1) :: T
    end
    println(Iterator)
end

