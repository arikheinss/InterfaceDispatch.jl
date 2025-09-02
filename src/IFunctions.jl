
mutable struct Node
    const implementation :: Any
    const callsignature :: CallSig
    const children :: Vector{Node}
end

struct IFunction
    name :: String
    methodtable :: Dict{Int, Vector{Node}}
end

IFunction(name) = IFunction(name, Dict{Int, Vector{Node}}())

register(f::IFunction, sig:: CallSig, impl::Any) = begin
    node = Node(impl, sig, Node[])
    nargs = length(sig.callsignature)
    if haskey(f.methodtable, nargs)
        table = f.methodtable[nargs]
        inject_node(node, table)
    else
        f.methodtable[nargs] = [node]
    end
    return f
end


# Prototype was in python, and I am too lazy to think up a more julian way
# I'm sorry
const Id = Ptr{Nothing}
id(x) = Base.pointer_from_objref(x)


# BROKEN. when fetching a signature, we get a list of concrete types that are to
# be compared to the types/interfaces.
fetch_node(signature :: List{ParametricType}, table :: Vector{Node}, visited = Dict{Id, Node}) = begin
    candidate = nothing
    for node in table
        haskey(visited, id(node)) && return visited[id(node)]
        if signature == node.callsignature 
            visited[id(node)] = node
            return node
        end
        if more_specific(signature, node.callsignature)
            new_candidate = fetch_node(signature, node.children)
            if new_candidate === nothing
                new_candidate = node 
            end
            if candidate !== nothing && new_candidate !== candidate
                throw("Multiple candidates found.")
            end
            candidate = new_candidate
        end
    end
    for node in table
        visited[id(node)] = candidate
    end
    return candidate
end


inject_node(node :: Node, table :: Vector{Node}; parent = nothing) = begin
    was_injected_here = was_injected = false
    i = 1
    while i ≤ length(table)
        othernode = table[i]
        othernode === node && return nothing
        if node.callsignature == othernode.callsignature
            node.children = othernode.children
            table[i] = node 
            return nothing
        end
        if more_specific(othernode.callsignature, node.callsignature)
            push!(node.children, othernode)
            if !was_injected_here
                table[i] = node
                was_injected = was_injected_here = true
            else
                deleteat!(table, i)
                continue
            end
        elseif more_specific(node.callsignature, othernode.callsignature)
            inject_node(node, othernode.children; parent = othernode)
            was_injected = true
        end
        i += 1
    end
    if !was_injected
        push!(table, node)
    end
end