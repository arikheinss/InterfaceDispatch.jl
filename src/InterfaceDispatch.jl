module InterfaceDispatch
import Base.==
import Base:iterate

include("utils.jl")
include("core.jl")
include("ConvenienceMacros.jl")

export @ignore, @interface
export TypeParam, ParametricType, Interface, Signature, CallSig, SignatureType, more_specific, applyReplacements, tolist, 
        interface, parametrictype, signature, IAny, <--, IFunction, Node, register, inject_node, ConcatIter, callsig, fully_applied


end # module InterfaceDispatch
