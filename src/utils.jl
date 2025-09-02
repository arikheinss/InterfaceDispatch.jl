on(f,g) = (args...) -> f(g.(args)...)
const ⊚ = on


struct ConcatIter{Coll}
    itrs :: Coll
end

iterate(itr::ConcatIter) = begin
    outer = iterate(itr.itrs)
    while outer !== nothing 
        currItr, outer_st = outer 
        inner = Base.iterate(currItr)
        if inner !== nothing
            val, inner_st = inner
            return (val, (currItr, outer_st, inner_st))
        end
        outer = Base.iterate(itr.itrs, outer_st)
    end
    return nothing
end

Base.iterate(itr::ConcatIter, (currItr, outer_st, inner_st)) = begin
    inner = Base.iterate(currItr, inner_st)
    if inner !== nothing
        val, inner_st = inner
        return (val, (currItr, outer_st, inner_st))
    end
    while  true
        outer = Base.iterate(itr.itrs, outer_st)
        outer == nothing && return nothing
        currItr, outer_st = outer

        inner = Base.iterate(currItr)
        if inner !== nothing
            val, inner_st = inner
            return (val, (currItr, outer_st, inner_st))
        end
    end
end

Base.eltype(itr::ConcatIter) = promote_type(eltype.(itr.itrs)...)

Base.IteratorSize(itr::ConcatIter) = begin
     Base.IteratorSize(itr.itrs) == Base.IsInfinite() && return Base.IsInfinite()
     for i in itr.itrs
        size_i = Base.IteratorSize(i) 
        size_i == Base.IsInfinite() && return Base.IsInfinite()
        size_i == Base.SizeUnknown() && return Base.SizeUnknown()
     end
     return Base.HasLength()
end

Base.length(itr::ConcatIter) = sum(length, itr.itrs)