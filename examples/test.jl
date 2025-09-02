
struct SimpleVec{T}
    ptr :: Ptr{T}
    len :: Int 
end

@Imethod length(l :: SimpleVec{T}) = l.len
@Imethod getindex(l::SimpleVec{T}, i :: Int) = if 1 ≤ i ≤ length(l)
    return Base.unsafe_load(l.ptr, i)
else
    throw("out of bounds error")
end



@interface Vec{V, T} begin
    getindex(V, Int) :: T 
    length(V) :: Int
end
# Potential Problem: Dict{Int, T} is now a Vec{&, T}
# Solution: Dict does not implement getindex, but a 
# different method getkey


@interface Array{A, T, N} begin
    size(A) :: NTuple{N, Int}
    getindex(A, NTuple{N, Int}...) :: T
end

@Imethod size(v :: Vec{&I, T}) = (length(v), )

struct ConstantComplexity end 
struct LinearComplexity end 
struct QuadraticComplexity end 

# there is something cool here, just gotta figure it out
@Imethod complexity( :: SimpleVec{T}, ::Function{getindex}, ::Type{Tuple{Int}}) = ConstantComplexity()

@interface Iterable{I, T} begin
    init_iter(I) :: _1
    has_next(I, _1) :: Bool 
    next(I, _1) :: Tuple{T, _1}
end

@interface SizedIterable{I, T} extends(Iterable{I, T})  begin
    length(I) :: Int
end

struct ItertypeInfinite end
@Ifunction itersize

@interface InfiniteIterator{I, T} extends{Iterable} begin
    itersize(I) :: ItertypeInfinite
end

@Imethod collect(itr :: Iteratble{&I, T}) = begin
    res = T[]
    for x in itr 
        push!(res, x)
    end
    res
end

@Imethod collect(itr :: SizedIterable{&I, T}) = begin
    res = Vector{T}(undef, length(itr))
    for (i, x) in enumerate(itr)
        setindex!(res, i, x)
    end
    res
end
@Imethod collect(itr :: InfiniteIterator{&I, T}) = throw("Attempted to collect infinite Iterator")



@Imethod init_iter(v :: Vec{&I, T})  = 1
@Imethod has_next(v :: Vec{&I, T}, i :: Int) = i ≤ length(v)  
@Imethod next(v :: Vec{&I, T}, i :: Int) = (getindex(l, i), i+1) 

@interface Summable{A, B, C} begin
    +(A, B) :: C
end
@interface SumReduce{A, B} begin
    +(A, B) :: A
end

@Imethod sum(itr :: Iterable{&I, T}, init :: SumReduce{&A, B}) = begin
    curr = init
    for x in itr
        curr = curr + x 
    end
    return curr
end

struct UnitRange
    start :: Int 
    stop :: Int 
end

@Imethod length(u :: UnitRange) = u.stop - u.start + 1
@Imethod getindex(u :: UnitRange, i :: Int) = u.start + i - 1

@Imethod gauss(n :: Int) = n * (n + 1) ÷ 2
@Imethod sum(u :: UnitRange, init :: Int) = begin
    gauss(u.stop) - gauss(u.start - 1) + init
end

