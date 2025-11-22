using InterfaceDispatch
using SumTypes: isvariant
for sym in names(InterfaceDispatch; all= true)
    @eval import InterfaceDispatch: $sym
end
using Test 

# ----------TestInterfaces -------------------------------------
begin
    struct ItersizeInfinite end

    init_iter(v :: Vector) = 1
    has_next(v :: Vector, i :: Int) = i ≤ length(v) 
    get_next(v :: Vector, i :: Int) = @inbounds (v[i], i+1)

    i_iter(I = TypeParam("I"), T = TypeParam("T"), ST = TypeParam("_ST")) = Interface([I, T, ST],[
            interfacesig(init_iter, I, ST),
            interfacesig(has_next, I, ST, Bool),
            interfacesig(get_next, I, ST, parametrizedType(Tuple, T, ST)),
        ],
        "iterate")

    i_sizediter(I = TypeParam("I"), T = TypeParam("T"), ST = TypeParam("_ST")) = 
        let i = i_iter(I, T, ST)
        push!(i.signatures, interfacesig(length, I, Int))
        i 
    end
    i_infiter(I = TypeParam("I"), T = TypeParam("T"), ST = TypeParam("_ST")) = 
        let i = i_iter(I, T, ST)
        push!(i.signatures, interfacesig(length, I, ItersizeInfinite))
        i 
    end

    i_vec(V = TypeParam("V"), T = TypeParam("T")) =
        Interface(
            [V, T],
            [
                interfacesig(getindex, V, T),
                interfacesig(length, V, Int)
            ],
            "vec"
        )
    i_mutvec(V = TypeParam("V"), T = TypeParam("T")) = let i = i_vec(V, T)
        push!(i.signatures, interfacesig(setindex!, V, T, Int, V))
        i 
    end

    IAny = Interface(TypeParam[], InterfaceSignature[], "IAny")

    struct SimpleVec{T}
        ptr :: Ptr{T}
        length :: Int 
    end

    struct Naturals end

    ($)(base :: Union{UnionAll, DataType}, args) = parametrizedType(base, args...)
    ($)(base :: Union{Function, IFunction}, args) = interfacesig(base, args...)
        

    struct AbstractVector´ end
    struct AbstractDenseVector´ end
end


@testset "Tests" begin
    TC = TypeContext

    A = TypeParam("A")
    B = TypeParam("B")
    C = TypeParam("C")
    D = TypeParam("D")
    E = TypeParam("E")
    F = TypeParam("F")
    G = TypeParam("G")
    H = TypeParam("H")
    I = TypeParam("I")
    J = TypeParam("J")
    K = TypeParam("K")
    L = TypeParam("L")
    M = TypeParam("M")
    N = TypeParam("N")
    O = TypeParam("O")
    P = TypeParam("P")
    Q = TypeParam("Q")
    R = TypeParam("R")
    S = TypeParam("S")
    T = TypeParam("T")
    U = TypeParam("U")
    V = TypeParam("V")
    W = TypeParam("W")
    X = TypeParam("X")
    Y = TypeParam("Y")
    Z = TypeParam("Z")
    _ST = TypeParam("_ST")
    I2 = TypeParam("I")
    _ST2 = TypeParam("_ST")
    I3 = TypeParam("I")
    _ST3 = TypeParam("_ST")



    @testset "types and parameters" begin
        @test T ≠ TypeParam("T")

        @test typebase(Int) === Int 
        @test typebase(Array{1, Int}) === Array

        tupledict = ParametrizedType(Dict, [T, ParametrizedType(Tuple, [T, T])])

        context = TypeContext(T => Int, N => 1)
        
        @test apply_context(T, context) == Int
        @test apply_context(tupledict, context) == Dict{Int, Tuple{Int, Int}}
        @test apply_context(ParametrizedType(Dict, [T, W]), context) === novalue
        @test apply_context(ParametrizedType(Array, [N, T]), context) == Array{1, Int}
        @test apply_context(ParametrizedType(Array, [N, ParametrizedType(Tuple, [T, T])]), context) == Array{1, Tuple{Int, Int}}



        
    end
    @testset "context application" begin
        @testset "InterfaceSignatures" begin
            context1 = TC(V => Vector{Int})

            sig1 = InterfaceSignature(Base.length, TypeLike[V], Int)
            @test apply_context(sig1, context1) == applicationresolved(context1)
            @test apply_context(sig1, TC(V => Nothing)) == applicationfailed

            sig2 = InterfaceSignature(length, TypeLike[V], T)
            @test apply_context(sig2, context1) == applicationresolved(TC(V => Vector{Int}, T => Int))
            
            sig3 = interfacesig(length, V, String)
            @test apply_context(sig3, context1) == applicationfailed

            @test apply_context(sig2, TC(V => parametrizedType(Array, 1, W))) == applicationincomplete

        end
        @testset "Interfaces" begin
            ivec = Interface([V, T], [
                interfacesig(getindex, V, Int, T),
                interfacesig(length, V, Int),
            ],
            "Vec")
            imutvec = i_mutvec(W, U)            

            @test apply_context(ivec, TC(V => Vector{Int})) == applicationresolved(TC(V => Vector{Int}, T => Int))
            @test apply_context(ivec, TC(T => Int)) == applicationincomplete
            # Would it be better to return a partially applied Interface upon incomplete Application? Do we even use this method anywhere?

            iiter = i_iter(I, T, _ST)
            @test apply_context(iiter, TC(I => Vector{Int})) == applicationresolved(TC(I => Vector{Int}, T => Int, _ST => Int))
        end
    end

    @testset "specificity tests" begin
        
        @testset "types and typeparams" begin
            context = TypeContext(T => Int, N => 1)

            @test isvariant(more_specific(Int, Int), :equal)
            @test more_specific(Int, Float64) === none
            @test more_specific(T, Int) === none
            @test more_specific(Int, T, context) == higher(context)
            @test isvariant(more_specific(Int, T), :higher)
            @test more_specific(String, T, context) == none
            @test more_specific(1, N, context) == higher(context)

            p = ParametrizedType(Array, [N, T])
            @test more_specific(Array{1, Int}, p, context) == higher(context)
            @test more_specific(ParametrizedType(Tuple, [T, T]), ParametrizedType(Tuple, [V, W])) == higher(TC(V => T, W => T))
            @test more_specific(ParametrizedType(Tuple, [V, V]), ParametrizedType(Tuple, [T, W]), context) == none
            @test more_specific(Tuple{Int, Int}, ParametrizedType(T, [Int, Int])) == higher(TC(T => Tuple))
            @test more_specific(Tuple{Int, String}, ParametrizedType(T, [Int, Int])) == none
            @test more_specific(Tuple{Int, Int}, ParametrizedType(T, [Int, Int])) == higher(TC(T => Tuple))
        end

        @testset "interfacesig" begin
            sig1 = interfacesig(length, V, T)
            sig2 = interfacesig(length, W, Int)
            @test more_specific(sig2, sig1) == higher(TC(V => W, T => Int))

            @test more_specific(interfacesig(length, Int, Int), interfacesig(size, Int, Int)) == none
            @test more_specific(interfacesig(length, Int, Char, Int), interfacesig(length, T, T, Int)) == none
            @test more_specific(interfacesig(length, Tuple{Int, Int}, Int), interfacesig(length, parametrizedType(Tuple, T, T), Int)) == higher(TC(T => Int))
            @test more_specific(interfacesig(length, Int, Int), interfacesig(length, T, Int), TC(T=>Int)) == higher(TC(T => Int))
            @test more_specific(interfacesig(length, Int, Int), interfacesig(length, Int, Int), TC(T=>Int)) == equal(TC(T => Int))
            
            
        end
        @testset "Interface" begin
            ivec = Interface([V, T], [
                interfacesig(getindex, V, Int, T),
                interfacesig(length, V, Int),
            ],
            "Vec")
            imutvec = Interface([W, U], [
                interfacesig(getindex, W, Int, U),
                interfacesig(length, W, Int),
                interfacesig(setindex!, W, Int, U, W),
            ],
            "MutVec")

            ivec2 = Interface([W, U], [
                interfacesig(getindex, W, Int, U),
                interfacesig(length, W, Int),
            ],
            "Vec2")
            @test more_specific(ivec, ivec2) == equal(TC(W => V, U => T))
            @test more_specific(imutvec, ivec) == higher(TC(T => U, V => W))
            @test more_specific(ivec, imutvec) == none

            function has_next end
            function init_iter end 
            function get_next end 

            iiter = Interface([I, T, _ST], [
                interfacesig(init_iter, I, _ST),
                interfacesig(get_next, I, _ST, parametrizedType(Tuple, T, _ST)),
                interfacesig(has_next, I, _ST, Bool),
            ],
            "iter",
            )
            isizediter = Interface([I2, U, _ST2], [
                interfacesig(init_iter, I2, _ST2),
                interfacesig(get_next, I2, _ST2, parametrizedType(Tuple, U, _ST2)),
                interfacesig(has_next, I2, _ST2, Bool),
                interfacesig(length, I2, Int),
            ],
            "sizediter",
            )
            iinfiter = Interface([I3, W, _ST3], [
                interfacesig(init_iter, I3, _ST3),
                interfacesig(get_next, I3, _ST3, parametrizedType(Tuple, W, _ST3)),
                interfacesig(has_next, I3, _ST3, Bool),
                interfacesig(length, I3, Int),
            ],
            "infiter",
            )

            @test more_specific(iinfiter, iiter) == higher(TC(I => I3, T => W, _ST => _ST3))
            @test more_specific( iiter, iinfiter,) == none

            @test more_specific(isizediter, iiter) == higher(TC(I => I2, T => U, _ST => _ST2))
            @test more_specific( iiter, isizediter,) == none
        end

        @testset "MethodSignature" begin
            iAny = Interface(TypeParam[], InterfaceSignature[], "IAny")
            m1 = MethodSignature(TypeLike[Int, Int], iAny)
            m2 = MethodSignature(TypeLike[T, T], Interface(TypeParam[T], InterfaceSignature[
                interfacesig(+, T, T, T)
            ], ""))

            @test more_specific(m1, m2) == higher(TC(T => Int))
            @test more_specific(m2, m1) == none

            
            function has_next end
            function init_iter end 
            function get_next end 

            mi1 = MethodSignature(TypeLike[parametrizedType(Array, 1, T)], iAny)
            mi2 = MethodSignature(TypeLike[U], Interface([I, U, _ST], [
                interfacesig(init_iter, I, _ST),
                interfacesig(get_next, I, _ST, parametrizedType(Tuple, U, _ST)),
                interfacesig(has_next, I, _ST, Bool),
            ],
            "iter"))
            
            # see my comment on the corresponding method definition
            @test_broken more_specific(m1, m2) == higher(TC(I => parametrizedType(Array, 1, T), U => T, _ST => Int))

        end

        
        @testset "Vec{DataType} and Methodsigs" begin

            # sum(Iterable[&I, T], Summable[&T])
            i1 = i_iter(I, T, _ST)
            push!(i1.signatures, interfacesig(+, T, T, T))
            m1 = MethodSignature(TypeLike[I, T], i1)

            @test more_specific([Vector{Int}, Int], m1) == higher(TC(I => Vector{Int}, T => Int, _ST => Int))
        end
    end
    @testset "IFunctions" begin
        i_length = IFunction("length")
        i_getindex = IFunction("getindex")
        i_setindex = IFunction("setindex")
        i_collect = IFunction("collect")
        i_init_iter = IFunction("init_iter")
        i_has_next = IFunction("has_next")
        i_get_next = IFunction("get_next")
        

        # register_method(i_length, MethodSignature(TypeLike[parameterType]))
        ms = MethodSignature

        register_method(i_length, ms([SimpleVec$(A,)], IAny), x -> x.length)
        register_method(i_length, ms([Naturals], IAny), x -> ItersizeInfinite())

        register_method(i_getindex, ms([SimpleVec$(B,), Int], IAny), (v, i) -> Base.unsafe_load(v.ptr, i))
        register_method(i_getindex, ms([Naturals, Int], IAny), (_, i) -> i)


        a = [0.0, 1.0, 2.0]
        v1 = SimpleVec(pointer(a), 3)
        𝐍 = Naturals()

        @test i_length(v1) == 3
        @test i_length(𝐍) == ItersizeInfinite()

        @test i_getindex(v1, 2) == a[2]
        @test i_getindex(𝐍, 1337) == 1337

        @test infer_returntype(i_length, [SimpleVec{Int}]) == Int
        @test infer_returntype(i_length, [Naturals]) == ItersizeInfinite
        @test infer_returntype(i_getindex, [SimpleVec{String}, Int]) == String

        ivec = Interface([V, T], [
            i_length$(V, Int),
            i_getindex$(V, Int, T),
        ], 
        "Vec")

        iiter = Interface([I, T, _ST], [
            i_init_iter$(I, _ST),
            i_has_next$(I, _ST, Bool),
            i_get_next$(I, _ST, Tuple$(T, _ST)),
        ],
        "iiter"
        )

        @test apply_context(ivec, TC(V => SimpleVec{String})) == applicationresolved(TC(V => SimpleVec{String}, T => String))
        @test apply_context(ivec, TC(V => Naturals)) == applicationfailed # Nats don't check Vec because length(𝐍) ≠ Int

        @test apply_context(iiter, TC(I => SimpleVec{String})) == applicationfailed
        @test apply_context(iiter, TC(I => Naturals)) == applicationfailed # Nats don't check Vec because length(𝐍) ≠ Int

        register_method(i_init_iter, ms([V], ivec), x -> 1)
        register_method(i_has_next, ms([V, Int], ivec), (v, i) -> i ≤ (i_length(v) :: Int))

        getnext_simplevec(v :: SimpleVec{T}, i) where T = (i_getindex(v, i) :: T, i+1)
        register_method(i_get_next, ms([V, Int], ivec), getnext_simplevec)

        @test apply_context(iiter, TC(I => SimpleVec{String})) == applicationresolved(TC(I => SimpleVec{String}, T => String, _ST => Int))

        @test let arr = Float64[], state = i_init_iter(v1)
            while i_has_next(v1, state)
                x, state = i_get_next(v1, state)
                push!(arr, x)
            end
            arr == a 
        end

        i_zero = IFunction("zero")
        iZero = Interface([V], [i_zero$(Type$(V,), V)], "IZero")

        register_method(i_zero, ms([Type{Int}], IAny), _ -> 0)
        register_method(i_zero, ms([Type{Float64}], IAny), _ -> 0.0)
        register_method(i_zero, ms([Type{Bool}], IAny), _ -> false)

        @test i_zero(Int) == 0
        @test i_zero(Bool) == false

        @test apply_context(iZero, TC(V => Bool)) == applicationresolved(TC(V => Bool))
        @test apply_context(iZero, TC(V => Int)) == applicationresolved(TC(V => Int))
        @test apply_context(iZero, TC(V => Int32)) == applicationfailed


        complex_zero(::Type{Complex{V}}) where V = (i_zero(V) :: V) + im * (i_zero(V) :: V)
        register_method(i_zero, ms([Type$(Complex$(V,),)], iZero), complex_zero)

        @test i_zero(Complex{Int}) == 0 + 0 * im

        @test_throws Any i_zero(Complex{Int32})

        @test apply_context(iZero, TC(V => Complex{Int})) == applicationresolved(TC(V => Complex{Int}))
        @test apply_context(iZero, TC(V => Complex{Int32})) == applicationfailed
        



        # so GC does not delete it before, since a is not used directly
        Base.donotdelete(a)

        struct IsSuperType end
        struct NotSuperType end
        struct NoSuperType end

        i_parent = IFunction("parent")
        register_method(i_parent, ms([Type$(T,)], IAny), _ -> NoSuperType())

        i_isparent = IFunction("isparent")
        register_method(i_isparent, ms([Type$(T,), Type$(T,)], IAny), (a, b) -> IsSuperType())
        register_method(i_isparent, ms([Type$(T,), Type$(W,)], IAny), (a, b) -> NotSuperType())

        i_isSuperType = Interface([T, S], [
            i_isparent$(Type$(T,), Type$(S,), IsSuperType),
        ],
        "isSuperType",
        )

        i_parentIsSuperType =  Interface([T, S, P], [
            i_parent$(Type$(T,), Type$(P,)),
            i_isparent$(Type$(P,), Type$(S,), IsSuperType),
        ],
        "ParentIsSuperType"
        )
        
        # this causes a StackOverflow, because I fixed the more_specific(::MSig, ::MSig) method.
        register_method(i_isparent, ms([Type$(T,), Type$(S,)], i_parentIsSuperType), (a, b) -> IsSuperType())




        # @test apply_context(i_isSuperType, TC(T => SimpleVec$(W,), S => AbstractVector´)) in (applicationfailed, applicationincomplete)

        register_method(i_parent, ms([Type$(AbstractDenseVector´,)], IAny), _-> AbstractVector´)
        register_method(i_parent, ms([Type$(SimpleVec$(W,),)], IAny), _-> AbstractDenseVector´)

        @test infer_returntype(i_parent, DataType[Type{SimpleVec{Int}}]) === Type{AbstractDenseVector´}
        @test infer_returntype(i_parent, DataType[Type{Int}]) === NoSuperType


        @test apply_context(i_isSuperType, TC(T => SimpleVec{Int}, S => AbstractDenseVector´)) == applicationresolved(TC(T => SimpleVec{Int}, S => AbstractDenseVector´))
        @test apply_context(i_isSuperType, TC(T => SimpleVec{Int}, S => AbstractVector´)) == applicationresolved(TC(T => SimpleVec{Int}, S => AbstractVector´))

        # @test_broken apply_context(i_isSuperType, TC(T => SimpleVec$(W,), S => AbstractDenseVector´)) == applicationresolved(TC(T => SimpleVec$(W,), S => AbstractDenseVector´))
        # @test_broken apply_context(i_isSuperType, TC(T => SimpleVec$(W,), S => AbstractVector´)) == applicationresolved(TC(T => SimpleVec$(W,), S => AbstractVector´))
    end
    
end