using Test
using InterfaceDispatch


for c in 'A':'Z'
    @eval $(Symbol(c)) = TypeParam(string($c))
    @eval $(Symbol(c * '2')) = TypeParam(string($c))
end

specific_with_reps(a, b) = let d = Dict()
    more_specific(a,b; replacement_rules = d), d
end
const Empty = Dict()
testmatch(a,b, req = Empty) = let (pass, d) = specific_with_reps(a, b)
    pass && all(haskey(d, k) && d[k] == v for (k, v) in req)
end



@testset "basic" begin
    @testset "ConcatIter" begin
        itr = ConcatIter(((), [1, 2, 3], (), 4:9))
        @test collect(itr) == collect(1:9)
        @test eltype(itr) == Int
        @test Base.IteratorSize(itr) == Base.HasLength()
    end
    @testset "parametric Types and type params" begin

        # println(@macroexpand1 @testmatch ParametricType(Int)  ParametricType(Int)  Dict())
        @test testmatch(T, W, Dict(W => T))

        @test testmatch( ParametricType(Int),  ParametricType(Int))
        @test !(ParametricType(Float64) <-- ParametricType(Int))

        @test testmatch( ParametricType(Int),  T, Dict(T=> ParametricType(Int)))
        @test testmatch(parametrictype(Vector, W), T, Dict(T => parametrictype(Vector, W)))
        @test !(T <-- parametrictype(Int))
        @test testmatch(parametrictype(Complex, Int), parametrictype(Complex, T), Dict(T => parametrictype(Int)))
        @test testmatch(parametrictype(Tuple, T, T), parametrictype(Tuple, A, B), Dict(A => T, B => T))
        @test testmatch(parametrictype(Tuple, T, W), parametrictype(Tuple, A, B), Dict(A => T, B => W))
        @test !(parametrictype(Tuple, T, W) <-- parametrictype(Tuple, A, A))
    end
    @testset "signatures" begin
        s1 = signature("", Int, Int; retval = Int)
        s2 = signature("asdf", Int, Int; retval = Int)
        s3 = signature("", Int, Int; retval = Bool)
        @test testmatch(s1, s1, Empty)
        @test !((s1 <-- s3) || (s3 <-- s1))
        @test !((s1 <-- s2) || (s2 <-- s1))
        st = signature("", Int, Int; retval = T)
        @test testmatch(s1, st, Dict(T => parametrictype(Int)))


        s1 = signature("", Int, Int; retval = Int)
        st = signature("", Int, T; retval = Int)
        @test testmatch(s1, st, Dict(T => parametrictype(Int)))


        st = signature("", Int, T; retval = Int)
        sw = signature("", Int, W; retval = Int)
        svt = signature("", Int, parametrictype(Vector, W); retval = Int)
        @test testmatch(st, sw, Dict(W => T))
        @test testmatch( svt, st, Dict(T => parametrictype(Vector, W)))

        s_t = signature("", T, T; retval = parametrictype(Vector, T))
        s_abc = signature("", A, B; retval = parametrictype(Vector, C))

        @test testmatch(s_t, s_abc, Dict(A => T, B => T, C => T))

        si = signature("", Int, Int; retval = Bool)
        @test fully_applied(si)
        
        s = signature("", Int, parametrictype(Dict, Int, String); retval = Bool)
        @test fully_applied(s)

        s = signature("", T, parametrictype(Dict, Int, String); retval = Bool)
        @test !fully_applied(s)

        s = signature("", Int, parametrictype(Dict, Int, T), retval = Bool)
        @test !fully_applied(s)

        s = signature("", Int, parametrictype(Dict, Int, String), retval = W)
        @test !fully_applied(s)
    end
    @testset "interfaces" begin
        function get end
        function len end
        vec = interface(
             (V, T),
             (
                signature(get, V, Int; retval = T),
                signature(len, V; retval = Int),
            ),
        )
        println(vec)
        function set end
        mut_vec = interface(
             (V2, T2),
             (
                signature(get, V2, Int; retval = T2),
                signature(len, V2; retval = Int),
                signature(set, V2, T2; retval = V2),
            ),
        )
        println(mut_vec)
        @test mut_vec <-- vec
        @test !(vec <-- mut_vec)

        function plus end
        iadd_simple = interface(
            (T,),
             (
                signature(plus, T, T; retval = T),
            ),
        )
        iadd_hetero = interface(
            (A, B, C),
            (
                signature(plus, A, B; retval = C),
            ),
        )
        iadd_reducible = interface(
            (X, Y),
            (
                signature(plus, X, Y; retval = X),
            ),
        )
        @test testmatch(iadd_simple,  iadd_hetero, Dict(A => T, B => T, C => T))
        @test !( iadd_hetero <-- iadd_simple)

        @test testmatch(iadd_reducible, iadd_hetero, Dict(A => X, B => Y, C => X))
        @test !( iadd_hetero <-- iadd_reducible)
        
        @test testmatch(iadd_simple,  iadd_reducible, Dict(X => T, Y => T))
        @test !( iadd_reducible <-- iadd_simple)

        i3 = interface((A, B, C), 
            (signature("", A, C; retval = B), ))
        i4 = interface((X, Y), 
            (signature("", Y, Y; retval = X), ))
        @test testmatch(i4, i3, Dict(A => Y, C => Y, B => X))

        i_rep = applyReplacements(i3, Dict(B => W, C => Int))
        @test i_rep isa Interface 
        @test  length(i_rep.variables) == 2 && i_rep.variables[1].name == "A" && i_rep.variables[2].name == "W"
        
        @test length(i_rep.signatures) == 1 
        @show i_rep
        @show parametrictype(Int) == parametrictype(Int)
        @test i_rep.signatures[1].args[1] == i_rep.variables[1]
        @test i_rep.signatures[1].args[2] == parametrictype(Int)
        @test i_rep.signatures[1].retval == i_rep.variables[2]
        

    end
    @testset "function tables" begin
        testf = IFunction("test")

        ia = IAny
        # bottom
        sig_i_i = callsig(Int, Int)
        
        sig_a_b = callsig(A, B; req = interface((A, B), 
            (signature("", A; retval = A), )))
        sig_c_d = callsig(C, D; req = interface((C, D),
            (signature("", D; retval = D), )))
        sig_x_y = callsig(X, Y; req = interface((X, Y),
            (signature("", X; retval = X),
            signature("", Y; retval = Y),)))
        sig_e_e =  callsig(E, E; req = interface((E, ),
            (signature("", E; retval = E), )))
        sig_f_f = callsig(F, F)
        sig_v_w = callsig(V, W)
        @test more_specific(sig_f_f, sig_v_w)

        @test more_specific(sig_a_b, sig_v_w)
        @test more_specific(sig_c_d, sig_v_w)
        @test !more_specific(sig_v_w, sig_a_b)
        @test !more_specific(sig_v_w, sig_c_d)

        @test more_specific(sig_x_y, sig_a_b)
        @test more_specific(sig_x_y, sig_c_d)

        @test more_specific(sig_e_e, sig_x_y)
        @test more_specific(sig_i_i, sig_e_e)

        @test more_specific(sig_e_e, sig_f_f)

        

        ib = interface((A,),
            (
                signature("b", A; retval = A),
            ),
        )
        ic = interface((A,),
            (
                signature("b", A; retval = A),
                signature("c", A; retval = A),
            ),
        )
        id = interface((A,),
            (
                signature("b", A; retval = A),
                signature("c", A; retval = A),
                signature("d", A; retval = A),
            ),
        )
        @assert (ib <-- ia) && (ic <-- ib) && (id <-- ic)

        register(
            testf, 
            callsig(Int, Int; req = ia),
            (i, j) -> i + j,
        )
    end
end