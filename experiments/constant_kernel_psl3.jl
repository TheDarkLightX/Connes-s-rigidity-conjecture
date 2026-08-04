using JSON
using LinearAlgebra

const P = 3
const MAX_DEGREE = 3

modp(x) = mod(x, P)

# Polynomials in λ over F₃ represented by coefficient vectors of fixed length.
poly_const(x) = [modp(x); zeros(Int, MAX_DEGREE)...]
poly_lambda() = [0, 1, zeros(Int, MAX_DEGREE-1)...]

function poly_add(a, b)
    modp.(a .+ b)
end

function poly_mul(a, b)
    out = zeros(Int, MAX_DEGREE + 1)
    for i in 0:MAX_DEGREE, j in 0:MAX_DEGREE
        i + j <= MAX_DEGREE || continue
        out[i+j+1] = modp(out[i+j+1] + a[i+1] * b[j+1])
    end
    out
end

function poly_neg(a)
    modp.(-a)
end

function poly_equal(a, b)
    all(modp.(a .- b) .== 0)
end

function poly_matrix_mul(A, B)
    rows, inner, _ = size(A)
    inner2, cols, _ = size(B)
    @assert inner == inner2
    C = zeros(Int, rows, cols, MAX_DEGREE + 1)
    for i in 1:rows, j in 1:cols, k in 1:inner
        C[i,j,:] .= poly_add(C[i,j,:], poly_mul(vec(A[i,k,:]), vec(B[k,j,:])))
    end
    C
end

function poly_matrix_from_constant(A::Matrix{Int})
    rows, cols = size(A)
    out = zeros(Int, rows, cols, MAX_DEGREE + 1)
    out[:,:,1] .= modp.(A)
    out
end

function elementary_poly(i::Int, j::Int, sign::Int=1)
    U = zeros(Int, 3, 3, MAX_DEGREE + 1)
    for k in 1:3
        U[k,k,:] .= poly_const(1)
    end
    U[i,j,:] .= sign == 1 ? poly_lambda() : poly_neg(poly_lambda())
    U
end

function unique_permutations(t::NTuple{3,Int})
    a,b,c = t
    collect(Set([(a,b,c),(a,c,b),(b,a,c),(b,c,a),(c,a,b),(c,b,a)]))
end

function multiset_triples()
    [(a,b,c) for a in 1:3 for b in a:3 for c in b:3]
end

function symmetric_cube_action(U)
    triples = multiset_triples()
    row_of = Dict(t => q for (q,t) in enumerate(triples))
    A = zeros(Int, 10, 10, MAX_DEGREE + 1)
    for (col,t) in enumerate(triples)
        for source in unique_permutations(t)
            for a in 1:3, b in 1:3, c in 1:3
                a <= b <= c || continue
                coefficient = poly_mul(
                    poly_mul(vec(U[a,source[1],:]), vec(U[b,source[2],:])),
                    vec(U[c,source[3],:])
                )
                all(coefficient .== 0) && continue
                row = row_of[(a,b,c)]
                A[row,col,:] .= poly_add(A[row,col,:], coefficient)
            end
        end
    end
    A, triples
end

const K_TRIPLES = [(1,1,2),(1,1,3),(1,2,2),(1,2,3),(1,3,3),(2,2,3),(2,3,3)]
const DIAGONAL_TRIPLES = [(1,1,1),(2,2,2),(3,3,3)]

function kernel_action(U)
    A, triples = symmetric_cube_action(U)
    row_of = Dict(t => q for (q,t) in enumerate(triples))
    K = zeros(Int, 7, 7, MAX_DEGREE + 1)
    for (col,tcol) in enumerate(K_TRIPLES), (row,trow) in enumerate(K_TRIPLES)
        K[row,col,:] .= A[row_of[trow],row_of[tcol],:]
    end
    # Kernel invariance: no diagonal component may be produced.
    for tdiag in DIAGONAL_TRIPLES, tcol in K_TRIPLES
        @assert all(A[row_of[tdiag],row_of[tcol],:] .== 0)
    end
    K
end

# psl₃ quotient coordinates: E12,E13,E21,E23,E31,E32,H, H=diag(1,-1,0).
function psl_coordinates(M)
    coords = [
        vec(M[1,2,:]), vec(M[1,3,:]), vec(M[2,1,:]),
        vec(M[2,3,:]), vec(M[3,1,:]), vec(M[3,2,:]),
        poly_add(vec(M[1,1,:]), poly_neg(vec(M[3,3,:])))
    ]
    reduce(vcat, [reshape(c,1,:) for c in coords])
end

function psl_basis_matrix(index::Int)
    M = zeros(Int,3,3,MAX_DEGREE+1)
    if index == 1
        M[1,2,:] .= poly_const(1)
    elseif index == 2
        M[1,3,:] .= poly_const(1)
    elseif index == 3
        M[2,1,:] .= poly_const(1)
    elseif index == 4
        M[2,3,:] .= poly_const(1)
    elseif index == 5
        M[3,1,:] .= poly_const(1)
    elseif index == 6
        M[3,2,:] .= poly_const(1)
    elseif index == 7
        M[1,1,:] .= poly_const(1)
        M[2,2,:] .= poly_const(-1)
    else
        error("bad psl basis index")
    end
    M
end

function conjugation_action(U, Uinv)
    A = zeros(Int,7,7,MAX_DEGREE+1)
    for col in 1:7
        image = poly_matrix_mul(poly_matrix_mul(U, psl_basis_matrix(col)), Uinv)
        coordinates = psl_coordinates(image)
        for row in 1:7
            A[row,col,:] .= coordinates[row,:]
        end
    end
    A
end

# Explicit signed-permutation intertwiner from the tensor kernel to psl₃.
function intertwiner()
    T = zeros(Int,7,7)
    T[2,1] = -1  # [112] -> -E13
    T[1,2] = 1   # [113] ->  E12
    T[4,3] = 1   # [122] ->  E23
    T[7,4] = -1  # [123] -> -H
    T[6,5] = -1  # [133] -> -E32
    T[3,6] = -1  # [223] -> -E21
    T[5,7] = 1   # [233] ->  E31
    modp.(T)
end

function evaluate_poly_matrix(A, λ::Int)
    rows, cols, _ = size(A)
    M = zeros(Int,rows,cols)
    for i in 1:rows, j in 1:cols
        value = 0
        power = 1
        for d in 0:MAX_DEGREE
            value = modp(value + A[i,j,d+1] * power)
            power = modp(power * λ)
        end
        M[i,j] = value
    end
    M
end

function rank_mod(A::Matrix{Int})
    R = modp.(copy(A))
    rows, cols = size(R)
    rank = 0
    pivot_row = 1
    for col in 1:cols
        pivot_row > rows && break
        pivot = findfirst(r -> R[r,col] != 0, pivot_row:rows)
        pivot === nothing && continue
        row = pivot_row - 1 + pivot
        R[pivot_row,:], R[row,:] = copy(R[row,:]), copy(R[pivot_row,:])
        if R[pivot_row,col] == 2
            R[pivot_row,:] .= modp.(2 .* R[pivot_row,:])
        end
        for r in 1:rows
            if r != pivot_row && R[r,col] != 0
                factor = R[r,col]
                R[r,:] .= modp.(R[r,:] .- factor .* R[pivot_row,:])
            end
        end
        rank += 1
        pivot_row += 1
    end
    rank
end

function orbit_span_dimension(generators::Vector{Matrix{Int}}, v::Vector{Int})
    basis = reshape(modp.(v),:,1)
    while true
        candidates = [basis]
        for g in generators
            push!(candidates, modp.(g*basis))
        end
        joined = hcat(candidates...)
        # Select independent columns greedily.
        selected = zeros(Int,size(joined,1),0)
        current_rank = 0
        for c in 1:size(joined,2)
            trial = hcat(selected, joined[:,c])
            new_rank = rank_mod(trial)
            if new_rank > current_rank
                selected = trial
                current_rank = new_rank
            end
        end
        size(selected,2) == size(basis,2) && return size(basis,2)
        basis = selected
    end
end

function main()
    T = intertwiner()
    @assert rank_mod(T) == 7

    generator_reports = Any[]
    numeric_generators = Matrix{Int}[]
    for i in 1:3, j in 1:3
        i == j && continue
        U = elementary_poly(i,j,1)
        Uinv = elementary_poly(i,j,-1)
        source = kernel_action(U)
        target = conjugation_action(U,Uinv)
        lhs = poly_matrix_mul(poly_matrix_from_constant(T), source)
        rhs = poly_matrix_mul(target, poly_matrix_from_constant(T))
        difference = modp.(lhs .- rhs)
        max_nonzero_degree = -1
        for d in 0:MAX_DEGREE
            any(difference[:,:,d+1] .!= 0) && (max_nonzero_degree = d)
        end
        @assert max_nonzero_degree == -1
        source_degree = maximum(
            [d for d in 0:MAX_DEGREE if any(source[:,:,d+1] .!= 0)]; init=0
        )
        target_degree = maximum(
            [d for d in 0:MAX_DEGREE if any(target[:,:,d+1] .!= 0)]; init=0
        )
        push!(generator_reports, Dict(
            "i"=>i, "j"=>j,
            "source_action_degree"=>source_degree,
            "target_action_degree"=>target_degree,
            "intertwiner_identity"=>true
        ))
        push!(numeric_generators, evaluate_poly_matrix(source,1))
    end

    all_distinct = zeros(Int,7)
    all_distinct[4] = 1
    cyclic_dimension = orbit_span_dimension(numeric_generators,all_distinct)
    @assert cyclic_dimension == 7

    output = Dict(
        "field_characteristic" => 3,
        "source_basis" => ["[112]","[113]","[122]","[123]","[133]","[223]","[233]"],
        "target_basis" => ["E12","E13","E21","E23","E31","E32","H"],
        "intertwiner_columns" => [
            "[112] -> -E13", "[113] -> E12", "[122] -> E23",
            "[123] -> -H", "[133] -> -E32", "[223] -> -E21",
            "[233] -> E31"
        ],
        "intertwiner_rank" => rank_mod(T),
        "generator_reports" => generator_reports,
        "all_distinct_cyclic_span_dimension" => cyclic_dimension,
        "constant_kernel_dimension" => 7,
        "polynomial_identity_checked" => true,
        "maximum_parameter_degree_checked" => MAX_DEGREE,
        "claim_boundary" => (
            "Exact finite-dimensional polynomial-matrix certificate; the general polynomial-current-algebra kernel still requires a proof."
        )
    )
    open("experiments/constant_kernel_psl3_result.json","w") do io
        JSON.print(io,output,2)
    end
    println(JSON.json(output))
end

main()
