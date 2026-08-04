using JSON

mod3(x) = mod(x, 3)
mod9(x) = mod(x, 9)

function carry3(a::Int, c::Int)::Int
    mod3(-(a*a*c + a*c*c))
end

function wadd(x::Tuple{Int,Int}, y::Tuple{Int,Int})::Tuple{Int,Int}
    a, b = x
    c, d = y
    (mod3(a + c), mod3(b + d + carry3(a, c)))
end

naive_index(x::Tuple{Int,Int}) = mod9(x[1] + 3*x[2])
teich_index(x::Tuple{Int,Int}) = mod9(x[1]^3 + 3*x[2])

states = [(a,b) for a in 0:2 for b in 0:2]

cocycle_failures = Any[]
for a in 0:2, b in 0:2, c in 0:2
    lhs = mod3(carry3(a,b) + carry3(mod3(a+b), c))
    rhs = mod3(carry3(b,c) + carry3(a, mod3(b+c)))
    if lhs != rhs
        push!(cocycle_failures, Dict("a"=>a, "b"=>b, "c"=>c, "lhs"=>lhs, "rhs"=>rhs))
    end
end

associativity_failures = Any[]
for x in states, y in states, z in states
    lhs = wadd(wadd(x,y),z)
    rhs = wadd(x,wadd(y,z))
    if lhs != rhs
        push!(associativity_failures, Dict("x"=>x, "y"=>y, "z"=>z, "lhs"=>lhs, "rhs"=>rhs))
    end
end

naive_failures = Any[]
teich_failures = Any[]
for x in states, y in states
    sumxy = wadd(x,y)
    naive_lhs = naive_index(sumxy)
    naive_rhs = mod9(naive_index(x) + naive_index(y))
    if naive_lhs != naive_rhs
        push!(naive_failures, Dict("x"=>x, "y"=>y, "sum"=>sumxy,
                                   "phi_sum"=>naive_lhs, "sum_phi"=>naive_rhs))
    end
    teich_lhs = teich_index(sumxy)
    teich_rhs = mod9(teich_index(x) + teich_index(y))
    if teich_lhs != teich_rhs
        push!(teich_failures, Dict("x"=>x, "y"=>y, "sum"=>sumxy,
                                   "phi_sum"=>teich_lhs, "sum_phi"=>teich_rhs))
    end
end

orbit = Tuple{Int,Int}[]
x = (0,0)
for _ in 0:8
    push!(orbit, x)
    x = wadd(x, (1,0))
end
order_nine = x == (0,0) && length(unique(orbit)) == 9

# Exhaust the reduced total-degree <= 3 polynomial functions in two variables.
monomials = [(i,j) for i in 0:2 for j in 0:2 if i+j <= 3]
points = [(x,y) for x in 0:2 for y in 0:2]
minimum_support = 9
minimizer_count = 0
polynomial_count = 3^length(monomials)
for code in 1:(polynomial_count-1)
    coeffs = Int[]
    n = code
    for _ in monomials
        push!(coeffs, mod3(n))
        n = div(n,3)
    end
    support = 0
    for (x,y) in points
        value = 0
        for (coef,(i,j)) in zip(coeffs,monomials)
            value = mod3(value + coef * x^i * y^j)
        end
        support += value != 0
    end
    if support < minimum_support
        minimum_support = support
        minimizer_count = 1
    elseif support == minimum_support
        minimizer_count += 1
    end
end

result = Dict(
    "state_count" => length(states),
    "pair_count" => length(states)^2,
    "cocycle_failure_count" => length(cocycle_failures),
    "associativity_failure_count" => length(associativity_failures),
    "naive_coordinate_failure_count" => length(naive_failures),
    "naive_first_counterexample" => isempty(naive_failures) ? nothing : first(naive_failures),
    "teichmueller_coordinate_failure_count" => length(teich_failures),
    "teichmueller_formula" => "phi(a,b) = (a^3 + 3b) mod 9",
    "generator_orbit" => orbit,
    "generator_has_order_nine" => order_nine,
    "degree_three_two_variable_monomials" => monomials,
    "degree_three_two_variable_polynomial_count" => polynomial_count,
    "degree_three_two_variable_minimum_support" => minimum_support,
    "degree_three_two_variable_minimizer_count" => minimizer_count,
    "claim_boundary" => "Exhaustive finite computation; not a substitute for the Lean family proof."
)

open("experiments/ternary_witt_exhaustive_result.json", "w") do io
    JSON.print(io, result, 2)
end

println(JSON.json(result))

@assert isempty(cocycle_failures)
@assert isempty(associativity_failures)
@assert !isempty(naive_failures)
@assert isempty(teich_failures)
@assert order_nine
@assert minimum_support == 2
