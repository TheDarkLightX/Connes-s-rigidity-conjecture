using JSON

const RESULT_PATH = joinpath(@__DIR__, "prime_rank_detector_result.json")

function trimpoly(a::Vector{Int})
    b = copy(a)
    while !isempty(b) && b[end] == 0
        pop!(b)
    end
    return b
end

function polyrem(a::Vector{Int}, b::Vector{Int}, p::Int)
    r = trimpoly(a)
    d = trimpoly(b)
    isempty(d) && error("polynomial division by zero")
    invlead = powermod(d[end], p - 2, p)
    while !isempty(r) && length(r) >= length(d)
        shift = length(r) - length(d)
        factor = mod(r[end] * invlead, p)
        for j in eachindex(d)
            index = shift + j
            r[index] = mod(r[index] - factor * d[j], p)
        end
        r = trimpoly(r)
    end
    return r
end

function polygcd(a::Vector{Int}, b::Vector{Int}, p::Int)
    x = trimpoly(a)
    y = trimpoly(b)
    while !isempty(y)
        x, y = y, polyrem(x, y, p)
    end
    isempty(x) && return x
    invlead = powermod(x[end], p - 2, p)
    return [mod(invlead * c, p) for c in x]
end

function decode_polynomial(index::Int, p::Int, n::Int)
    coefficients = zeros(Int, n)
    value = index
    for j in 1:n
        coefficients[j] = mod(value, p)
        value = div(value, p)
    end
    return coefficients
end

function brute_primitive_count(p::Int, r::Int, n::Int)
    polynomials = [decode_polynomial(i, p, n) for i in 0:(p^n - 1)]
    count = 0
    for vector in Iterators.product(ntuple(_ -> polynomials, r)...)
        divisor = Int[]
        for polynomial in vector
            divisor = polygcd(divisor, polynomial, p)
        end
        count += length(divisor) == 1
    end
    return count
end

function predicted_primitive_count(p::Int, r::Int, n::Int)
    return big(p)^(r * n) - big(p)^(r * n - r + 1) + p - 1
end

function detector_constant(p::Int, r::Int)
    support = Rational{BigInt}(p - 1, big(p)^2)
    nonprimitive = Rational{BigInt}(1, big(p)^(r - 1))
    return (support - nonprimitive) / (1 - nonprimitive)
end

function chart_constant(p::Int, r::Int)
    r > p || return Rational{BigInt}(0, 1)
    return Rational{BigInt}((r - p) * (p - 1), big(r) * big(p)^2)
end

function reed_muller_support(p::Int, d::Int)
    a, b = divrem(d, p - 1)
    return Rational{BigInt}(p - b, big(p)^(a + 1))
end

function degree_primitive_constant(p::Int, r::Int, d::Int)
    support = reed_muller_support(p, d)
    nonprimitive = Rational{BigInt}(1, big(p)^(r - 1))
    return (support - nonprimitive) / (1 - nonprimitive)
end

function degree_chart_constant(p::Int, r::Int, d::Int)
    r > d || return Rational{BigInt}(0, 1)
    return Rational{BigInt}(r - d, r) * reed_muller_support(p, d)
end

function rational_string(x::Rational{BigInt})
    denominator(x) == 1 && return string(numerator(x))
    return string(numerator(x), "/", denominator(x))
end

phase_cases = [(2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (5, 3), (7, 3)]
phase_table = []
for (p, r) in phase_cases
    c = detector_constant(p, r)
    push!(phase_table, Dict(
        "prime" => p,
        "rank" => r,
        "constant" => rational_string(c),
        "positive" => c > 0,
        "phase_expression" => (p - 1) * big(p)^(r - 3),
    ))
end

expected = Dict(
    (2, 3) => "0",
    (2, 4) => "1/7",
    (2, 5) => "1/5",
    (3, 3) => "1/8",
    (3, 4) => "5/26",
    (5, 3) => "1/8",
    (7, 3) => "5/48",
)
for row in phase_table
    @assert row["constant"] == expected[(row["prime"], row["rank"])]
    @assert row["positive"] == (row["phase_expression"] > 1)
end

chart_cases = [(2, 3), (2, 4), (2, 5), (3, 4), (3, 5)]
chart_expected = Dict(
    (2, 3) => "1/12",
    (2, 4) => "1/8",
    (2, 5) => "3/20",
    (3, 4) => "1/18",
    (3, 5) => "4/45",
)
chart_table = []
for (p, r) in chart_cases
    c = chart_constant(p, r)
    @assert rational_string(c) == chart_expected[(p, r)]
    push!(chart_table, Dict(
        "prime" => p,
        "rank" => r,
        "constant" => rational_string(c),
        "nonzero_charts" => r - p,
        "total_charts" => r,
    ))
end

coverage_checks = []
for p in [2, 3, 5, 7, 11], r in 3:8
    primitive = detector_constant(p, r)
    chart = chart_constant(p, r)
    @assert primitive > 0 || chart > 0
    push!(coverage_checks, Dict(
        "prime" => p,
        "rank" => r,
        "primitive_constant" => rational_string(primitive),
        "chart_constant" => rational_string(chart),
        "best_constant" => rational_string(max(primitive, chart)),
    ))
end

degree_cases = [(2, 1, "1/2"), (2, 2, "1/4"),
                (3, 1, "2/3"), (3, 2, "1/3"),
                (3, 3, "2/9"), (3, 4, "1/9"),
                (5, 5, "4/25")]
degree_rank_checks = []
for (p, d, expected_support) in degree_cases
    support = reed_muller_support(p, d)
    @assert rational_string(support) == expected_support
    for r in max(3, d):max(4, d + 1)
        primitive = degree_primitive_constant(p, r, d)
        chart = degree_chart_constant(p, r, d)
        push!(degree_rank_checks, Dict(
            "prime" => p,
            "degree" => d,
            "rank" => r,
            "reed_muller_support" => rational_string(support),
            "primitive_constant" => rational_string(primitive),
            "chart_constant" => rational_string(chart),
        ))
    end
end

primitive_cases = [(2, 3, 1), (2, 3, 2), (2, 4, 2),
                   (3, 3, 1), (3, 3, 2), (5, 3, 2)]
primitive_checks = []
for (p, r, n) in primitive_cases
    brute = brute_primitive_count(p, r, n)
    predicted = predicted_primitive_count(p, r, n)
    @assert brute == predicted
    push!(primitive_checks, Dict(
        "prime" => p,
        "rank" => r,
        "box_length" => n,
        "brute_count" => brute,
        "formula_count" => predicted,
        "total_vectors" => big(p)^(r * n),
    ))
end

result = Dict(
    "status" => "passed",
    "phase_table" => phase_table,
    "chart_table" => chart_table,
    "coverage_checks" => coverage_checks,
    "degree_rank_checks" => degree_rank_checks,
    "primitive_count_checks" => primitive_checks,
    "constant_formula" => "((p-1)/p^2-p^(1-r))/(1-p^(1-r))",
    "chart_constant_formula" => "(r-p)*(p-1)/(r*p^2) for p<r",
    "degree_support_formula" => "if d=a*(p-1)+b with 0<=b<p-1, then (p-b)/p^(a+1)",
    "positive_iff" => "(p-1)*p^(r-3)>1",
)

open(RESULT_PATH, "w") do io
    JSON.print(io, result, 2)
    println(io)
end

println(JSON.json(result))
