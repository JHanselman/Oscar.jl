#= 
[ES24] Minimization of hypersurfaces, A.-S. Elsenhans and M. Stoll, Mathematics of Computation
=#

function minimize_and_reduce_plane_curve(F::MPolyRingElem{ZZRingElem})
  F, T = minimize_plane_curve(F)
  F, T1 = adhoc_reduce_plane_curve(F)
  return F, T * T1
end
function minimize_and_reduce_plane_curve(F::MPolyRingElem{QQFieldElem})
  return minimize_and_reduce_plane_curve(clear_denominators(F))
end

function minimize_plane_curve(F::MPolyRingElem{QQFieldElem}) 
  return minimize_plane_curve(clear_denominators(F))
end

function clear_denominators(F::MPolyRingElem{QQFieldElem})
  mu = lcm(map(denominator, collect(coefficients(F))))
  F *= mu
  return change_coefficient_ring(ZZ, F)
end

function minimize_plane_curve(F::MPolyRingElem{ZZRingElem}) 
  R = parent(F)
  @req is_homogeneous(F) && number_of_generators(R) == 3 "Input needs to be a homogeneous ternary form."
  bad_primes = find_bad_primes_plane_curve(F)
  T = identity_matrix(ZZ, 3)
  for p in bad_primes
    F, T1, e = minimize_plane_curve(F, p)
    T = T * T1
  end
  return F, T
end

function minimize_plane_curve(F::MPolyRingElem{ZZRingElem}, p::ZZRingElem)
  T = identity_matrix(ZZ, 3)
  e = valuation(content(F), p)
  G = F/p^e
  success, G, T1, e1 = minimize_plane_curve_one_step(G, p)
  while success 
    T = T * T1
    e = e + e1 
    success, G, T1, e1 = minimize_plane_curve_one_step(G, p)
  end
  return G, T, e
end

function minimize_plane_curve_one_step(F::MPolyRingElem{ZZRingElem}, p::ZZRingElem)
  d = total_degree(F)

  function _recurse(F::MPolyRingElem{ZZRingElem}, r::Int, gamma::Int, T0::ZZMatrix)
    K = GF(p)
    if gamma < 0
      return true, F, T0, ZZ(0)
    end

    if is_zero(change_base_ring(K, T0)) || r<= 0
      return false, F, T0, ZZ(0)
    end

    Fp = change_coefficient_ring(K, F)
    fac = factor(Fp)
    L = []
    R = parent(Fp)
    X = gens(R)
    G = one(R)

    for (f,e) in fac
      if total_degree(f) == 1
        push!(L, (f,e))
      else
        G *= f^e
      end
    end

    for l in L
      P = [coeff(l[1], X[i]) for i in (1:3)]
      #Ensure equation is monic in x
      j = findfirst(isone, P)
      P = swap_rows(matrix(P), 1, j)
      #Complete basis by adding [0,1,0] and [0,0,1]
      M = Hecke.complete_to_basis(transpose(matrix(P)))
      #Swap back to undo the change made in swap_rows
      swap_cols!(M, 1, j)

      #Following [ES24] we want to find a map that maps l to lambda*z for some z
      #So we move P to the last row. 
      swap_rows!(M, 1, 3)

      #Invert to get the correct map
      T = inv(map(x->lift(ZZ,x), M))
      if l[2] <= d//3
        x, y, z = gens(R)
        TF_p = transformation_GLn(Fp, change_base_ring(K, T))/z^l[2]
        facs = factor(TF_p(x, y, zero(R)))
        test = any([total_degree(f) == 1 && e>= (d - 3*l[2])//2 for (f, e) in facs])
        if !test
          continue
        end
      end
      F1, e = apply_weight(F, T, [0,0,1], p)
      M001 = diagonal_matrix(ZZ, [1,1,p])
      success, F2, T1, e1 = _recurse(F1, r-1, gamma + d - 3*e, T0 * T * M001)
      if success
        return true, F2, T1, e + e1
      end
    end
    R_p = parent(G)
    R_p, _ = grade(R_p)
    G = R_p(G)
    dG = total_degree(G)
    partial_derivs = [Set([G])]
    for i in (1:div(dG,2))
      part_derivs_i = Set([])
      for f in partial_derivs[i]
        for j in (1:3)
          push!(part_derivs_i, derivative(f, j))
        end
      end
      push!(partial_derivs, part_derivs_i)
    end
    I = collect(union(partial_derivs...))
    sing_points = projective_scheme(ideal(R_p, I))
    if dim(sing_points) == 1
      points = _find_points_on_projective_hyper_surface(sing_points)
    else
      sing_points = algebraic_set(ideal(R_p, I))
      #Ensure the set is non-empty
      points = []
      if dim(sing_points) == 0
        points = rational_points(Vector, sing_points)
      end
    end

    filter!(x-> !any([is_on_scheme(x, projective_scheme(ideal(R_p,l[1]))) for l in L]), points)
    if is_empty(points)
      return false, F, T0, ZZ(0)
    end
    P = points[1]
    T = transpose(map(x->lift(ZZ,x), Hecke.complete_to_basis(transpose(matrix(P)))))
    F1, e = apply_weight(F, T, [0,1,1], p)
    M011 = diagonal_matrix(ZZ, [1,p,p])
    success, F2, T1, e1 = _recurse(F1, r - 2, gamma + 2*d - 3*e, T0 * T * M011)
    if success
      return true, F2, T1, e + e1 
    end

    return false, F, T0, ZZ(0)
  end
  #TODO set 2*d-1 to be something else.
  return _recurse(F, 2*d-1, 0, identity_matrix(ZZ, 3))
end

#=
Following [ES24] Paragraph 8
When deg F is even, then I1(F) = transvectant([F,F,F], d) is (generically) 
a non-zero invariant, and G = transvectant([F,F,F], d-2) is a sextic covariant. 
So I2(F) = transvectant([G,G,G], 6) is another invariant. GCD of these invariants can
be used to find bad primes.

When deg F is odd, then G = transvectant([F,F,F], d-1)
is a cubic covariant of F. We can take the invariants J4, J6 of G.
=#
function find_bad_primes_plane_curve(F::MPolyRingElem{ZZRingElem})
  d = total_degree(F)
  if is_even(d)
    S = transvectant_sequence([F, F, F], d)
    I1F = S[d]
    G = S[d-2]
    S2 = transvectant_sequence([G, G, G], 6)
    I2F = S2[6]
    N = gcd(content(I1F), content(I2F))
  else
    S = transvectant_sequence([F, F, F], d-1)
    G = S[d-1]
    c4, c6 = c_invariants(G)
    disc = c4^3−c6^2/1728
    N = gcd(c4, c6, disc)
  end
  return prime_divisors(N)
end

function adhoc_reduce_plane_curve(F::MPolyRingElem)
  I = identity_matrix(ZZ, 3)
  test_matrix_basis = [I]
  for i in (1:3)
    for j in (i:3)
      if i != j
        M = identity_matrix(ZZ,3)
        M[i,j] = 1
        push!(test_matrix_basis, M)
        push!(test_matrix_basis, transpose(M))
      end
    end
  end

  test_matrix_basis = vcat(test_matrix_basis, map(inv, test_matrix_basis))
  test_matrices = Set{ZZMatrix}([])

  for (M1, M2, M3) in Iterators.product(test_matrix_basis, test_matrix_basis, test_matrix_basis)
    M = M1 * M2 * M3
    push!(test_matrices, M)
  end

  min = ternary_form_size(F)
  T0 = identity_matrix(ZZ, 3)

  while true
    improvement = false
    for T in test_matrices
      F_new = transformation_GLn(F, T)
      size = ternary_form_size(F_new)
      if size < min 
        T0 = T0 * T
        min = size 
        F = F_new
        improvement = true
      end
    end

    if !improvement
      break 
    end
    return F, T0
  end
end

function ternary_form_size(F::ZZMPolyRingElem)
  return sum(map(x-> x^2, collect(coefficients(F)));init = zero(ZZ))
end

function apply_weight(F::MPolyRingElem{ZZRingElem}, T::ZZMatrix, w::Vector{Int}, p::ZZRingElem)
  F1 = transformation_GLn(F, T)
  R = parent(F1)
  X = gens(R)
  F2 = F1([X[i]*p^w[i] for i in (1:length(X))]...)
  e = valuation(content(F2), p)
  return F2/p^e, e
end
