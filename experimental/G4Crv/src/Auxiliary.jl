
#We should instead write a generic point finding algorithm using
#Noether normalization
function _find_points_on_projective_hyper_surface(S)
  I = radical(defining_ideal(S))
  @req length(gens(I)) == 1 "Input should be a hypersurface cut out by one equation."
  f = I[1]
  R_p = parent(f)

  points = Set{Vector{FqFieldElem}}([])
  n = number_of_generators(R_p)
  K = base_ring(R_p)

  Kn = Iterators.product(repeat([K], n-1)...)

  Rx, x = polynomial_ring(K, :x)
  for v in Kn
    poly = f(x, v...)
    if !is_zero(poly)
      ys = roots(K, poly)
      for y in ys
        y = K(y)
        if !all(is_zero, vcat([y], [v...]))
          push!(points, vcat([y], [v...]))
        end
      end
    else
      push!(points, vcat([one(K)], [v...]))
    end
  end
return collect(points)
end


function _ZZ_parametrization(line)
  I = defining_ideal(line)
  R_p = base_ring(I)
  S, (s, t) = polynomial_ring(ZZ,  [:s,:t])
  par = kernel(map(x-> lift(ZZ, x), transpose(matrix([[coeff(I[j], gens(R_p)[i]) for i in (1:4)] for j in [1,2]]))))
  return [s*par[1,i] + t*par[2,i] for i in (1:4)]
end

function _parametrization(line)
  I = defining_ideal(line)
  R_p = base_ring(I)
  F = base_ring(R_p)
  S, (s, t) = polynomial_ring(F,  [:s,:t])
  par = kernel(transpose(matrix([[coeff(I[j], gens(R_p)[i]) for i in (1:4)] for j in [1,2]])))
  return [s*par[1,i] + t*par[2,i] for i in (1:4)]
end

function is_on_scheme(v::Vector, X::ProjectiveScheme)
  return all([iszero(evaluate(f, v)) for f in gens(defining_ideal(X))])
end

