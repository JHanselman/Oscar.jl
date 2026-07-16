function a_invariants(F::MPolyRingElem)
  R = parent(F)
  x, y, z = gens(R)
  @req is_homogeneous(F) && number_of_generators(R) == 3 && total_degree(F) == 3 "Input needs to be a homogeneous ternary cubic."
  a = coeff(F, x^3)
  b = coeff(F, y^3)
  c = coeff(F, z^3)
  d = coeff(F, x^2*y)
  e = coeff(F, x^2*z)
  f = coeff(F, x*y^2)
  g = coeff(F, y^2*z)
  h = coeff(F, x*z^2)
  i = coeff(F, y*z^2)
  m = coeff(F, x*y*z)
  a1 = m
  a2 = -(d*i + e*g + f*h);
  a3 = 9*a*b*c - (a*g*i + b*e*h + c*d*f) - (d*g*h + e*f*i)
  a4 = -3*(a*b*h*i + a*c*f*g  + b*c*d*e) + a*(f*i^2 + g^2*h) +
      b*(d*h^2 + e^2*i) + c*(d^2*g + e*f^2) + d*i*e*g + f*h*d*i + e*g*f*h
  a6 = a*b*c*(-27*a*b*c + 9*(a*g*i + c*d*f + b*e*h) + m^3) +
   3*a*b*c*((d*g*h + e*f*i) - (d*i + e*g + f*h)*m) - a^2*(b*i^3 + c*g^3) - 
   b^2*(c*e^3 + a*h^3) - c^2*(a*f^3 + b*d^3) + 
   (a*b*h*i + b*c*d*e + a*c*f*g)*(2*(d*i + e*g + f*h) - m^2) - 
   3*(a*b*e*g*h*i + b*c*d*e*f*h + a*c*d*f*g*i) - a*((f*h + d*i)*g^2*h +
   (h*f + e*g)*f*i^2) - b*((i*d + e*g)*h^2*d + (d*i + f*h)*i*e^2) - 
   c*((e*g + f*h)*d^2*g + (g*e + d*i)*e*f^2) - d*e*f*g*h*i +
   a*b*(e*i^2 + g*h^2)*m + b*c*(d^2*h + e^2*f)*m + a*c*(d*g^2 + f^2*i)*m +
  (a*f*g*h*i + b*d*e*h*i + c*d*e*f*g)*m
  return a1, a2, a3, a4, a6
end

function b_invariants(F::MPolyRingElem)
  a1, a2, a3, a4, a6 = a_invariants(F)
  return Hecke._ellcrv_b_invariants(a1, a2, a3, a4, a6)
end

function c_invariants(F::MPolyRingElem)
  b2, b4, b6, b8 = b_invariants(F)
  return Hecke._ellcrv_c_invariants(b2, b4, b6, b8)
end 