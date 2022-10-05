import analysis.special_functions.pow

theorem schur_inequality (x y z t : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) (ht : t > 0) :
  x^t * (x - y) * (x - z) + y^t * (y - z) * (y - x) + z^t * (z - x) * (z - y) ≥ 0 := sorry