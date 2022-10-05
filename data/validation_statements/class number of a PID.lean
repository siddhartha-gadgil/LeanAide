import ring_theory.principal_ideal_domain
import ring_theory.dedekind_domain.basic
import number_theory.class_number.number_field

theorem number_field.class_number_eq_one_iff_ {K : Type*} [field K] [number_field K] :
number_field.class_number K = 1 ↔ is_principal_ideal_ring (number_field.ring_of_integers K) := sorry