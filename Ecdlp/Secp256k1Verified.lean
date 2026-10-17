namespace Secp256k1

def p : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
def n : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
def lam : Nat := 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
def beta : Nat := 0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE

theorem p_special_form : p = 2^256 - 2^32 - 977 := by native_decide

theorem glv_lambda_eigenvalue : (lam^2 + lam + 1) % n = 0 := by native_decide

theorem lambda_is_cube_root : lam^3 % n = 1 := by native_decide

theorem lambda_ne_one : lam ≠ 1 := by native_decide

theorem beta_field_eigenvalue : (beta^2 + beta + 1) % p = 0 := by native_decide

theorem beta_is_cube_root : beta^3 % p = 1 := by native_decide

theorem lam_lt_n : lam < n := by native_decide
theorem beta_lt_p : beta < p := by native_decide


def Gx : Nat := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
def Gy : Nat := 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

/-- The secp256k1 base point `G = (Gx, Gy)` satisfies the curve equation
`y² = x³ + 7` (mod `p`). -/
theorem generator_on_curve : (Gy ^ 2) % p = (Gx ^ 3 + 7) % p := by native_decide

end Secp256k1
