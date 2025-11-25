import math
import random


p = 2**127 - 1      # Mersenne
F = lambda x: x % p

'''
witness: x
output: x^2 = 25

We should proof that we know x as x^2 = 25
'''


# I. Arithmetization (R1CS Rank 1 Constraint System)
# witness: x; vector = [1, x, x^2]
# R1CS build : <A_i, w> * <B_i, w> = <C_i, w>

# Constraint 1: x*x = x^2
# Constraint 1: x^2 = 25

A = [
    [0, 1, 0],
    [0, 0, 1]
]
B = [
    [0, 1, 0],
    [1, 0, 0]
]
C = [
    [0, 0, 1],
    [0, 0, 0]
]

K = [0, 25]

N_CONSTRAINTS = 2
N_VARS = 3

print("R1CS ")
print("- 2 constraints")
print("- 3 vars (1, x, x^2) -> vector")
print("A:", A)
print("B:", B)
print("C:", C)
print("K:", K)


def check_r1cs(x, nb_constraint=2, nb_var=3):
    w = [1, F(x), F(x*x)]

    for i in range(nb_constraint):
        A_dot = sum(A[i][j] * w[j] for j in range(nb_var))
        B_dot = sum(B[i][j] * w[j] for j in range(nb_var))
        C_dot = sum(C[i][j] * w[j] for j in range(nb_var)) + K[i]

        print(f"Constraint {i+1}:  {A_dot} * {B_dot} =? {C_dot}")

        if A_dot * B_dot != C_dot:
            print("R1CS invalid")
            return False
    
    print("R1CS valid")
    return True

check_r1cs(4, N_CONSTRAINTS, N_VARS)
print("-----")
check_r1cs(5, N_CONSTRAINTS, N_VARS)
print("-----")
check_r1cs(7, N_CONSTRAINTS, N_VARS)


# II. Constraints to polynomial ( R1CS -> QAP Quadratic Arithmetic Program) 
# Transform linear constraints to a unique polynomial, verifiable with an single secret point

def lagrange_basis(i, n):
    def poly(t): #closure func
        num = 1
        den = 1
        for j in range(1, n+1):
            if j != i:
                num = F(num * (t-j))
                den = F(den * (i-j))
        return F(num * pow(den, -1, p))
    return poly

L = [lagrange_basis(i, N_CONSTRAINTS) for i in range(1, N_CONSTRAINTS+1)]

print("Constructed basic Lagrange polynomials.")

def poly_from_R1CS_vector(vec):
    """Build a polynomial (N_CONSTRAINTS-1) from L_i."""
    def poly(t):
        acc = 0
        for i in range(N_CONSTRAINTS):
            acc = F(acc + vec[i] * L[i](t))
        return acc
    return poly

A_poly = [poly_from_R1CS_vector([A[i][j] for i in range(N_CONSTRAINTS)]) for j in range(N_VARS)]
B_poly = [poly_from_R1CS_vector([B[i][j] for i in range(N_CONSTRAINTS)]) for j in range(N_VARS)]
C_poly = [poly_from_R1CS_vector([C[i][j] for i in range(N_CONSTRAINTS)]) for j in range(N_VARS)]
K_poly = poly_from_R1CS_vector(K)

print("Polynomials A(t), B(t), C(t), K(t) generated.")


# III. Parameters setup

tau = random.randint(1, p-1)

print("tau =", tau)

tau_powers = [pow(tau, i, p) for i in range(10)]
print(tau_powers)


# IV. Proof gen

def gen_proof(x):
    # Witness:
    w = [1, F(x), F(x*x)]

    def eval_poly_set(poly_set):
        return sum( poly_set[i](tau) * w[i] for i in range(3) ) % p

    At = eval_poly_set(A_poly)
    Bt = eval_poly_set(B_poly)
    Ct = eval_poly_set(C_poly)
    Kt = K_poly(tau)

    # Q(t) = A(t)B(t) - C(t) - K(t)
    Qt = F(At * Bt - Ct - Kt)

    # Z(t) = (t-1)(t-2)
    Zt = F((tau-1)*(tau-2))

    Ht = F(Qt * pow(Zt, -1, p))

    return (At, Bt, Ht)

secret_x = 5  # for 5^2 = 25
proof = gen_proof(secret_x)

print("Proof generated :", proof)


# V. Verification
def verify_proof(proof, x):
    At, Bt, Ht = proof
    w = [1, F(x), F(x*x)]

    Ct = sum(C_poly[j](tau) * w[j] for j in range(3)) % p
    Kt = K_poly(tau)
    Zt = F((tau - 1)*(tau - 2))

    LHS = F(At * Bt - Ct - Kt)
    RHS = F(Ht * Zt)

    print("LHS =", LHS)
    print("RHS =", RHS)

    return LHS == RHS


is_valid = verify_proof(proof, secret_x)
print("Proof valid?", is_valid)