import random
import sympy

# ------------------------------
# Field
# ------------------------------
p = 2**127 - 1
F = lambda x: x % p

# Fake bilinear group
g = 9
def Gexp(x):
    return pow(g, x % p, p)

def pairing_exp(a, b):
    return (a * b) % p

# ------------------------------
# R1CS: x^2 = 25
# ------------------------------
# Constraints: (1) x^2 - 25 = 0
# Using variables: w0 = 1 (constant), w1 = x, w2 = x^2
A = [
    [0, 0, 1],  # A1: x
]
B = [
    [1, 0, 0],  # B1: x
]
C = [
    [0, 0, 0],  # C1: x^2
]
K = [25]        # constant term

N_CONSTRAINTS = 1
N_VARS = 3

# ------------------------------
# Lagrange basis
# ------------------------------
def lagrange_basis(i, n):
    X = sympy.symbols('X')
    basis = 1
    for j in range(1, n+1):
        if j != i:
            basis *= (X - j) / (i - j)
    return sympy.simplify(basis)

L = [lagrange_basis(i+1, N_CONSTRAINTS) for i in range(N_CONSTRAINTS)]

def poly_from_R1CS_vector(vec):
    X = sympy.symbols('X')
    poly = sum(vec[i] * L[i] for i in range(N_CONSTRAINTS))
    return sympy.simplify(poly)

A_poly = [poly_from_R1CS_vector([A[i][j] for i in range(N_CONSTRAINTS)]) for j in range(N_VARS)]
B_poly = [poly_from_R1CS_vector([B[i][j] for i in range(N_CONSTRAINTS)]) for j in range(N_VARS)]
C_poly = [poly_from_R1CS_vector([C[i][j] for i in range(N_CONSTRAINTS)]) for j in range(N_VARS)]
K_poly = poly_from_R1CS_vector(K)

# ------------------------------
# Public evaluation points
# ------------------------------
tau = random.randint(1, p-1)
Z_poly = (sympy.symbols('X') - 1)*(sympy.symbols('X') - 2)  # roots at constraints

# ------------------------------
# Compute H(X) properly
# ------------------------------
X = sympy.symbols('X')
Q_poly = sum(A_poly[j]*B_poly[j] for j in range(N_VARS)) - sum(C_poly[j] for j in range(N_VARS)) - K_poly
H_poly = sympy.simplify(Q_poly / Z_poly)  # division polynomiale

# ------------------------------
# Prover
# ------------------------------
def prove(x):
    w = [1, F(x), F(x*x)]

    def eval_poly(poly_list):
        return F(sum(F(poly_list[j].subs(X, tau)) * w[j] for j in range(N_VARS)))

    At = F(int(eval_poly(A_poly)))
    Bt = F(int(eval_poly(B_poly)))
    Ct = F(int(eval_poly(C_poly)))
    Kt = F(int(K_poly.subs(X, tau)))
    Ht = F(int(H_poly.subs(X, tau)))
    Zt = F(int(Z_poly.subs(X, tau)))


    # commitments
    piA = Gexp(At)
    piB = Gexp(Bt)
    piC = Gexp(Ht)

    public_input = F(Ct + Kt)

    return {
        "piA": piA, "Aexp": At,
        "piB": piB, "Bexp": Bt,
        "piC": piC, "Hexp": Ht,
        "public": public_input,
        "Zexp": Zt
    }

# ------------------------------
# Verifier
# ------------------------------
def verify(proof):
    lhs = pairing_exp(proof["Aexp"], proof["Bexp"])
    rhs = F(proof["Hexp"] * proof["Zexp"] + proof["public"])

    print("LHS =", lhs)
    print("RHS =", rhs)
    return lhs == rhs

# ------------------------------
# Test
# ------------------------------
print("Testing correct x = 5")
proof = prove(5)
print(proof)
print("Valid proof ?", verify(proof))

print("\nTesting wrong x = 9")
proof = prove(9)
print(proof)
print("Valid proof ?", verify(proof))


