##################################################
# RING-LWE ATTACK #
##################################################

# General preparation of Sage: Create a polynomial ring and import GaussianSampler, Timer
P.<y> = PolynomialRing(RationalField(), 'y')
from sage.stats.distributions.discrete_gaussian_lattice import DiscreteGaussianDistributionLatticeSampler
RP = RealField(300) # sets the precision
from sage.doctest.util import Timer

# Give the Minkowski lattice for a given ring determined by a polynomial.
def cmatrix(): 
    global N, a
    N.<a> = NumberField(f)
    fdeg = f.degree()
    key = [0 for i in range(fdeg)] # 0 = real, 1 = real part, 2 = imaginary part
    embs = N.embeddings(CC)
    M = matrix(RP, fdeg, fdeg)
    
    print("Preparing an embedding matrix: computing powers of the root.")
    apows = [a^j for j in range(n)]
    print("Finished computing the powers of the root.")
    
    i = 0
    while i < n:
        em = embs[i]
        if Mod(i, 20) == 0:
            print(f"Embedding matrix: {i} rows out of {n} complete.")
        
        if em(a).imag() == 0:
            key[i] = 0
            for j in range(n):
                M[i, j] = em(apows[j]).real()
            i = i + 1
        else:
            key[i] = 1
            key[i+1] = 2
            for j in range(n):
                M[i, j] = em(apows[j]).real()
                M[i+1, j] = (em(apows[j]) * I).real()
            i = i + 2
    return M, key

# Produce a random vector from (Z/qZ)^n
def random_vec(q, dim):
    return vector([ZZ.random_element(0, q) for i in range(dim)])

# Useful function for real numbers modulo q
def modq(r, q):
    t = r/q - floor(r/q)
    return t*q

# Call sampler
def call_sampler():
    e = sampler().change_ring(RP)
    return e

# Create samples using a lattice
def get_sample(latmat, latmatinv, sec, qval, keyval):
    e = call_sampler() 
    dim = latmat.dimensions()[0]
    pre_a = random_vec(qval, dim)
    a_vec = latmat * pre_a 
    b_vec = vecmul_poly(a_vec, sec, latmat, latmatinv) + e
    pre_b = latmatinv * b_vec
    pre_b_red = vector([modq(c, qval) for c in pre_b])
    b_vec = latmat * pre_b_red
    return [a_vec, b_vec]

# Global choices: setup dummy values
q = 1
n = 1
sig = 1/sqrt(2*pi)
Zq = IntegerModRing(q)
R.<x> = PolynomialRing(Zq)
f = y + 1
N.<a> = NumberField(f)
S.<z> = R.quotient(f) 
cm, key = matrix(RP, 1, 1, [0]), []
cmi = cm

# Set the parameters for the attack
def setup_params(fval, qval, sval):
    global q, n, sig, f, S, x, z, Zq
    f = fval
    n = f.degree()
    q = qval
    Zq = IntegerModRing(q)
    R.<x> = PolynomialRing(Zq)
    sig = sval/sqrt(2*pi)
    S.<z> = R.quotient(f)
    print(f"Setting up parameters, poly = {f}, prime = {q}, sigma = {sig}")
    print("Verifying properties: ")
    print("Prime?", q.is_prime())
    print("Irreducible? ", f.is_irreducible())
    print("Value at 1 modulo q?", Mod(f.subs(y=1), q))
    return True

# Compute the lattices in Minkowski space
def prepare_matrices():
    global cm, key, cmi, cmqq
    print("Preparing matrices.")
    cm, key = cmatrix()
    cmi = cm.inverse()
    cm53 = cm.change_ring(RealField(10))
    cmqq = cm53.change_ring(QQ)
    print("All matrices prepared.")
    return True

# Make a vector in R^n into a polynomial
def make_poly(a_vec, matchange, var):
    coeffs = matchange * a_vec
    pol = 0
    for i in range(n):
        pol = pol + ZZ(round(coeffs[i])) * var^i
    return pol

# Make a polynomial into a vector in Minkowski space
def make_vec(fval, matchange):
    coeffs = [0 for i in range(n)]
    if fval != 0:
        colist = lift(fval).coefficients()
        for i in range(len(colist)):
            coeffs[i] = ZZ(colist[i])
    return matchange * vector(coeffs)

# Multiplication in Minkowski space
def vecmul_poly(u, v, mat, matinv):
    poly_u = make_poly(u, matinv, z)
    poly_v = make_poly(v, matinv, z)
    poly_prod = poly_u * poly_v
    return make_vec(poly_prod, mat)

def initiate_sampler():
    global sampler
    print("Initiating Sampler.")
    sampler = DiscreteGaussianDistributionLatticeSampler(cmqq.transpose(), sig)
    print(f"Sampler initiated with sigma {RDF(sig)}")
    return True

def error_test(num):
    print(f"Testing error production for {num} samples.")
    errorlist = [sampler().norm().n() for _ in range(num)]
    meannorm = mean(errorlist)
    maxnorm = max(errorlist)
    print(f"Avg error norm: {RDF(meannorm/(sqrt(n)*sampler.sigma*sqrt(2*pi)))} * sqrt(n)*s")
    return True

secret = 0
def create_secret():
    global secret
    secret = cm * random_vec(q, n)
    return True

samps = []
def create_samples(numsampsval):
    global samps
    samps = []
    print("Creating samples...")
    for i in range(numsampsval):
        samp = get_sample(cm, cmi, secret, q, key)
        samps.append(samp)
    print(f"Done creating {len(samps)} samples.")
    return True

def go_to_q(a_vec, matchange):
    pol = make_poly(a_vec, matchange, x)
    pol_eval = pol.subs(x=1)
    return Zq(pol_eval)

def sanity_check():
    print("Initiating sanity check...")
    mat = cmi
    pvec1 = random_vec(q, n)
    vec1 = cm * pvec1
    pvec2 = random_vec(q, n)
    vec2 = cm * pvec2
    vprod2 = vecmul_poly(vec1, vec2, cm, cmi)
    first_thing = go_to_q(vprod2, mat)
    second_thing = go_to_q(vec1, mat) * go_to_q(vec2, mat)
    if first_thing == second_thing:
        print("Sanity confirmed.")
    else:
        print("!!! SANITY ERROR !!!")
    return True

def histoq(data):
    hist = [0 for i in range(10)]
    zeroct = 0
    for datum in data:
        if datum == 0: zeroct += 1
        histbit = floor(ZZ(datum)*10/q)
        if histbit > 9: histbit = 9
        hist[histbit] += 1
    return [hist, zeroct]

def histo(data, cmi_mat):
    return histoq([go_to_q(datum, cmi_mat) for datum in data])

lift_s = 0
def secret_mod_q():
    global lift_s
    lift_s = go_to_q(secret, cmi)
    print(f"Secret mod q: {lift_s}")
    return True

def alg2(reportrate, quickflag=False):
    print("Beginning algorithm 2.")
    numsamps = len(samps)
    a_vals = [go_to_q(s[0], cmi) for s in samps]
    b_vals = [go_to_q(s[1], cmi) for s in samps]
    
    winner = [[], 0]
    
    for round_idx in range(2):
        if round_idx == 0:
            print("ROUND 1: Peeking at real secret.")
            iterat = [lift_s]
        else:
            print("ROUND 2: Running attack naively.")
            iterat = range(1000) if quickflag else range(q)
            
        possibles = []
        for g in iterat:
            if Mod(g, reportrate) == 0: print(f"Checking residue {g}")
            g_zq = Zq(g)
            potential = True
            ctr = 0
            while ctr < numsamps and potential:
                e = abs(lift(Zq(b_vals[ctr] - g_zq * a_vals[ctr])))
                if q/4 < e < 3*q/4:
                    potential = False
                else:
                    ctr += 1
            
            if ctr >= winner[1]:
                if ctr > winner[1]: winner = [[g_zq], ctr]
                else: winner[0].append(g_zq)
            
            if potential: possibles.append(g_zq)

    print(f"Real secret mod q was: {lift_s}")
    if lift_s in possibles:
        print("Success! Secret found.")
        return True
    return False

def shebang(fval, qval, sval, numsampsval, numtrials, quickflag=False):
    global sig
    print("Welcome to the Ring-LWE Attack.")
    n_deg = fval.degree()
    
    setup_params(fval, qval, sval)
    prepare_matrices()
    
    initiate_sampler()
    count_successes = 0
    
    for trialnum in range(numtrials):
        print(f"\n--- TRIAL {trialnum} ---")
        create_secret()
        create_samples(numsampsval)
        sanity_check()
        secret_mod_q()
        if alg2(10000, quickflag):
            count_successes += 1
            
    print(f"\nFinal Result: {count_successes}/{numtrials} successes.")
    return count_successes


# # gọi hàm ví dụ
f = y^4 + 1      # đa thức cyclotomic bậc 4
q = 101          # số nguyên tố
s = 3            # sigma

shebang(f, q, s, numsampsval=50, numtrials=5, quickflag=True)