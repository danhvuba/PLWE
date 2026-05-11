##################################################
# RING-LWE ATTACK #
##################################################

# General preparation of Sage: Create a polynomial ring and import GaussianSampler, Timer
# P: Ring đa thức trên trường số hữu tỉ P[y] = Q[y]
P.<y> = PolynomialRing(RationalField(), 'y')

# Phân phối Gauss
from sage.stats.distributions.discrete_gaussian_lattice import DiscreteGaussianDistributionLatticeSampler

# RP: RealField với độ chính xác cao (300 bit) (mặc định chỉ có 53 bit)
RP = RealField(300) 
# this sets the precision; if it is insufficient, the implementation won’t be valid

from sage.doctest.util import Timer


# Global choices: setup dummy values
# --- Các biến toàn cục (Global State) ---
# Các biến này sẽ được cập nhật thông qua hàm setup_params()
q = 1                           # Modulo q
sig = 1/sqrt(2*pi)              # Độ lệch chuẩn (sigma) cho nhiễu Gaussian - dummy values
Zq = IntegerModRing(q)          # Ring Z/qZ
R.<x> = PolynomialRing(Zq)      # Ring đa thức trên Zq: R[x] = Zq[x]
f = y + 1                       # Đa thức f
n = 1                           # Bậc của đa thức f
N.<a> = NumberField(f)          # Trường số được sinh bởi nghiệm của f là a; N = Q(a)
S.<z> = R.quotient(f)           # Ring S[z] = R[z]/(f(z)) = Zq[z] / (f(z)) 
# => This is P_q

# y,x là các symbol bất kỳ
# a,z là các symbol nghiệm của f trên N, S  ???

# cm (Canonical Matrix) - Ma trận M_alpha
# Chuyển vector hệ số đa thức về dạng Vector trong không gian Minkowski (đẳng cấu RR^n)
# Vector_V = cm * Vector_Coefficients
# cmi: Ma trận nghịch đảo của cm
# cm - ma trận trên RP, kích thước 1x1 = [0]
# key - vector định dạng hàng là phần thực/ảo trong ma trận cm
cm, key = matrix(RP, 1, 1, [0]), []                  
cmi = None
cm53 = cm.change_ring(RealField(10)) # .change_ring - ép kiểu toàn bộ phần tử của cm về RealField(10)
cmqq = cm53.change_ring(QQ)          # Chuyển ma trận về vành số hữu tỉ (QQ)
sampler = DiscreteGaussianDistributionLatticeSampler(cmqq.transpose(), sig)

# Lưu trữ dữ liệu tấn công
secret = 0                      # Vector bí mật (secret key)
samps = []                      # Danh sách các mẫu (a, b) = (a, a*s + e)
numsamps = 1                    # Số lượng mẫu
lift_s = 0                      # chuyển secret về dạng đa thức, tính giá trị đa thức tại x = 1, mod q.
# sig = sval/sqrt(2*pi)  - độ lệch chuẩn trong phân phối Gaussian
# sampler = DiscreteGaussianDistributionLatticeSampler(cmqq.transpose(), sig)


#################### Thiết lập tham số
# Set the parameters for the attack
# fval - đa thức f(y)
# qval - giá trị q
# sval - tham số Gaussian => dùng để tính độ lệch chuẩn sig (sigma)
def setup_params(fval, qval, sval):
    global q, n, sig, f, S, x, z, Zq
    f = fval
    n = f.degree()
    q = qval
    Zq = IntegerModRing(q)
    R.<x> = PolynomialRing(Zq)
    sig = sval/sqrt(2*pi) # sigma - độ lệch chuẩn trong phân phối Gaussian
    S.<z> = R.quotient(f)  # Zq[z]/f(z)
    print(f"Setting up parameters, poly = {f}, prime = {q}, sigma = {sig}")
    print("Verifying properties: ")

    if not q.is_prime():
        raise ValueError("q is not prime")
    print("q - prime? True")

    if not f.is_irreducible():
        raise ValueError("f is not irreducible")
    print("f - irreducible? True")

    if Mod(f.subs(y=1), q) != 0:
        raise ValueError(f"f(1) mod q = {Mod(f.subs(y=1), q)}, expected 0")
    print("f(1) ≡ 0 mod q? True")
    print()
    return True


####################  Minkowski space
# Give the Minkowski lattice for a given ring determined by a polynomial
# Also gives a key to which are real embeddings.
def cmatrix(): # returns a matrix, columns basis 1, x, x^2, x^3, ... given in the canonical embedding
    global N, a
    # 1. Khởi tạo Trường N sinh bởi nghiệm 'a' của f(y) = 0 trên CC
    N.<a> = NumberField(f)
    fdeg = f.degree()
    
    # key: Danh sách đánh dấu kiểu hàng 
    # 0 = real, 1 = real part of complex emb, 2 = imaginary part
    key = [0 for i in range(fdeg)] 
    
    # embs: Tập hợp n phép nhúng (embeddings) từ trường số N vào số phức CC
    # [alpha_0, ... , alpha_(n-1)] - tập hợp nghiệm của f trên N; 
    # embs = [embs_0, ....];   embs_i: g(x) --> g(alpha_i)
    # Mỗi phép nhúng tương ứng với việc thay một nghiệm phức của f vào đa thức
    embs = N.embeddings(CC)
    M = matrix(RP, fdeg, fdeg)
    
    print("Preparing an embedding matrix: computing powers of the root.")
    # apows: Tính trước các lũy thừa [a^0, a^1, ..., a^(n-1)] => rút gọn bậc => để tăng tốc ??
    apows = [a^j for j in range(n)]
    print("Finished computing the powers of the root.")
    
    i = 0
    while i < n:
        em = embs[i] # Lấy phép nhúng thứ i (ứng với nghiệm alpha_i)
        
        # in thông báo quá trình chạy
        if Mod(i,20)==Mod(0,20) or Mod(i,20)==Mod(1,20):
            print(f"Embedding matrix: {i} rows out of {n} complete.")
        
        # TRƯỜNG HỢP 1: em(a) = alpha_i - là số thực
        if em(a).imag() == 0:
            key[i] = 0
            for j in range(n):
                # Hàng của M là các giá trị em(a^j)
                M[i, j] = em(apows[j]).real()
            i = i + 1
            
        # TRƯỜNG HỢP 2: Nghiệm alpha_i là số phức
        # Ta tách thành 2 hàng:
        else:
            key[i] = 1      # Đánh dấu hàng phần thực: Real
            key[i+1] = 2    # Đánh dấu hàng phần ảo: Imag
            
            for j in range(n):
                val = em(apows[j])
                # M[i]   = Real(val)
                # M[i+1] = - Imag(val)
                M[i, j] = val.real()
                M[i+1, j] = (val * I).real() 
            i = i + 2
            
    return M, key

# Make a vector in RR^n into a polynomial ???
# Chuyển đổi một Vector trong θ(R) về đa thức
# a_vec: Vector trong θ(R)
# matchange: Ma trận nghịch đảo cmi (cm^-1)
# var: Biến của đa thức (x hoặc z)
def make_poly(a, matchange, var):
    coeffs = matchange * a #coefficients of the polynomial are given by the change of basis matrix
    pol = 0
    
    for i in range(n):
        # round làm tròn ????????
        # ZZ ép kiểu số nguyên: 1.0 -> 1
        pol = pol + ZZ(round(coeffs[i])) * var^i 
        # var controls where it will live (what poly ring)
        
    return pol

# Make a polynomial into a vector in Minkowski space
# Chuyển đổi một đa thức thành vector trong θ(R)
# fval: Đa thức đầu vào
# matchange: Ma trận nhúng Minkowski (cm)
def make_vec(fval, matchange):
    if fval == 0:
        coeffs = [0 for i in range(n)]
    else:
        coeffs = [0 for i in range(n)]
        # lift(fval):    trả về một đa thức cụ thể trong class (vì đang làm việc trong thương)
        # .coefficients(): Trả về danh sách các hệ số [c0, c1, c2, ...]
        colist = lift(fval).coefficients()
        
        for i in range(len(colist)):
            coeffs[i] = ZZ(colist[i]) # Gán hệ số vào vector, đảm bảo kiểu dữ liệu là số nguyên ZZ
            
    return matchange * vector(coeffs)

# Multiplication in Minkowski space via moving to polynomial ring
# Thực hiện phép nhân hai phần tử trong θ(R) thông qua nhân đa thức
# u, v: Hai vector trong θ(R)
# mat: Ma trận nhúng M (cm)
# matinv: Ma trận nghịch đảo M^-1 (cmi)
def vecmul_poly(u, v, mat, matinv):
    poly_u = make_poly(u, matinv, z)
    poly_v = make_poly(v, matinv, z)
    
    # Nhân đa thức trong vành đa thức
    poly_prod = poly_u * poly_v
    return make_vec(poly_prod, mat)

# Compute the lattices in Minkowski space
# Chuẩn bị các ma trận lưới trong không gian Minkowski
def prepare_matrices():
    global cm, key, cmi, cmqq
    print("Preparing matrices.")
    
    # Tạo ma trận lưới Minkowski (Minkowski Lattice Matrix) từ vành đa thức f
    cm, key = cmatrix()
    print ("Embedding matrix prepared.")
    cmi = cm.inverse()
    print ("Inverse matrix found.")
    
    # cm53: Bản sao của cm nhưng giảm độ chính xác xuống
    # RealField(10) trường số thực độ chính xác 10 bit
    # giúp tăng tốc độ cho các phép tính
    # .change_ring - ép kiểu toàn bộ phần tử của cm về RealField(10)
    # phải đặt tên là cm10 mới đúng ????????????????????????????????????????????????????????????
    cm53 = cm.change_ring(RealField(10))
    
    # cmqq: Chuyển ma trận về vành số hữu tỉ (QQ)
    cmqq = cm53.change_ring(QQ)
    
    print("All matrices prepared.")
    return True


###################### lấy mẫu

# Các hàm phụ
# Produce a random vector from (Z/qZ)^n
# ZZ - tập hợp các số nguyên
def random_vec(q, dim):
    return vector([ZZ.random_element(0, q) for i in range(dim)])

# Real numbers modulo q
def modq(r, q):
    t = r/q - floor(r/q)
    return t*q

########## lấy mẫu 
# Create the sampler on the lattice embedded ( θ(R) ) in RR^n
def initiate_sampler():
    global sampler
    print("Initiating Sampler.")
    
    # 1. DiscreteGaussianDistributionLatticeSampler: Bộ lấy mẫu phân phối Gaussian rời rạc
    # 2. cmqq.transpose(): ma trận chuyển vị của cmqq 
    # 3. sig: Độ lệch chuẩn (sigma) = sval/sqrt(2*pi)
    sampler = DiscreteGaussianDistributionLatticeSampler(cmqq.transpose(), sig)
    
    # RDF(sig): Ép kiểu sigma sang Real Double Field để in ra màn hình cho gọn
    print(f"Sampler initiated with sigma {RDF(sig)}")
    
    return True

# Call sampler
# lấy mẫu nhiễu e 
def call_sampler():
    # .change_ring(RP): .change_ring - ép kiểu toàn bộ phần tử về RP (độ chính xác 300 bit)
    e = sampler().change_ring(RP)
    return e

# Create samples using a lattice
# Tạo các cặp mẫu (a, b) Ring-LWE trong θ(R_q)
# latmat: Ma trận nhúng M (cm), latmatinv: Ma trận nghịch đảo M^-1 (cmi)
# sec: Vector bí mật 's' trong θ(R)
# qval: Giá trị Modulo q của hệ thống
# keyval - vector định dạng hàng là phần thực/ảo trong ma trận Minkowski
def get_sample(latmat, latmatinv, sec, qval, keyval):
    # 1. Lấy mẫu nhiễu e trong θ(R)
    e = call_sampler() 
    
    # 2. Tạo đa thức ngẫu nhiên 'pre_a'
    dim = latmat.dimensions()[0]  # lấy số hàng của ma trận; cm[nxn]
    pre_a = random_vec(qval, dim) # create a uniformly randomly in terms of basis in cm  ???????
    # tạo pre_a trên P_q
    
    # 3. Chuyển 'pre_a' sang θ(R_q)
    a = latmat * pre_a 
    
    # 4. Tính b = a * s + e trong θ(R)
    # Dùng vecmul_poly để nhân trong không gian Minkowski (thông qua nhân đa thức)
    b = vecmul_poly(a, sec, latmat, latmatinv) + e
    
    # 5. Rút gọn b  ??????????
    # chuyển b về dạng đa thức
    pre_b = latmatinv * b  # move to basis in cm in order to reduce mod q
    # Thực hiện Modulo q đối với từng hệ số vector
    pre_b_red = vector([modq(c, qval) for c in pre_b])
    
    # 6. Đưa b đã rút gọn quay lại θ(R_q)
    b = latmat * pre_b_red
    
    return [a, b]

# taọ secret trên θ(R_q)
def create_secret():
    global secret
    secret = cm * random_vec(q, n)
    return True

# tạo danh sách chứa numsampsval mẫu (a, b) Ring-LWE trong θ(R_q)
def create_samples(numsampsval):
    global samps, numsamps
    samps = []
    print("Creating samples...")
    for i in range(numsampsval):
        #print (f"Creating sample number  {i}")
        samp = get_sample(cm, cmi, secret, q, key)
        samps.append(samp)
    numsamps = len(samps)
    print(f"Done creating {len(samps)} samples.")
    return True

# Produce error vectors, just a test to see how they look
def error_test(num):
    print(f"Testing the error vector production by producing {num} errors.")
    
    # Tạo danh sách độ dài của các vector nhiễu:
    # sampler(): Lấy một mẫu nhiễu e (dạng vector) từ bộ lấy mẫu Gaussian rời rạc
    # .norm(): Tính chuẩn (độ dài) của vector nhiễu đó
    # .n(): Chuyển giá trị độ dài sang dạng số thực (numerical)
    errorlist = [sampler().norm().n() for _ in range(num)]
    meannorm = mean(errorlist)  # average norm
    maxnorm = max(errorlist)    # maximum norm
    
    # Tính toán tỷ lệ
    avg_ratio = RDF(meannorm / (sqrt(n) * sampler.sigma() * sqrt(2 * pi)))
    max_ratio = RDF(maxnorm / (sqrt(n) * sampler.sigma() * sqrt(2 * pi)))
    
    print(f"The average error norm is {avg_ratio} times sqrt(n)*s.")
    print(f"The maximum error norm is {max_ratio} times sqrt(n)*s.")
    
    if max_ratio > 1:
        print("~~~~~~~~~~~~~~~~~~~~~~~ ERROR ~~~~~~~~~~~~~~~~~~~~~~~~~")
        print("The errors do not satisfy a proven upper bound in norm.")
        return True
    
    return False

# Function for going down to q
# Chuyển đổi đối tượng từ không gian Minkowski về đa thức
# và trả về giá trị đa thức tại x = 1 modulo q
def go_to_q(a_vec, matchange):
    pol = make_poly(a_vec, matchange, x)
    pol_eval = pol.subs(x=1)
    return Zq(pol_eval)

# Create the secret mod q
# chuyển secret về đa thức, thay giá trị x = 1, mod q
def secret_mod_q():
    global lift_s
    lift_s = go_to_q(secret, cmi)
    print("Storing the secret mod q.")
    print("The secret is ", secret)
    print("s(1) mod q = ", lift_s)
    return True

# Check to make sure moving to q preserves product -- the last two lines should be equal
# Kiểm tra tính đúng đắn của phép đồng cấu (Sanity Check)
# Xác nhận rằng tính chất nhân của vành được bảo toàn khi chuyển 
# từ θ(R_q) về đa thức. Nếu bài kiểm tra này vượt qua, 
# cuộc tấn công dựa trên phép đánh giá đa thức tại 1 mới có thể thực hiện được.
def sanity_check():
    print("Initiating sanity check...")
    mat = cmi
    
    # 1. Tạo hai vector trong θ(R_q)
    # thông qua hai vector đa thức trên P_q => chuyển về θ(R_q)
    pvec1 = random_vec(q, n)
    vec1 = cm * pvec1
    pvec2 = random_vec(q, n)
    vec2 = cm * pvec2
    
    # 2. Thực hiện kiểm tra tính đồng cấu qua hai con đường:
    # Cách 1: Nhân hai vector thông qua đa thức trước, 
    # sau đó mới dùng hàm go_to_q để chuyển về số nguyên Zq
    vprod2 = vecmul_poly(vec1, vec2, cm, cmi)
    first_thing = go_to_q(vprod2, mat)
    
    # Cách 2: Chuyển từng vector về đa thức; dùng hàm go_to_q để chuyển về số nguyên Zq, 
    # sau đó mới nhân các số nguyên đó với nhau
    second_thing = go_to_q(vec1, mat) * go_to_q(vec2, mat)
    
    # 3. Đối chiếu kết quả
    if first_thing != second_thing:
        raise ValueError(
            f"Sanity problem: {first_thing} != {second_thing}. "
            "Check that your ring has root 1 mod q."
    )
    print("Sanity confirmed.")
    return True

# Given a list of elements of Z/qZ, make a histogram and zero count
def histoq(data):
    hist = [0 for i in range(10)] # empty histogram
    zeroct = 0 # count of zeroes mod q
    for datum in data:
        e = datum
        if e == 0: 
            zeroct += 1
        histbit = floor(ZZ(e)*10/q)
        hist[histbit] = hist[histbit] + 1
    return [hist, zeroct]

# Given a list of vectors in R^n, create a histogram of their
# values in Z/qZ under make_poly, together with a zero count
def histo(data, cmi):
    return histoq([go_to_q(datum, cmi) for datum in data])

# Create a histogram of error vectors, transported to polynomial ring
def histogram_of_errors():
    print("Creating a histogram of errors mod q.")
    errs = []
    for i in range(80):
        errs.append(sampler())
    hist = histo(errs,cmi)
    print("The number of error vectors that are zero:", hist[1])
    # bar_chart(hist[0], width=1).show(figsize=2)
    bar_chart(hist[0], width=1).save('histogram_of_errors.png') 
    print("Saved histogram_of_errors to histogram_of_errors.png")
    return True

# Create a histogram of the a’s in the samples, transported to polynomial ring
def histogram_of_as():
    print("Creating a histogram of sample a’s mod q.")
    a_vals = [samp[0] for samp in samps]
    hist = histo(a_vals,cmi)
    print("The number of a’s that are zero:", hist[1])
    # bar_chart(hist[0], width=1).show(figsize=2)
    bar_chart(hist[0], width=1).save('histogram_of_as.png') 
    print("Saved histogram_of_as to histogram_of_as.png")
    return True

# Create a histogram of errors by correct guess
def histogram_of_errors_2():
    print("Creating a histogram of supposed errors if sample is guessed, mod q.")
    hist = histoq([ lift(Zq(go_to_q(sample[1],cmi) - go_to_q(sample[0],cmi)*go_to_q(secret,cmi))) for sample in samps])
    print("The number of such that are zero:", hist[1])
    # bar_chart(hist[0], width=1).show(figsize=2)
    bar_chart(hist[0], width=1).save('histogram_of_errors_2.png') 
    print("Saved histogram_of_errors_2 to histogram_of_errors_2.png")
    
    return True

def histogram_of_errors_guess():
    print("Creating a histogram of supposed errors if sample is guessed, mod q.")
    for g in range(q):
        hist = histoq([ lift(Zq(go_to_q(sample[1],cmi) - go_to_q(sample[0],cmi)*Zq(g))) for sample in samps])
        bar_chart(hist[0], width=1).save('errors_guess.png') 
        input(f"Thử g = {g}. Nhấn Enter để tiếp tục...")
    return True

# Algorithm 2: Đoán giá trị g (secret trong Zq := s(1) mod q)
# reportrate controls how often it updates the status of the loop; larger = less frequently
# quickflag = True will run only the secret and a few other values to give a quick idea if it works
def alg2(numsamps, reportrate, quickflag = False):
    print("")
    print("")
    print(f"******************* Beginning ALGORITHM 2 with {numsamps} samples ********************")
    #numsamps = len(samps)
    a = [ 0 for i in range(numsamps)]
    b = [ 0 for i in range(numsamps)]
    
    print("Moving samples to F_q.")
    # 1. Chuyển đổi toàn bộ các phân phối từ θ(R_q) về số nguyên trong Zq
    for i in range(numsamps):
        sample = samps[i]
        # đối với mỗi phân phối
        a[i] = go_to_q(sample[0],cmi) # a_i = a(1) mod q
        b[i] = go_to_q(sample[1],cmi) # b_i = b(1) mod q
        
    possibles = [] # Danh sách các ứng viên vượt qua toàn bộ mẫu
    winner = [[],0] # Lưu kẻ thắng cuộc: [[danh_sách_g], số_mẫu_vượt_qua]
    
    print("Samples have been moved to F_q.")
    print("")
    
    # Thuật toán chạy qua 2 vòng (Round)
    for i in range(2):
        if i == 0:
            # ROUND 1: Kiểm tra xem bí mật thực sự (lift_s) vượt qua được bao nhiêu mẫu
            print("!!!!! ROUND 1: !!!!! First, checking how many samples the secret survives (peeking ahead).")
            iterat = [lift_s]
        if i == 1:
            # ROUND 2: Tấn công thực tế bằng cách thử các giá trị g khác nhau
            print("")
            print("!!!!! ROUND 2: !!!!! Now, running the attack naively.")
            possibles = []
            if quickflag:
                # Nếu bật quickflag, chỉ thử 1000 giá trị đầu tiên để tiết kiệm thời gian
                print("We are doing it quickly (not a full test).")
                iterat = range(1000) 
            else:
                # Thử toàn bộ các giá trị từ 0 đến q-1
                iterat = range(q)
        
        # thử tìm các giá trị g        
        for g in iterat:
            # In trạng thái tiến độ dựa trên reportrate
            
            # if Mod(g,reportrate) == Mod(0,reportrate) and g != 0:
            #     print("")
            #     print(f"Currently checking g = {g}")
            
            g = Zq(g) # ép kiểu g sang Zq
            potential = True # Gán cờ giả định g là ứng viên tiềm năng
            ctr = 0 # Bộ đếm số lượng mẫu mà g vượt qua
            
            # Duyệt qua từng mẫu để kiểm tra với giá trị g hiện tại
            while ctr < numsamps and potential:
                # Tính sai số e = b - g*a (tương đương với e(1) trong lý thuyết)
                e = abs(lift(Zq(b[ctr] - g * a[ctr])))
                
                # KIỂM TRA ĐIỀU KIỆN
                if e > q/4 and e < 3*q/4:
                    potential = False 
                    # => kết thúc vòng lặp
                    # Cập nhật Winner
                    if ctr == winner[1]:
                        winner[0].append(g)
                        #print(f"We have a new tie for longest chain: {g_zq} has survived {ctr} rounds.")
                    
                    if ctr > winner[1]:
                        winner = [[g],ctr]
                        #print(f"We have a new longest chain of samples survived: {g_zq} has survived {ctr} rounds.")
                
                ctr = ctr + 1 # chuyển đến mẫu tiếp theo
            
            # Nếu g vượt qua toàn bộ các mẫu mà không bị loại
            if potential == True and i != 0:
                #print(f"We found a potential secret: {g}, pass {numsamps} samples")
                possibles.append(g)
            
            # Thông báo riêng nếu giá trị đang xét chính là bí mật thực sự
            if g == lift_s:
                if i == 0:
                    print(f"The real secret {lift_s}")
                    print(f"pass {ctr} samples.")
                #break
    
    print("")               
    print(f"Full list of survivors of the {numsamps} samples: list g {possibles}")
    print(f"The real secret mod q was: {lift_s}")
    
    # KIỂM TRA CUỐI CÙNG
    if len(possibles) == 1 and possibles[0] == lift_s:
        print("Success!")
        return True
    else:
        print("Failure!")
        return False


# Run a simulation.
def shebang(fval,qval,sval,numsampsval,numtrials,quickflag=False):
    global sig#, n
    print("Welcome to the Ring-LWE Attack.")
    
    n = fval.degree()
    
    # In ra giá trị dự đoán khả năng thành công dựa trên lý thuyết toán học
    print("The attack should theoretically work if the following quantity is greater than 1.")
    print("Quantity: ", RDF( qval/( 2*sqrt(2)*sval*n*(qval-1)^( (n-1)/2/n) ) ))
    
    # Khởi tạo bộ đếm thời gian
    timer = Timer()
    timer2 = Timer()
    timer.start()
    
    print("")
    print("") 
    print("********** PHASE 1: SETTING UP SYSTEM ")
    # Thiết lập các thông số cơ bản và chuẩn bị ma trận Minkowski
    setup_params(fval,qval,sval)
    prepare_matrices()
    
    print("") 
    print("Computing the adjustment factor for s.")
    # cembs: Số lượng các cặp embedding phức 
    cembs = (n - len(N.embeddings(RR)))/2
    # detscale: Hệ số điều chỉnh dựa trên định thức của vành (discriminant) để khớp với không gian Minkowski
    detscale = RP( ( 2^(-cembs)*sqrt(abs(f.discriminant())) )^(1/n) ) # adjust the sigma,s
    
    # Điều chỉnh tham số s và độ lệch chuẩn sig theo cấu trúc hình học của vành
    sval = sval*detscale
    sig = sig*detscale
    
    print("Adjusted s for use with this embedding, result is ", sval)
    print("") 
    
    # Khởi tạo bộ lấy mẫu nhiễu Gaussian sau khi đã điều chỉnh sig
    initiate_sampler()
    
    print("The sampler has been created with sigma = ", sampler.sigma())
    print("Sampled vectors will have expected norm ", RDF(sqrt(n)*sampler.sigma()))
    
    # # Chạy thử nghiệm nhiễu trên 5 mẫu
    # error_test(5)
    # print("Time for Phase 1: ", timer.stop())
    
    timer.start()
    count_successes = 0
    timer2.start()
    
    # Bắt đầu vòng lặp thử nghiệm (trials)
    for trialnum in range(numtrials):
        print("")
        print("")
        print("*~*~*~*~*~*~*~*~*~*~*~*~* TRIAL NUMBER ", trialnum, "*~*~*~*~*~*~*~*~*~*~*~*~*~*~*~*~")
        
        print("********** PHASE 2: CREATE SECRET AND SAMPLES")
        # Tạo khóa bí mật s và các mẫu Ring-LWE (a, b)
        create_secret()
        create_samples(numsampsval)
        
        # Kiểm tra 
        sanity_check()
        print("Time for Phase 2: ", timer.stop())
        
        timer.start()
        print("")
        print("")
        print("********** PHASE 3: HISTOGRAMS")
        # Vẽ biểu đồ phân phối lỗi và các giá trị 'a' để quan sát đặc điểm dữ liệu
        # histogram_of_errors()
        # print("The histogram of errors (above) should be clustered at edges for success.")
        
        # histogram_of_as()
        # print("The histogram of a’s (above) should be fairly uniform.")
        
        # histogram_of_errors_2()
        # print("The histogram of sample errors (above) should be clustered at edges for success.")
        # print("Time for Phase 3: ", timer.stop())

        # input(f"Lần thử thứ {trialnum}: s(1) mod q = {go_to_q(secret, cmi)} Nhấn Enter để tiếp tục...")
        # histogram_of_errors_guess()
        
        timer.start()
        
        print("")
        print("")
        print("********** PHASE 4: ATTACK ALGORITHM")
        # Tìm giá trị thực của bí mật mod q (để đối chiếu) và chạy thuật toán tấn công
        secret_mod_q()
        
        for i in range(1,30):
            result = alg2(i,10000,quickflag)
        
        # print("Result of Algorithm 2:", result)
        print("Time for Phase 4: ", timer.stop())
        
        # Nếu tìm được đúng bí mật, tăng biến đếm thành công
        if result == True:
            count_successes = count_successes + 1
            
        print("*~*~*~*~*~*~*~*~*~*~*~*~* ", count_successes, " out of ", trialnum+1, " successes so far. *~*~*~*~*~*")
        
    # Kết thúc tất cả các lượt thử, dừng đồng hồ tổng
    totaltime = timer2.stop()
    print("")
    print("")
    print("Total time for ", trialnum+1, "trials was ", totaltime)
    
    return count_successes


# # # gọi hàm ví dụ
# # đa thức cyclotomic bậc 4; # f(1) mod q = 0
# f = y^4 + y^3 + y^2 + y + 1    
# q = 5 
# # chọn s sao cho:  q << sigma * sqrt(n) 
# # sigma = s/sqrt(2*pi)                 
# s = 0.1                       


# # 2.
# # f(1) mod q = 0
# f = y^128 + 524288*y + 5248285
# q = 5248287 
# # sigma = s/sqrt(2*pi)                 
# s = 8.00    # := w   

# 3.
# # gọi hàm ví dụ
# f(1) mod q = 0
f = y^192 + 4092    
q = 4093 
# sigma = s/sqrt(2*pi)                 
s = 8.87    # := w         

# # 4.
# # f(1) mod q = 0
# f = y^256 + 8190
# q = 8191 
# # sigma = s/sqrt(2*pi)                 
# s = 8.35    # := w    

shebang(f, q, s, numsampsval=30, numtrials=1, quickflag=False)




# # Thử với p lớn 
# p_prime = 11
# f = sum(y^i for i in range(p_prime))
# q = p_prime 
# # f(1) mod q = 0
# #chọn s sao cho:  q << sigma * sqrt(n) 
# sigma = s/sqrt(2*pi)   
# s = 0.1

#shebang(f, q, s, numsampsval=50, numtrials=5, quickflag=False)


# f = y^3 - 2
# f = y^6 - 5*y^4 + 5*y^2 + 6   
# f = y^8 - 10*y^6 + 20*y^4 + 5*y^2 + 2
# f = y^12 - 2         # (2,5)
# f = y^8 - 10*y^6 + 20*y^4 + 5*y^2 + 2     # (2,3)
# N.<a> = NumberField(f)
# n = f.degree()
# embs = N.embeddings(CC)

# print(N.signature())
# for i in range (n):
#     em = embs[i]
#     print(f"{em(a).real()} + i * {-((em(a)*I).real())}")
    
