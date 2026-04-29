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
N.<a> = NumberField(f)          # Trường số được sinh bởi f; N[a] = Q[a] / (f(a))
S.<z> = R.quotient(f)           # Ring S[z] = R[z]/(f(z)) = Zq[z] / (f(z))

# y,x là các symbol bất kỳ
# a,z là các symbol nghiệm của f trên N, S!!!!!!!

# cm (Canonical Matrix): Chuyển đa thức về dạng Vector trong không gian Minkowski
# Vector_V = cm * Vector_Coefficients
# cmi: Ma trận nghịch đảo của cm
# cm - ma trận trên RP, kích thước 1x1 = [0]
# key - vector định dạng hàng là phần thực/ảo trong ma trận Minkowski
cm, key = matrix(RP, 1, 1, [0]), []                  
cmi = cm

# Lưu trữ dữ liệu tấn công
secret = 0                      # Vector bí mật (secret key)
samps = []                      # Danh sách các mẫu (a, b) = (a, a*s + e)
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
    sig = sval/sqrt(2*pi)
    S.<z> = R.quotient(f)
    print(f"Setting up parameters, poly = {f}, prime = {q}, sigma = {sig}")
    print("Verifying properties: ")
    print("q - prime?", q.is_prime())
    print("f - irreducible? ", f.is_irreducible())
    print("Value at 1 of f modulo q?", Mod(f.subs(y=1), q))
    return True


####################  Minkowski space

# Give the Minkowski lattice for a given ring determined by a polynomial
# Tạo ma trận lưới Minkowski (Minkowski Lattice Matrix) từ vành đa thức f
# M = [ [sigma_1(a^0), sigma_1(a^1), ..., sigma_1(a^(n-1))] ]
#     [ [sigma_2(a^0), sigma_2(a^1), ..., sigma_2(a^(n-1))] ]
#     ...
# Trong đó sigma_i là phép nhúng thứ i vào số phức CC.

# Công thức hàng (Row formulas) trong ma trận M:
# Nếu sigma_i(a) là THỰC: 
#    M[i, j] = Re(sigma_i(a^j)) | key[i] = 0
# Nếu sigma_i(a) là PHỨC (sigma_i, sigma_{i+1} là cặp liên hợp):
#    M[i, j]   = Re(sigma_i(a^j))     | key[i]   = 1
#    M[i+1, j] = Im(sigma_i(a^j))     | key[i+1] = 2
def cmatrix(): 
    global N, a
    # 1. Khởi tạo Trường  N sinh bởi nghiệm 'a' của f(y) = 0
    # N[a] = Q[a] / (f(a)) - trường đa thức
    N.<a> = NumberField(f)
    fdeg = f.degree()
    
    # key: Danh sách đánh dấu kiểu hàng (0: thực, 1: phần thực phức, 2: phần ảo phức) ?????????????????????????????????
    key = [0 for i in range(fdeg)] 
    
    # embs: Tập hợp n phép nhúng (embeddings) từ trường đa thức N vào số phức CC
    # [alpha_0, ... , alpha_(n-1)] - tập hợp nghiệm của f trên N; 
    # embs = [embs_0, ....];   embs_i: g(x) --> g(alpha_i)
    # Mỗi phép nhúng tương ứng với việc thay một nghiệm phức của f vào đa thức
    embs = N.embeddings(CC)
    M = matrix(RP, fdeg, fdeg)
    
    print("Preparing an embedding matrix: computing powers of the root.")
    # apows: Tính trước các lũy thừa [a^0, a^1, ..., a^(n-1)] => rút gọn bậc => để tăng tốc
    apows = [a^j for j in range(n)]
    print("Finished computing the powers of the root.")
    
    i = 0
    while i < n:
        em = embs[i] # Lấy phép nhúng thứ i (ứng với nghiệm alpha_i)
        
        # in thông báo quá trình chạy
        if Mod(i, 20) == 0:
            print(f"Embedding matrix: {i} rows out of {n} complete.")
        
        # TRƯỜNG HỢP 1: em(a) = alpha_i - là số thực
        if em(a).imag() == 0:
            key[i] = 0
            for j in range(n):
                # Hàng của M là các giá trị em(a^j)
                M[i, j] = em(apows[j]).real()
            i = i + 1
            
        # TRƯỜNG HỢP 2: Nghiệm alpha_i là số phức
        # Một nghiệm phức luôn đi kèm nghiệm liên hợp. Ta tách thành 2 hàng thực:
        else:
            key[i] = 1      # Đánh dấu hàng phần thực: Real(sigma(a))
            key[i+1] = 2    # Đánh dấu hàng phần ảo: Imag(sigma(a))
            
            for j in range(n):
                val = em(apows[j])
                # Công thức nhúng Minkowski cho cặp nghiệm phức:
                # M[i]   = Real(val)
                # M[i+1] = Imag(val) (được tính bằng Real(val * I) để giữ độ chính xác)
                M[i, j] = val.real()
                M[i+1, j] = (val * I).real() 
            i = i + 2
            
    return M, key

# Make a vector in R^n into a polynomial
# Chuyển đổi một Vector trong không gian Minkowski (R^n) về dạng Đa thức
# a_vec: Vector tọa độ thực
# matchange: Ma trận nghịch đảo cmi (cm^-1)
# var: Biến của đa thức (x hoặc z)
def make_poly(a_vec, matchange, var):
    # Công thức: Vector_Hệ_Số = M^-1 * Vector_Minkowski
    coeffs = matchange * a_vec
    pol = 0
    
    for i in range(n):
        # Làm tròn số thực về số nguyên ZZ để ?????????????????
        # pol = c_0*var^0 + c_1*var^1 + ... + c_n*var^n
        pol = pol + ZZ(round(coeffs[i])) * var^i
        
    return pol

# Make a polynomial into a vector in Minkowski space
# Chuyển đổi một đa thức thành vector trong không gian Minkowski (R^n)
# fval: Đa thức đầu vào
# matchange: Ma trận nhúng Minkowski (cm)
def make_vec(fval, matchange):
    # 1. Trích xuất các hệ số của đa thức thành một danh sách (list)
    # vector hệ số
    coeffs = [0 for i in range(n)]
    
    if fval != 0:
        # lift(fval): ????????
        # .coefficients(): Trả về danh sách các hệ số [c0, c1, c2, ...]
        colist = lift(fval).coefficients()
        
        for i in range(len(colist)):
            # Gán hệ số vào vector, đảm bảo kiểu dữ liệu là số nguyên ZZ
            coeffs[i] = ZZ(colist[i])
            
    # 2. Thực hiện phép nhúng: Vector_Minkowski = M * Vector_Hệ_Số
    # matchange ở đây chính là ma trận cm được tạo từ hàm cmatrix()
    return matchange * vector(coeffs)

# Multiplication in Minkowski space
# Thực hiện phép nhân hai phần tử trong không gian Minkowski thông qua nhân đa thức
# u, v: Hai vector trong không gian thực R^n
# mat: Ma trận nhúng M (cm)
# matinv: Ma trận nghịch đảo M^-1 (cmi)
def vecmul_poly(u, v, mat, matinv):
    poly_u = make_poly(u, matinv, z)
    poly_v = make_poly(v, matinv, z)
    
    # Nhân đa thức trong vành (thực hiện modulo f tự động bởi Sage)
    poly_prod = poly_u * poly_v
    return make_vec(poly_prod, mat)

# Compute the lattices in Minkowski space
# Chuẩn bị các ma trận lưới trong không gian Minkowski
def prepare_matrices():
    global cm, key, cmi, cmqq
    print("Preparing matrices.")
    
    # Tạo ma trận lưới Minkowski (Minkowski Lattice Matrix) từ vành đa thức f
    cm, key = cmatrix()
    cmi = cm.inverse()
    
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

# Khởi tạo bộ lấy mẫu nhiễu trên lưới (Lattice Sampler)
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
# Tạo các cặp mẫu (a, b) Ring-LWE trong không gian Minkowski
# latmat: Ma trận nhúng M (cm), latmatinv: Ma trận nghịch đảo M^-1 (cmi)
# sec: Vector bí mật 's' đã được nhúng vào không gian Minkowski
# qval: Giá trị Modulo q của hệ thống
# keyval - vector định dạng hàng là phần thực/ảo trong ma trận Minkowski
def get_sample(latmat, latmatinv, sec, qval, keyval):
    # 1. Lấy mẫu nhiễu e trực tiếp trong không gian Minkowski, e sinh ra đã có dạng vector thực
    e = call_sampler() 
    
    # 2. Tạo đa thức ngẫu nhiên 'a'
    dim = latmat.dimensions()[0]  # lấy số hàng của ma trận; cm[nxn]
    pre_a = random_vec(qval, dim) # a ở dạng vector hệ số nguyên [0, q-1]
    
    # 3. Chuyển 'a' sang không gian Minkowski
    a_vec = latmat * pre_a 
    
    # 4. Tính b = a * s + e trong không gian Minkowski
    # Dùng vecmul_poly để nhân trong không gian Minkowski thông qua nhân đa thức
    b_vec = vecmul_poly(a_vec, sec, latmat, latmatinv) + e
    
    # 5. Rút gọn b về vành Zq (Redundancy Reduction) ??????????
    # Vì b = a*s + e có thể vượt quá q, ta phải đưa nó về lại dạng hệ số để Modulo q ??????????
    pre_b = latmatinv * b_vec  # Giải mã b_vec về dạng hệ số thực
    
    # Thực hiện Modulo q đối với từng hệ số vector
    pre_b_red = vector([modq(c, qval) for c in pre_b])
    
    # 6. Đưa b đã rút gọn quay lại không gian Minkowski
    b_vec = latmat * pre_b_red
    
    return [a_vec, b_vec]

# taọ secret trong R^n
def create_secret():
    global secret
    secret = cm * random_vec(q, n)
    return True

# tạo danh sách chứa numsampsval mẫu (a, b) Ring-LWE trong không gian Minkowski
def create_samples(numsampsval):
    global samps
    samps = []
    print("Creating samples...")
    for i in range(numsampsval):
        samp = get_sample(cm, cmi, secret, q, key)
        samps.append(samp)
    print(f"Done creating {len(samps)} samples.")
    return True


def error_test(num):
    # In thông báo đang kiểm tra quá trình tạo nhiễu với 'num' mẫu thử
    print(f"Testing error production for {num} samples.")
    
    # 1. Tạo danh sách độ dài của các vector nhiễu:
    # sampler(): Lấy một mẫu nhiễu e (dạng vector) từ bộ lấy mẫu Gaussian rời rạc
    # .norm(): Tính chuẩn (độ dài) của vector nhiễu đó
    # .n(): Chuyển giá trị độ dài sang dạng số thực (numerical)
    errorlist = [sampler().norm().n() for _ in range(num)]
    
    # 2. Tính toán các giá trị thống kê cơ bản từ danh sách nhiễu
    meannorm = mean(errorlist) # Giá trị trung bình của độ dài các vector nhiễu
    maxnorm = max(errorlist)   # Độ dài lớn nhất ghi nhận được (nhiễu cực đại)
    
    # 3. In ra kết quả kiểm tra tỉ lệ:
    # RDF(...): Ép kiểu sang Real Double Field để hiển thị số thực ngắn gọn
    # Công thức: Chia meannorm cho (sqrt(n) * sigma * sqrt(2*pi))
    # Mục đích: Kiểm tra xem nhiễu thực tế có nằm trong phạm vi lý thuyết cho phép không.
    # Nếu tỉ lệ này xấp xỉ 1 hoặc nhỏ hơn, nhiễu được coi là "an toàn" cho việc giải mã/tấn công.
    print(f"Avg error norm: {RDF(meannorm/(sqrt(n)*sampler.sigma*sqrt(2*pi)))} * sqrt(n)*s")
    
    return True


# Chuyển đổi đối tượng từ không gian Minkowski về đa thức
# và trả về giá trị đa thức tại x = 1 modulo q
def go_to_q(a_vec, matchange):
    pol = make_poly(a_vec, matchange, x)
    pol_eval = pol.subs(x=1)
    return Zq(pol_eval)


# Kiểm tra tính đúng đắn của phép đồng cấu (Sanity Check)
# Xác nhận rằng tính chất nhân của vành được bảo toàn khi chuyển 
# từ không gian Minkowski (đa thức) về số nguyên Zq. Nếu bài kiểm tra này vượt qua, 
# cuộc tấn công dựa trên phép đánh giá đa thức tại 1 mới có thể thực hiện được.
def sanity_check():
    print("Initiating sanity check...")
    mat = cmi
    
    # 1. Tạo hai vector hệ số đa thức ngẫu nhiên và đưa chúng vào không gian Minkowski
    pvec1 = random_vec(q, n)
    vec1 = cm * pvec1
    pvec2 = random_vec(q, n)
    vec2 = cm * pvec2
    
    # 2. Thực hiện phép nhân hai vector này trong không gian Minkowski
    vprod2 = vecmul_poly(vec1, vec2, cm, cmi)
    
    # 3. Thực hiện kiểm tra tính đồng cấu qua hai con đường:
    # Cách 1: Nhân hai đa thức trước, sau đó mới dùng hàm go_to_q để chuyển về số nguyên Zq
    first_thing = go_to_q(vprod2, mat)
    
    # Cách 2: Chuyển từng đa thức về số nguyên Zq trước bằng go_to_q, sau đó mới nhân các số nguyên đó với nhau
    second_thing = go_to_q(vec1, mat) * go_to_q(vec2, mat)
    
    # 4. Đối chiếu kết quả
    if first_thing == second_thing:
        # Nếu bằng nhau: Phép ánh xạ là một đồng cấu vành hợp lệ
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

# chuyển secret về đa thức, thay giá trị x = 1, mod q
def secret_mod_q():
    global lift_s
    lift_s = go_to_q(secret, cmi)
    print(f"Secret mod q: {lift_s}")
    return True

# Algorithm 2: Đoán giá trị g (secret trong Zq := s(1) mod q)
# reportrate controls how often it updates the status of the loop; larger = less frequently
# quickflag = True will run only the secret and a few other values to give a quick idea if it works
def alg2(reportrate, quickflag = False):
    print("Beginning algorithm 2.")
    numsamps = len(samps)
    a = [ 0 for i in range(numsamps)]
    b = [ 0 for i in range(numsamps)]
    
    print("Moving samples to F_q.")
    # 1. Chuyển đổi toàn bộ các phân phối từ không gian Minkowski về số nguyên trong Zq
    for i in range(numsamps):
        sample = samps[i]
        # đối với mỗi phân phối
        a[i] = go_to_q(sample[0],cmi) # a_i = a(1) mod q
        b[i] = go_to_q(sample[1],cmi) # b_i = b(1) mod q
        
    possibles = [] # Danh sách các ứng viên vượt qua toàn bộ mẫu
    winner = [[],0] # Lưu kẻ thắng cuộc: [[danh_sách_g], số_mẫu_vượt_qua]
    
    print("Samples have been moved to F_q.")
    
    # Thuật toán chạy qua 2 vòng (Round)
    for i in range(2):
        if i == 0:
            # ROUND 1: Kiểm tra xem bí mật thực sự (lift_s) vượt qua được bao nhiêu mẫu
            print("!!!!! ROUND 1: !!!!! First, checking how many samples the secret survives (peeking ahead).")
            iterat = [lift_s]
        if i == 1:
            # ROUND 2: Tấn công thực tế bằng cách thử các giá trị g khác nhau
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
            if Mod(g,reportrate) == Mod(0,reportrate):
                print(f"Currently checking residue {g}")
            
            g = Zq(g) # Chuyển số nguyên g sang vành Zq
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
            if potential == True:
                print(f"We found a potential secret: {g}")
                possibles.append(g)
            
            # Thông báo riêng nếu giá trị đang xét chính là bí mật thực sự
            if g == lift_s:
                if i == 0:
                    print(f"The real secret survived {ctr} samples.")
                #break
                   
    print(f"Full list of survivors of the {numsamps} samples: list g_zq {possibles}")
    print(f"The real secret mod q was: {lift_s}")
    
    # KIỂM TRA CUỐI CÙNG
    if len(possibles) == 1 and possibles[0] == lift_s:
        print("Success!")
        return True
    else:
        print("Failure!")
        return False


# Run a simulation.
# Hàm thực hiện: Chạy mô phỏng toàn bộ quá trình tấn công Ring-LWE
# Chức năng: Điều phối các giai đoạn từ thiết lập tham số, tạo mẫu, kiểm tra thống kê đến thực thi thuật toán tấn công.
def shebang(fval,qval,sval,numsampsval,numtrials,quickflag=False):
    global sig
    print("Welcome to the Ring-LWE Attack.")
    
    n = fval.degree()
    
    # In ra giá trị dự đoán khả năng thành công dựa trên lý thuyết toán học
    print("The attack should theoretically work if the following quantity is greater than 1.")
    print("Quantity: ", RDF( qval/( 2*sqrt(2)*sval*n*(qval-1)^( (n-1)/2/n) ) ))
    
    # Khởi tạo bộ đếm thời gian
    timer = Timer()
    timer2 = Timer()
    timer.start()
    
    print("********** PHASE 1: SETTING UP SYSTEM ")
    # Thiết lập các thông số cơ bản và chuẩn bị ma trận Minkowski
    setup_params(fval,qval,sval)
    prepare_matrices()
    
    print("Computing the adjustment factor for s.")
    # cembs: Số lượng các cặp nghiệm phức (embeddings)
    cembs = (n - len(N.embeddings(RR)))/2
    # detscale: Hệ số điều chỉnh dựa trên định thức của vành (discriminant) để khớp với không gian Minkowski
    detscale = RP( ( 2^(-cembs)*sqrt(abs(f.discriminant())) )^(1/n) ) # adjust the sigma,s
    
    # Điều chỉnh tham số s và độ lệch chuẩn sig theo cấu trúc hình học của vành
    sval = sval*detscale
    sig = sig*detscale
    
    print("Adjusted s for use with this embedding, result is ", sval)
    
    # Khởi tạo bộ lấy mẫu nhiễu Gaussian sau khi đã điều chỉnh sig
    initiate_sampler()
    
    print("The sampler has been created with sigma = ", sampler.sigma)
    print("Sampled vectors will have expected norm ", RDF(sqrt(n)*sampler.sigma))
    
    # Chạy thử nghiệm nhiễu trên 5 mẫu
    error_test(5)
    print("Time for Phase 1: ", timer.stop())
    
    timer.start()
    count_successes = 0
    timer2.start()
    
    # Bắt đầu vòng lặp thử nghiệm (trials)
    for trialnum in range(numtrials):
        print("*~*~*~*~*~*~*~*~*~*~*~*~* TRIAL NUMBER ", trialnum, "*~*~*~*~*~*~*~*~*~*~*~*~*~*~*~*~")
        
        print("********** PHASE 2: CREATE SECRET AND SAMPLES")
        # Tạo khóa bí mật s và các mẫu Ring-LWE (a, b)
        create_secret()
        create_samples(numsampsval)
        
        # Kiểm tra tính đồng cấu của hệ thống trước khi tấn công
        sanity_check()
        print("Time for Phase 2: ", timer.stop())
        
        timer.start()
        print("********** PHASE 3: HISTOGRAMS")
        # Vẽ biểu đồ phân phối lỗi và các giá trị 'a' để quan sát đặc điểm dữ liệu
        histogram_of_errors()
        print("The histogram of errors (above) should be clustered at edges for success.")
        
        histogram_of_as()
        print("The histogram of a’s (above) should be fairly uniform.")
        
        histogram_of_errors_2()
        print("The histogram of sample errors (above) should be clustered at edges for success.")
        print("Time for Phase 3: ", timer.stop())
        
        timer.start()
        print("********** PHASE 4: ATTACK ALGORITHM")
        # Tìm giá trị thực của bí mật mod q (để đối chiếu) và chạy thuật toán tấn công
        secret_mod_q()
        result = alg2(10000,quickflag)
        
        print("Result of Algorithm 2:", result)
        print("Time for Phase 4: ", timer.stop())
        
        # Nếu tìm được đúng bí mật, tăng biến đếm thành công
        if result == True:
            count_successes = count_successes + 1
            
        print("*~*~*~*~*~*~*~*~*~*~*~*~* ", count_successes, " out of ", trialnum+1, " successes so far. *~*~*~*~*~*")
        
    # Kết thúc tất cả các lượt thử, dừng đồng hồ tổng
    totaltime = timer2.stop()
    print("Total time for ", trialnum+1, "trials was ", totaltime)
    
    return count_successes


# # gọi hàm ví dụ
# đa thức cyclotomic bậc 4; # f(1) mod q = 0
f = y^4 + y^3 + y^2 + y + 1    
q = 5 
# sigma => nhiễu siêu nhỏ  q << sigma * sqrt(n)                  
s = 0.1                        

shebang(f, q, s, numsampsval=50, numtrials=5, quickflag=False)


# # Thử với p lớn 
# p_prime = 11
# f = sum(y^i for i in range(p_prime))
# q = p_prime 
# # f(1) mod q = 0
# # q << sigma * sqrt(n) => thành công
# s = 0.1

# shebang(f, q, s, numsampsval=50, numtrials=5, quickflag=True)