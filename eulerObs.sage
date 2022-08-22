import os.path
from collections import Counter
from copy import deepcopy

''' 
    This file computes the Chern-Mather class for each Schubert variety and the
    Chern-Schwartz-MacPherson class for each Schubert cell in a simply laced
    cominuscule Grassmannian, and verifies strong posititivity of the CSM
    classes. It also computes the local Euler obstructions and compares them
    with the value of the Kazhdan-Lusztig polynomials evaluated at q=1. The
    program does not compute these values for largest Schubert variety, i.e.,
    the manifold itself. To include this computation, set the variable
    include_full_manifold to True. The lie_type and rank of the underlying group
    are supplied as the first and second command line argument. The cominuscule
    Grassmannian corresponds to a parabolic subgroup which contains all but one
    simple root. By default, the missing root is taken to be the last root. A
    third optional argument is used to override this behaviour. The output is
    written in a subdirectory named data.
'''

''' Refernces:
    [AM06] Aluffi, Mihalcea, "Chern-Schwartz-MacPherson classes for Schubert
    cells in flag manifolds", Compos. Math., 152(12):2603-2625, 2016.
    [MS20] Mihalcea, Singh, "Mather classes and conormal spaces of Schubert
    varieties in cominuscule spaces", arXiv:2006.04842.
'''

include_full_manifold = False

if len(sys.argv) > 4: 
    raise IndexError("Too many command line arguments")
if len(sys.argv) < 3: 
    raise IndexError("Too few command line arguments")

lie_type = str(sys.argv[1])
rank = int(sys.argv[2])

if len(sys.argv) == 4:
    d = int(sys.argv[3])
else:
    d = rank

###Check for errors in input.
assert 1 <= d <= rank
if lie_type not in ['A', 'D', 'E']:
    raise ValueError("Not a simply laced cominuscule space.")
if lie_type == 'E' and rank not in [6,7]:
    raise ValueError("Rank must equal 6 or 7 in type E.")
if lie_type == 'D' and rank <= 3:
    raise ValueError("Rank must be greater that 3 in type D.")
if lie_type in ['D', 'E'] and rank != d:
    raise ValueError("Not a simply laced cominuscule space.")

W = CoxeterGroup( lie_type + str(rank))
S = [W.simple_root_index(i) for i in W.index_set()]
alpha = [W.roots()[i] for i in S]
alpha = {i+1: root for i, root in enumerate(alpha)}

W3 = CoxeterGroup( lie_type + str(rank), implementation='coxeter3')

def cartan_matrix(W):
    ''' Construct the Cartan matrix of the underlying group.
    '''
    C = [[v for v in row] for row in W.coxeter_matrix()]
    for i in range(len(C)):
        for j in range(len(C[0])):
            x = C[i][j]
            C[i][j] = 2 if x == 1 else 0 if x == 2 else -1
    return Matrix(C)

C = cartan_matrix(W)

''' root_of_reflection is a dictionary. The keys are the reflections r_beta in
    W, and the values the corresponding positive root beta.
'''
root_of_reflection = {
    W.reflections()[root]: root\
        for root in W.roots()\
        if root > 0
}

def pairing(a,b): 
    ''' Takes as input two roots a and b. Returns the bilinear product <a^v,b>,
        where a^v is the coroot dual to a.
    '''
    return a*C*b

def generateWP():
    ''' This function returns a list of elements in W^P sorted by length.
    '''
    new = {W.one()}
    by_len = []
    while new:
        by_len.append(new)
        new = set()
        for w in by_len[-1]:
            for sref in W.simple_reflections():
                v = sref * w
                if v.length() > w.length() and all( v * alpha[i] > 0 for i in range( 1, d)) and all( v * alpha[i] > 0 for i in range( d + 1, rank + 1)):
                    new.add(v)
    new = []
    for sub in by_len:
        for w in sub:
            new.append(w)
    return new

WP = generateWP()
if not include_full_manifold: WP = WP[:-1] 

def lUpdate( root, vec):
    ''' The lUpdate function takes as input a root and a homology class vec
        (stroed as a python dictionary), and updates vec according to the rule
        vec = c_1(L_root) vec. Here c_1(L_root) is the first Chern class of the
        line bundle corresponding to root. Note that vec is updates in-place,
        unlike in tOp.
    '''
    c = deepcopy(vec)
    for w in c:
        for v in w.lower_cover_reflections():
            p = -pairing(root, root_of_reflection[v])
            vec[w*v] += p * c[w]

def tOp( k, vec):
    ''' The variable vec is a homology class in G/B. The function applies the 
        operator T_k to vec and returns a new dictionary containing T_k(vec).
        See Thm 6.4 of [AM06] for more on the operator T_k, and its relation to
        CSM classes.
    '''
    res = Counter()
    for w, cof in vec.items():
        if w * alpha[k] < 0: 
            res[w] -= cof
            continue
        res[w] -= cof
        v = w * W.simple_reflection(k)
        res[v] += cof
        for u in v.lower_cover_reflections(): 
            beta = root_of_reflection[u]
            res[v*u] += cof * pairing( beta, alpha[k])
    return res

def pretty(vec):
    ''' This is a helper function to pretty print the homology class stored in
        vec.
    '''
    return ' + '.join(f'{vec[key]}*{key.reduced_word()}' for key in vec)

def compute_mather_classes():
    ''' This function computes the Mather class for each Schubert subvariety in
        G/P. We use Thm 1.1 of [MS20].
    '''
    Rn = [root for root in W.roots() if root < 0 and d-1 in root.support()]
    ''' Rn is the set of negative roots in the unipotent radical of the
        parabolic subgroup P.
    '''
    cMa=[]
    for w in WP:
        v = Counter([w])
        for beta in Rn:
            if w * beta > 0: 
                lUpdate(beta, v)
        cMa.append([])
        for u in WP:
            cMa[-1].append(v[u])
    return cMa

def compute_csm_classes():
    ''' This function computes the CSM class for each Schubert subvariety in
        G/P. Given w in W^P, we first compute the CSM class of X_B(w) using
        Thm 6.4 of [AM06], and then project this class to G/P.
    '''
    csm=[]
    for w in WP:
        v = Counter([W.one()])
        for k in w.reduced_word(): #T_{w^{-1}}*[X_id]
            v = tOp(k,v)
        csm.append([])
        for u in WP:
            csm[-1].append(v[u])
    # The following line verifies the strong positivity of the CSM class of X_w.
            assert u.bruhat_le(w) == (csm[-1][-1] != 0) 
    return csm

def longest_element_in_WP():
    if lie_type == 'E' and rank == 6:
        assert( d == rank)
        x = CoxeterGroup('D5').long_element().reduced_word()
        for i in range(len(x)):
            y = x[i]
            x[i] = 3 if y==2\
                else 4 if y==3\
                else 2 if y==4\
                else y
    elif lie_type == 'E' and rank == 7:
        assert( d == rank)
        x = CoxeterGroup('E6').long_element().reduced_word()
    elif lie_type == 'D':
        assert( d == rank)
        x = CoxeterGroup( 'A' + str( d - 1)).long_element().reduced_word()
    elif lie_type == 'A':
        x1 = x2 = []
        if d < rank:
            x2 = CoxeterGroup( 'A' + str(rank-d)).long_element().reduced_word()
            x2 = [k+d for k in x2]
        if d > 1:
            x1 = CoxeterGroup( 'A' + str( d - 1)).long_element().reduced_word()
        x = x1 + x2
    return x

def compute_kl():
    W3P = [W3.from_reduced_word(x.reduced_word()) for x in WP]
    wP = W3.from_reduced_word(longest_element_in_WP())
    WPmax = [x*wP for x in W3P]
    klp = []
    for u in WPmax:
        klp.append([])
        for v in WPmax:
            poly = W3.kazhdan_lusztig_polynomial( u, v)
            klp[-1].append( sum(poly.coefficients()))
    return Matrix(klp)

print(f"Computing Mather Classes for {len(WP)} cases")
cMaMatrix = Matrix(compute_mather_classes()).transpose()

print(f"Computing CSM Classes for {len(WP)} cases")
csmMatrix = Matrix(compute_csm_classes()).transpose()

eulerObsMatrix = csmMatrix.inverse() * cMaMatrix

print(f"Computing KL polynomials for {len(WP)} cases")
klp = compute_kl()

if (klp == eulerObsMatrix):
    print("The Euler obstructions equal the Kazhdan-Lusztig polynomials evaluated at q = 1")
else:
    print("The Euler obstructions do not equal the Kazhdan-Lusztig polynomials evaluated at q = 1")

WP = [x.reduced_word() for x in WP]
with open(\
        os.path.join(\
            'data',
            lie_type + ' ' + str(rank) + ' ' + str(d) + '.txt'),\
        'w') as f:
    f.write(str(WP)[1:-1])
    f.write('\nMather Classes\n') 
    f.write(cMaMatrix.str())
    f.write('\nCSM classes\n')
    f.write(csmMatrix.str())
    f.write('\nEuler Obstructions\n')
    f.write(eulerObsMatrix.str())
    f.write('\nKazhdan-Lusztig Polynomial evaluated at q=1\n')
    f.write(klp.str())
    if klp == eulerObsMatrix: 
        f.write('\nThe characteristic cycle is irreducible.')
    else:
        f.write('\nThe characteristic cycle is not irreducible.')

