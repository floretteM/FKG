from fpylll import *

""" a: multiplier
    N: modulus
    m: nb of outputs
    ell: nb of truncated bits
"""
def LCG(a,N,m,ell,x0 = 0):
    if x0 == 0:
        x0 = ZZ.random_element(1,N-1)
    res = []
    x = int(x0)
    for i in range(m):
        res.append(x >> ell)
        x = (a*x) % N
    return(x0,res)

def transform(Y,ell):
    H=[]
    for y in Y:
        H.append(y*2^ell + 2^(ell-1))
    return(H)

#################
### a,N known ###
#################

### CVP ###

def attack_CVP(H,a,N,m,ell):
    #straight forward attack using a CVP solver. Inconvenient: expensive

    lattice = matrix(m)
    for i in range(m):
        lattice[i,i] = N 
        lattice[0,i] = (a**i) % N
    lattice  = IntegerMatrix.from_matrix(lattice)
    lattice = fplll.lll.lll_reduction(lattice)
    target = tuple(vector(H[:m]))
    x0 = CVP.closest_vector(lattice,target)[0]

    return x0

### Frieze ###

def attack_frieze(H,a,N,m,ell):

    M = matrix(m)
    for i in range(1,m):
        M[i,i] = -1
        M[i,0] = (a**i) % N
    M[0,0] = N
    M = IntegerMatrix.from_matrix(M)
    M = fplll.lll.lll_reduction(M)
    M = matrix(M)
    v = vector(H[:m])
    temp = (M*v)/N
    K = vector(ZZ,[round(t) for t in temp])
    X = M.solve_right(N*K)
    x0 = X[0]
    return x0

#########################
### a unkown, N known ###
#########################

### Stern ###

def find_polynomial_simple(H,N,ell):
    """ Input:  H is the modified ouputs of a LCG (public)
                N he modulus (public)
                ell the number of truncated bits  (public)
                r,d parameters to choose      
        Output: a vector "target" such that <target,H_i> = 0 [N]. """

    mp = len(H)
    d = (mp+1)//2
    r = mp+1 - d

    block_H = matrix(d,r)
    for i in range(d):
        for j in range(r):
            block_H[i,j] = H[i+j]
    M=block_matrix(2,2,[2**(ell-1)*identity_matrix(d),block_H,matrix(r,d),N*identity_matrix(r)])
    M = IntegerMatrix.from_matrix(M)
    M=fplll.lll.lll_reduction(M)
    M=matrix(M)
    target = vector(ZZ,vector(ZZ,M[0][:d])/(2**(ell-1)))
    return(target)

def attack_simple_stern(H,N,mp,ell):
    """ Input:  H is the modified ouputs of a LCG (public)
                N the modulus (public)
                ell the number of truncated bits  (public)
                r is a parameter to choose       
        Output: a, the secret multiplier """

    m = len(H)
    d = (mp+1)//2
    R.<z> = Integers(N)[]
    coeff = find_polynomial_simple(H[:mp],N,ell)
    P1 = sum([coeff[i]*z^i for i in range(d)])
    P1 =R(P1)

    d = (mp+1)//2
    coeff2 = find_polynomial_simple(H[d:d+mp],N,ell)
    P2 = sum([coeff2[i]*z^i for i in range(d)])
    P2=R(P2)
    P = GCD(P1,P2)

    if P.degree() != 1:
        return
    
    y0 = P[0]
    y1 = P[1]

    if y1.is_unit():
        abis = -y0/y1 % N
        x0bis = attack_frieze(H,abis,N,m,ell)
        return(x0bis,abis)

def check_consistency(x0bis,abis,N,ell,H):
    m = len(H)
    Ybis = LCG(abis,N,m,ell,x0bis)[1]
    Hbis = transform(Ybis,ell)
    return(H==Hbis)

def attack_simple_stern_alt(H,n,ell):
    """ Input:  H is the modified ouputs of a LCG (public)
                N =2^n the modulus (public)
                ell the number of truncated bits  (public)
                r,d parameters to choose       
        Output: a, the secret multiplier """
    m =len(H)
    d = (m+1)//2
    N=2^n
    coeff = find_polynomial_simple(H,N,ell)
    R.<z> = ZZ[]
    P = sum([coeff[i]*z^i for i in range(d)])
    roots=[]
    if P(0) % 2 == 0:
        roots.append(0)
    if P(1) % 2 == 0:
        roots.append(1)
    for i in range(1,n+1):
        new_roots = []
        for a0 in roots:
            if P(a0) %2^i == 0:
                new_roots.append(a0)
            if P(a0+2^(i-1)) %2^i == 0:
                new_roots.append(a0+2^(i-1))
        roots = new_roots
        if len(roots) > 100 :
            return
    
    for abis in roots:
        x0bis = attack_frieze(H,abis,2^n,m,ell)
        if check_consistency(x0bis,abis,2^n,ell,H):
            return(ZZ(x0bis),ZZ(abis))


### Coppersmith ###

def coppersmith(G,monomials,N,ell,m):
    """ retrieve a little common root of polynomials over a certain modulo
    
    Input:  G a list of polynomials
                monomials the list of monomials appearing in G (in a certain order)
                N the moduli
                ell the size of the unknown root
                m the multiplicity of the root in the polynomials of G (in our case it is the same for all polynomials)"""

    nb_poly = len(G)
    nb_mono = len(monomials)

    # Construction of the matrix described in section 2
    
    M = matrix(QQ,nb_mono+nb_poly)
    for i in range(nb_mono):
        if monomials[i] == 1: 
            M[i,i] = 1
        else:
            M[i,i] = (2^ell)^(-1*monomials[i].degree())

    for j in range(nb_poly):
        M[nb_mono+j,nb_mono+j] = N^m
        for i in range(nb_mono):
            M[i,nb_mono+j] = G[j].monomial_coefficient(monomials[i])
                   
    # LLL
    M=M.LLL()
    
    
    # recuperation of the smallest vector with the correct form
    
    i=0
    
    while i < nb_mono+nb_poly and  abs(M[i,0]) == 0:
        i=i+1
    if i != nb_mono+nb_poly : 
        v = M[i,0]^-1*M[i]
        v_final = 2^ell*v

        return v_final
        
    return 0 #In the case the algorithm fails

def attack_Coppersmith(H,N,ell):
    """ Input:  H is the modified ouputs of a LCG (public)
                N he modulus (public)
                ell the number of truncated bits  (public)

                
        Output: the secret seed. """ 
        
    m = len(H)
    Ring = Integers(N)

        
    d_var = var(['d'+ str(i) for i in range(m)])
    R = PolynomialRing(ZZ,d_var)
    d= [R(variable) for variable in d_var]
    
    G=[]                            # G is the list of polynomials used in the Coppersmith method
    list_monomials = [d[0]^0] + d  
    
    for i in range(1,m):
        for j in range(i+1,m):
            P = d[i]*d[j-1] - d[i-1]*d[j] + H[i]*d[j-1] + H[j-1]*d[i] - H[j]*d[i-1] - H[i-1]*d[j] + (H[i]*H[j-1] - H[i-1]*H[j])
            P=R(P)
            G.append(P)
            list_monomials.append(d[i]*d[j-1])
            list_monomials.append(d[i-1]*d[j])
    
    res_cop = coppersmith(G,list_monomials,N,ell-1,1)
    
    return([H[i] + res_cop[i+1] for i in range(m)]) 


###########################
### a unkown, N unknown ###
###########################

### Stern ###

def find_coeff_full(Y,K,r,d,ell):
    """ Input:  H is the modified ouputs of a LCG (public)
                N he modulus (public)
                ell the number of truncated bits  (public)
                r,d are parameters to choose

                
        Output: a vector "target" such that <target,H_i> = 0 . """    

    block_Y = matrix(d,r)
    for i in range(d):
        for j in range(r):
            block_Y[i,j] = Y[i+j]
    M=block_matrix(1,2,[identity_matrix(d),K*block_Y])
    M = IntegerMatrix.from_matrix(M)
    M=fplll.lll.lll_reduction(M)
    M=matrix(M)
    target = vector(ZZ,M[0][:d])
    return(target)

def attack_stern(n,Y,r,d,ell):
    """ Input:  H is the modified ouputs of a LCG (public)
                N he modulus (public)
                ell the number of truncated bits  (public)
                r is a parameter to choose

                
        Output: a, the secret multiplier and N, the secret modulus """
    s=4
    #r = ceil(n/(n-ell))
    #d = ceil(sqrt(2*(n-ell)*r))
    b=(n-ell +log(d,2) -1)*r/(d-r)
    B=2^b
    K = ceil(sqrt(d)*2^(d-1)/2*B)
    R.<z> = ZZ[]
    coeff = find_coeff_full(Y,K,r,d,ell)
    P = sum([coeff[i]*z^i for i in range(d)])
    coeff_2 = find_coeff_full(Y[r:],K,r,d,ell)
    P2 = sum([coeff_2[i]*z^i for i in range(d)])
    coeff_3 = find_coeff_full(Y[2*r:],K,r,d,ell)
    P3 = sum([coeff_3[i]*z^i for i in range(d)])
    R1 = P.resultant(P2,z)
    R2 = P.resultant(P3,z)
    R3 = P2.resultant(P3,z)
    N=GCD(R1,R2)
    N=GCD(N,R3)
    #If we do not use the fact that N is prime the probability to obtain the good N seems to be around 50%
    if N <= 1 :
        return
    N = N.factor()[-1][0]
    # The other factors of N are small so this step is not costly

    R.<z> = Integers(N)[]
    P=R(P)
    P2=R(P2)
    P3=R(P3)
    P=GCD(P,P2)
    P=GCD(P,P3)
    if P.degree() != 1 :
        return

    y0 = P[0]
    y1 = P[1]

    if y1.is_unit():
        abis = -y0/y1 % N
        x0bis = attack_frieze(transform(Y,ell),abis,N,r,ell)
        return(x0bis,abis,N)


    return(N)


def coeff_th(n,ell,r):
    if n > 100:
        d = ceil(sqrt(2*(n-ell)*r))
    else :
        d = ceil(sqrt(2*n*r))
    print('r,d,m',r,d,3*r+d)
   

