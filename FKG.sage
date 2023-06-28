from time import *

poly32 = [0,1,2,22]     #feedback polynomial for n=32
poly64 = [0,60,61,63]   #feedback polynomial for n=64
poly1024 = [0,1,6,19]   #feedback polynomial for n=1024

############
### PRNG ###
############

def LFSR(x0,feedback_polynomial):
    """ Input:  x0 (n bits)
                feedback_polynomial
                
        Output: x1 (n bits)"""
        
    last_coeff = sum([x0[p] for p in feedback_polynomial])
    x1=x0[1:] + [last_coeff]
    return x1


def FKG(n,ell,m,feedback_polynomial):
    """ FKG stands for Fast Knapsack Generator
    
        Input:  n is the number of initial bits / size of the integers / 2^n is the modulus (public)
                l the number of truncated bits  (public)
                m the number of outputs         (public)    
                feedback_polynomial is the feed back polynomial of the LFSR (public)
                
        Output: x0 is part of the the seed of the PRNG : the initial control bits (secret)
                y,z are part of the seed : use to compute the weights (secret)
                Y is the output of the PRNG (public)
                
        Here the secret parameters are generated in the algorithm and not chosen by the user. """
        
        
    Ring = Integers(2^n)

    x0 = [GF(2).random_element() for i in range(n)] 
    
    U = [x0]
    for i in range(m-1):
        U.append(LFSR(U[-1],feedback_polynomial))
    U=matrix(U)                                     # all the control bits
    
    y = Ring.random_element()
    if y.is_unit() == False :
        y = Ring(y+1)
    
        
    z = Ring.random_element()
    if z.is_unit() == False:
        z = Ring(z+1)
        
    w = vector(Ring,[y*z**(n-j) for j in range(n)]) # The weights
    U=matrix(ZZ,U)
    v = U*w
    
    Y=[]                                           
    for i in range(m):
        Y.append(ZZ(v[i])//2^ell)

    return x0,y,z,v,Y
    
def output(vi,ell):
    """ Transform an internal state vi in a modified output Hi.
    
        Input:  vi an internal state
                l the number of discarded bits
                
        Output: Hi the modified output corresponding to vi"""
        
    res = (ZZ(vi)//(2^ell))*2^ell+2^(ell-1)
    return res      
        
            

###############
### Attacks ###
###############

def finding_y(H,n,ell,z,i,vi):
    """ Input:  H is the modified ouputs of a FKG (public)
                n is the number of initial bits / size of the integers / 2^n is the modulus (public)
                l the number of truncated bits  (public)
                z is part of the seed of the FKG (computed in the previous step)
                vi is an internal state (computed in the previous step)    
                i is the index of the internal state
                
        Output: y,z """

    
    m=len(H)
    Ring = Integers(2^n)
    z = Ring(z)
    if i > m-3:     #As we want to work on the vi+1 and vi+2, we need vi+1 and vi+2 to exist
        return 0
        
    R.<d1,d2> = ZZ[]
    monomials = [d1^0,d1,d2]
    
    a=z^(-1)
    
    #Case 1 and 2 : vi+1 = z*vi + X, vi+2 = z*vi+1 + X with X = zy or -z^(n+1)
                    
    P = ZZ(z+1)*(H[i+1] + d1) - (H[i+2] + d2) - ZZ(z)*vi    
    P = R(P) % 2^n

    deltas  = coppersmith([P],monomials,2^n,ell,1)
    if deltas != 0 and deltas.denominator() == 1:
         
        vi_1 = Ring(H[i+1] + deltas[1])
        vi_2 = Ring(H[i+2] + deltas[2])
        X = Ring(vi_1-z*vi)    
        y = a*X     #case 1
        flag = check_consistency_FKG(H,n,ell,z,i+2,vi_2,y)
        if flag :
            return y,z
                
        y = a^(n+1)*(-X)    #case 2
        flag = check_consistency_FKG(H,n,ell,z,i+2,vi_2,y)
        if flag :
            return y,z
             
    #Case 3: vi+1 = zvi + zy, vi+2 = zvi+1 -z^n+1y
    
    P = H[i+2] + d2 + ZZ(z^n-z)*(H[i+1] + d1) - ZZ(z^(n+1))*vi
    P = R(P) % 2^n

    deltas  = coppersmith([P],monomials,2^n,ell,1)
    if deltas != 0 and deltas.denominator()==1:
        vi_1 = Ring(H[i+1] + deltas[1])
        vi_2 = Ring(H[i+2] + deltas[2])     
                
        y = a*(vi_1-z*vi)
        flag = check_consistency_FKG(H,n,ell,z,i+2,vi_2,y)
        if flag :
            return y,z
                
    #Case 4: vi+1 = zvi + -z^n+1y, vi+2 = zvi+1 +zy
    
    P =-ZZ(z^n)*(H[i+2] + d2) + ZZ(z^(n+1)-1)*(H[i+1] + d1) + ZZ(z)*vi
    P = R(P) % 2^n   


    deltas  = coppersmith([P],monomials,2^n,ell,1)
    if deltas != 0 and deltas.denominator() == 1:
        vi_1 = Ring(H[i+1] + deltas[1])
        vi_2 = Ring(H[i+2] + deltas[2])
                
        y = a*(vi_2-z*vi_1)
        flag = check_consistency_FKG(H,n,ell,z,i+2,vi_2,y)
        if flag :
            return y,z                             
              
    #Case 5: vi+1 = zvi + zy, vi+2 = zvi+1 +zy -z^n+1y

    P = H[i+2] + d2 + ZZ(z^n-1-z)*(H[i+1] + d1) - ZZ(z*(z^n-1))*vi
    P = R(P) % 2^n        

    deltas  = coppersmith([P],monomials,2^n,ell,1)
    if deltas != 0 and deltas.denominator() == 1: 
        vi_1 = Ring(H[i+1] + deltas[1])
        vi_2 = Ring(H[i+2] + deltas[2])
                
        y = a*(vi_1-z*vi)
        flag = check_consistency_FKG(H,n,ell,z,i+2,vi_2,y)
        if flag :
            return y,z

    #Case 6: vi+1 = zvi + zy -z^n+1y, vi+2 = zvi+1 +zy
    
    P = -ZZ(z^n-1)*(H[i+2] + d2) + ZZ(z^(n+1)-z-1)*(H[i+1] + d1) + ZZ(z)*vi
    P = R(P) % 2^n         

      
    deltas  = coppersmith([P],monomials,2^n,ell,1)
    if deltas != 0 and deltas.denominator() == 1: 
        vi_1 = Ring(H[i+1] + deltas[1])
        vi_2 = Ring(H[i+2] + deltas[2])
        
        y = a*(vi_2-z*vi_1)
        flag = check_consistency_FKG(H,n,ell,z,i+2,vi_2,y)
        if flag :
            return y,z

    #Case 7: vi+1 = zvi -z^n+1y, vi+2 = zvi+1 +zy - z^(n+1)y
    
    P = H[i+2] + d2 + ZZ(a^n-z-1)*(H[i+1] + d1) + ZZ(z-a^(n-1))*vi
    P = R(P) % 2^n    

    deltas  = coppersmith([P],monomials,2^n,ell,1)
    if deltas != 0 and deltas.denominator()==1: 
        vi_1 = Ring(H[i+1] + deltas[1])
        vi_2 = Ring(H[i+2] + deltas[2])
                
        y = -z^(-n-1)*(vi_1-z*vi)
        flag = check_consistency_FKG(H,n,ell,z,i+2,vi_2,y)
        if flag :
            return y,z 

    #Case 8: vi+1 = zvi + zy -z^n+1y, vi+2 = zvi+1 - z^(n+1)y
    
    P = ZZ(z^(-n)-1)*(H[i+2] + d2) + ZZ(1+z-z^(-n+1))*(H[i+1] + d1) - ZZ(z)*vi 
    P = R(P)%2^n      

    deltas  = coppersmith([P],monomials,2^n,ell,1)
    if deltas != 0 and deltas.denominator()==1: 
        vi_1 = Ring(H[i+1] + deltas[1])
        vi_2 = Ring(H[i+2] + deltas[2])
                
        y = -z^(-n-1)*(vi_2-z*vi_1)
        flag = check_consistency_FKG(H,n,ell,z,i+2,vi_2,y)
        if flag :
            return y,z
            
    return 0
    
  
    
    
def check_consistency_FKG(H,n,ell,z,i_0,vi_0,y):
    """ Input:  H is the modified ouputs of a FKG (public)
                n is the number of initial bits / size of the integers / 2^n is the modulus (public)
                ell the number of truncated bits  (public)
                y,z are part of the seed of the FKG (computed in the previous step)
                vi_0 is an internal state (computed in the previous step)    
                i_0 is the index of the internal state
                
        Output: A boolean 
        
        Warning : does not work for very few outputs (explained in test)"""                
     
    vi = vi_0
    i = i_0           
    while i < len(H)-1 :
        i=i+1
        if H[i] == output(z*vi,ell):
            vi = z*vi
        elif H[i] == output(z*vi + z*y,ell) :
            vi = z*vi + z*y
        elif H[i] == output(z*vi -z^(n+1)*y,ell) :
            vi = z*vi -z^(n+1)*y
        elif H[i] == output(z*vi + z*y-z^(n+1)*y,ell):
            vi = z*vi + z*y-z^(n+1)*y
        else :
            return False
            
    # Backward  
        
    a = z^(-1)
    vi = vi_0
    i = i_0          
    
    while i > 0 :
        i=i-1
        if H[i] == output(a*vi,ell):
            vi = a*vi
        elif H[i] == output(a*vi - y,ell) :
            vi = a*vi - y
        elif H[i] == output(a*vi + z^n*y,ell) :
            vi = a*vi + z^n*y
        elif H[i] == output(a*vi -y +z^n*y,ell):
            vi = a*vi -y +z^n*y
        else :
            return False
    
    return True    
    
    
### Attack with consecutive outputs ###

def attack_FKG_consecutive(Y,n,l,k):
    """ Input:  Y is the ouputs of a FKG (public)
                n is the number of initial bits / size of the integers / 2^n is the modulus (public)
                l the number of truncated bits  (public)
                k the number of consecutive outputs we will use to retrieve z
                
        Output: (y,z) if the algorithm works, else 0 """
         
    m=len(Y)
    Ring = Integers(2^n)
    H = transform(Y,l)
        
    for track in range(m-k):
        
        # Finding z
        Hbis = H[track:track+k+1]
        v = attack_Coppersmith(Hbis,2^n,l)
        flag = True
        for i in range(k+1):
            if v[i] not in ZZ:
                flag = False

        if flag:       # Else our first assumption is FALSE
            v0=v[0]
            v1=v[1]
            padic_v0 = log(gcd(v0,2^n),2)   # The 2-adic valuations of v0
            padic_v1 = log(gcd(v1,2^n),2)                     
            
            if padic_v0 == padic_v1 :
                z = Ring(v1/v0)        
                for r in range(2^padic_v0):
                    z = z + r*2^(n-padic_v0)
                    if ZZ(z) % 2 ==1 :
                    #Finding y 
                        vk=ZZ(v[k])
                        temp = finding_y(H,n,l,z,track+k,vk)
                        if temp !=0:
                            return temp
    return 0
    
### Attack with non consecutive outputs ###

def attack_LCG_sparse(H,n,l,index):
    """ Input:  H is the modified ouputs of a FKG (public)
                n is the number of initial bits / size of the integers / 2^n is the modulus (public)
                l the number of truncated bits  (public)
                index is the ouputs we are going to use to retrieve z
                
        Output: the troncated bits used to reconstruct the internal states. """  
        
    m = len(H)
    Ring = Integers(2^n)

    d_var = var(['d'+ str(i) for i in range(m)])
    R = PolynomialRing(ZZ,d_var)
    d= [R(variable) for variable in d_var]   
     
    G=[]                        # G is the list of polynomials used in the Coppersmith method                
    list_monomials = [d[0]^0]
    
    var_nb = 0                  # number of variables
    len_index= len(index)
    
    for i in range(len_index):   
        if d[index[i]-1] not in list_monomials:
            list_monomials.append(d[index[i]-1])
            var_nb +=1
        if d[index[i]] not in list_monomials:
            list_monomials.append(d[index[i]]) 
            var_nb +=1  
    for i in range(len_index):
        for j in range(i+1,len_index):
            P = d[index[i]]*d[index[j]-1] - d[index[i]-1]*d[index[j]] + H[index[i]]*d[index[j]-1] + H[index[j]-1]*d[index[i]] - H[index[j]]*d[index[i]-1] - H[index[i]-1]*d[index[j]] + (H[index[i]]*H[index[j]-1] - H[index[i]-1]*H[index[j]])
            P = R(P)
            G.append(P)
                
         
            list_monomials.append(d[index[i]]*d[index[j]-1])
            list_monomials.append(d[index[i]-1]*d[index[j]])
     
    #list_monomials.sort()
    res = coppersmith(G,list_monomials,2^n,l-1,1)
    
    #if res.denominator() != 1:
        #return 0
    deltas = {}
    for i in range(len_index):
        deltas[index[i]-1] = res[list_monomials.index(d[index[i]-1])]
        deltas[index[i]] = res[list_monomials.index(d[index[i]])]
    
    #return (H[0] + res[1]) #to use the test function

    return deltas
    
def update(index,m):
    

    k = len(index)
    i0 = k-1
    while i0 <= k and index[i0] == m-(k-i0) :
        i0 -= 1
        
    if i0 == -1:
        return 'end'
        
    index[i0] += 1
    for i in range(i0+1,k):
        index[i] = index[i-1] + 1
    return index    


def attack_FKG_sparse(Y,n,l,k):
    """ Input:  Y is the ouputs of a FKG (public)
                n is the number of initial bits / size of the integers / 2^n is the modulus (public)
                l the number of truncated bits  (public)
                k the number of consecutive outputs we will use to retrieve z
                
        Output: (y,z) if the algorithm works, else 0 """
        
        
    Ring = Integers(2^n)
    m = len(Y)
    
    H=[]
    for yi in Y:
        H.append(ZZ(yi*2^l + 2^(l-1)))    
    
    index = [i for i in range(1,k+1)]
    dico={}
    
    while index != 'end' :
        deltas = attack_LCG_sparse(H,n,l,index)
        if deltas != 0 :
            if (vector(deltas.values())).denominator() == 1:       # Else our first assumption is FALSE
                v0=H[index[0]-1]+deltas[index[0]-1]
                v1=H[index[0]]+deltas[index[0]]
                
                padic_v0 = log(gcd(v0,2^n),2)   # The 2-adic valuations of v0
                padic_v1 = log(gcd(v1,2^n),2)                     
            
                if padic_v0 == padic_v1 :
                    z = Ring(v1/v0)        
                    for r in range(2^padic_v0):
                        z = z + r*2^(n-padic_v0)
                        if ZZ(z) % 2 ==1 :
                        #Finding y 
                            vk=ZZ(H[index[k-1]]+deltas[index[k-1]])
                            temp = finding_y(H,n,l,z,index[k-1],vk)
                            if temp !=0:
                                return temp
        index = update(index,m)
    return 0

#############
### Stern ###
#############

def attack_FKG_stern(Y,n,ell,k):
    """ Input:  Y is the ouputs of a FKG (public)
                n is the number of initial bits / size of the integers / 2^n is the modulus (public)
                l the number of truncated bits  (public)
                r the number of consecutive outputs we will use to retrieve z
                
        Output: (y,z) if the algorithm works, else 0 """
         
    H=transform(Y,ell)
    m=len(H)
    Ring = Integers(2^n)
    N=2^n     
    if (k+2) %2 == 0:
        r=(k+2)//2
        d=(k+2)//2
    else :
        d=(k+2)//2
        r=d+1

    for track in range(m-k):
        #print("entree dans la boucle")
        # Finding z
        Hbis = H[track:track+k+1]
        tmp = attack_simple_stern_alt(Hbis,n,r,d,ell)
        if tmp == None:
            continue
        v0,z = tmp
        vk = v0*pow(z,k,2^n)%2^n
        temp = finding_y(H,n,ell,z,track+k,vk)
        if temp !=0:
            return temp
    return 0
    
#################################
### Mofification/Optimisation ###
#################################

def finding_y_modified(H,n,l,z,list_j,list_vj):
    """ Input:  H is the modified ouputs of a FKG (public)
                n is the number of initial bits / size of the integers / 2^n is the modulus (public)
                l the number of truncated bits  (public)
                z is part of the seed of the FKG (computed in the previous step)
                list_vj is a list of internal states (computed in the previous step)    
                list_j is the indexes of the internal states
                
        Output: y,z (or 0 if it doesn't work)
        
        if we are from "attack_FKG_consecutive", list_vj = [v_j], list_j =[j]
        if we are from "attack_FKG_sparse", list_vj = V1, list_j = index """


    m=len(H)
    k=len(list_vj)
    
    Ring = Integers(2^n)
    R.<d1,d2> = ZZ[]
    monomials = [d1^0,d1,d2]

    a=z^(-1)
        
    for p in range(k):
        j=list_j[p]
        vj=list_vj[p]
        
        #Forward 
        
        # We search i such that vi=z*vi-1 but vi+1 !=z*vi
        i=j
        vi=vj
    
        while i <= m-2 and H[i+1] == output(z*vi,l) :
            i = i+1
            vi = Ring(z*vi) 
            
        #We are going to work on vi+1 and vi+2
            
        if i < m-2 : #else there is no vi+1 and vi+2 
            
            #Case n1 and n2: vi+1 = z*vi + X and vi+2 = z*vi+1 + X with X=zy or -z^n+1y
                      
            P = (ZZ(z+1)*(H[i+1] + d1) - (H[i+2] + d2) - ZZ(z)*vi) % 2^n
            P = R(P)
            
            di  = coppersmith([P],monomials,2^n,l,1)
            if di != 0 and di.denominator() == 1 : 
                vi_1 = Ring(ZZ(H[i+1]) + di[1])
                vi_2 = Ring(ZZ(H[i+2]) + di[2])
                X = Ring(vi_1-z*vi)
                
                y = a*X
                flag = check_consistency_FKG(H,n,l,z,i+2,vi_2,y)
                if flag :
                    return y,z
                
                y = a^(n+1)*(-X)
                flag = check_consistency_FKG(H,n,l,z,i+2,vi_2,y)
                if flag :
                    return y,z
              
            #Case n3: vi+1 = zvi + zy, vi+2 = zvi+1 -z^n+1y
            P = (H[i+2] + d2 + ZZ(z^n-z)*(H[i+1] + d1) - ZZ(z^(n+1))*vi) % 2^n
            P = R(P)         

            di  = coppersmith([P],monomials,2^n,l,1)
            if di != 0 and di.denominator()==1: 
                vi_1 = Ring(ZZ(H[i+1]) + di[1])
                vi_2 = Ring(ZZ(H[i+2]) + di[2])
                
                
                y = z^(-1)*(vi_1-z*vi)
                flag = check_consistency_FKG(H,n,l,z,i+2,vi_2,y)
                if flag :
                    return y,z
                
            #Case n4: vi+1 = zvi + -z^n+1y, vi+2 = zvi+1 +zy
            P = (-ZZ(z^n)*(H[i+2] + d2) + ZZ(z^(n+1)-1)*(H[i+1] + d1) + ZZ(z)*vi) % 2^n
            P = R(P)         

            di  = coppersmith([P],monomials,2^n,l,1)
            if di != 0 and di.denominator() == 1:
                vi_1 = Ring(ZZ(H[i+1]) + di[1])
                vi_2 = Ring(ZZ(H[i+2]) + di[2])
                
                
                y = z^(-1)*(vi_2-z*vi_1)
                flag = check_consistency_FKG(H,n,l,z,i+2,vi_2,y)
                if flag :
                    return y,z                             
              
            #Case n5: vi+1 = zvi + zy, vi+2 = zvi+1 +zy -z^n+1y
            P = (H[i+2]+d2 + ZZ(z^n-1-z)*(H[i+1] + d1) - ZZ(z*(z^n-1))*vi) % 2^n
            P = R(P)         

            di  = coppersmith([P],monomials,2^n,l,1)
            if di != 0 and di.denominator() == 1: 
                vi_1 = Ring(ZZ(H[i+1]) + di[1])
                vi_2 = Ring(ZZ(H[i+2]) + di[2])
                
                
                y = z^(-1)*(vi_1-z*vi)
                flag = check_consistency_FKG(H,n,l,z,i+2,vi_2,y)
                if flag :
                    return y,z

            #Case n6: vi+1 = zvi + zy -z^n+1y, vi+2 = zvi+1 +zy
            P = (-ZZ(z^n-1)*(H[i+2] + d2) + ZZ(z^(n+1)-z-1)*(H[i+1] + d1) + ZZ(z)*vi) % 2^n
            P = R(P)         
      
            di  = coppersmith([P],monomials,2^n,l,1)
            if di != 0 and di.denominator() == 1: 
                vi_1 = Ring(ZZ(H[i+1]) + di[1])
                vi_2 = Ring(ZZ(H[i+2]) + di[2])
                
                
                y = z^(-1)*(vi_2-z*vi_1)
                flag = check_consistency_FKG(H,n,l,z,i+2,vi_2,y)
                if flag :
                    return y,z

            #Case n7: vi+1 = zvi -z^n+1y, vi+2 = zvi+1 +zy - z^(n+1)y
            P = (H[i+2] + d2 + ZZ(a^n-z-1)*(H[i+1] + d1) + ZZ(z-a^(n-1))*vi) % 2^n
            P = R(P)         

            di  = coppersmith([P],monomials,2^n,l,1)
            if di != 0 and di.denominator()==1: 
                vi_1 = Ring(ZZ(H[i+1]) + di[1])
                vi_2 = Ring(ZZ(H[i+2]) + di[2])
                
                
                y = -z^(-n-1)*(vi_1-z*vi)
                flag = check_consistency_FKG(H,n,l,z,i+2,vi_2,y)
                if flag :
                    return y,z 

            #Case n8: vi+1 = zvi + zy -z^n+1y, vi+2 = zvi+1 - z^(n+1)y
            P = (ZZ(z^(-n)-1)*(H[i+2]+d2) + ZZ(1+z-z^(-n+1))*(H[i+1] + d1) - ZZ(z)*vi) % 2^n
            P = R(P)         

            di  = coppersmith([P],monomials,2^n,l,1)
            if di != 0 and di.denominator()==1: 
                vi_1 = Ring(ZZ(H[i+1]) + di[1])
                vi_2 = Ring(ZZ(H[i+2]) + di[2])
                
                
                y = -z^(-n-1)*(vi_2-z*vi_1)
                flag = check_consistency_FKG(H,n,l,z,i+2,vi_2,y)
                if flag :
                    return y,z    
     
        # Backward
        
        # We search i st vi = z^-1*vi+1 but vi-1 != z^-1*vi+1
        i=j
        vi=vj

        while i != 0 and H[i-1] == output(a*vi,l) :
            i = i-1
            vi = a*vi
            

        #We are going to work on vi-1 and vi-2
        if i > 1 : 
            
            #Case n1 and n2: vi-1 = a*vi + X and vi-2 = a*vi-1 + X with X=-y or z^ny         
            P = (- (H[i-2]+d2) + ZZ(a+1)*(H[i-1] + d1) - ZZ(a*vi)) % 2^n
            P = R(P)
            
            di  = coppersmith([P],monomials,2^n,l,1)
            if di != 0 and di.denominator()==1: 
                vi_1 = Ring(ZZ(H[i-1]) + di[1])
                vi_2 = Ring(ZZ(H[i-2]) + di[2])
                X = Ring(vi_1-a*vi)
                
                y = -X
                
                flag = check_consistency_FKG(H,n,l,z,i-2,vi_2,y)
                if flag :
                    return y,z
                
                y = pow(z,-n,2^n)*X
                
                flag = check_consistency_FKG(H,n,l,z,i-2,vi_2,y)
                if flag :
                    return y,z
              
            #Case n3: vi-1 = avi - y, vi-2 = avi-1 + z^ny
            P = (H[i-2] + d2 - ZZ(z^n+a)*(H[i-1] + d1) + ZZ(z^(n-1))*vi) % 2^n
            P = R(P)         
            
            di  = coppersmith([P],monomials,2^n,l,1)
            if di != 0 and di.denominator()==1: 
                vi_1 = Ring(ZZ(H[i-1]) + di[1])
                vi_2 = Ring(ZZ(H[i-2]) + di[2])
                
                
                y = a*vi - vi_1
                
                flag = check_consistency_FKG(H,n,l,z,i-2,vi_2,y)
                if flag :
                    return y,z
                
            #Case n4: vi-1 = avi + +z^ny, vi-2 = avi-1 -y
            P = (-ZZ(z^n)*(H[i-2]+d2 + ZZ(z^(n-1)-1)*(H[i-1] + d1) + ZZ(a)*vi)) % 2^n
            P = R(P)         

            
            di  = coppersmith([P],monomials,2^n,l,1)
            if di != 0 and di.denominator()==1: 
                vi_1 = Ring(ZZ(H[i-1]) + di[1])
                vi_2 = Ring(ZZ(H[i-2]) + di[2])
                
                
                y = a*vi_1-vi_2
                
                flag = check_consistency_FKG(H,n,l,z,i-2,vi_2,y)
                if flag :
                    return y,z                              
              
            #Case n5: vi-1 = avi - y, vi-2 = avi-1 -y +z^ny  
            P = (H[i-2] + d2 + ZZ(z^n-1-a)*(H[i-1] + d1) + ZZ(a-z^(n-1))*vi) % 2^n
            P = R(P)         
            
            di  = coppersmith([P],monomials,2^n,l,1)
            if di != 0 and di.denominator()==1: 
                vi_1 = Ring(ZZ(H[i-1]) + di[1])
                vi_2 = Ring(ZZ(H[i-2]) + di[2])
                
                
                y = a*vi-vi_1
                
                flag = check_consistency_FKG(H,n,l,z,i-2,vi_2,y)
                if flag :
                    return y,z 


            #Case n6: vi-1 = avi - y +z^ny, vi-2 = avi-1 - y 
            P = (ZZ(1-z^n)*(H[i-2] + d2) + ZZ(z^(n-1)-a-1)*(H[i-1] + d1) + ZZ(a)*vi) % 2^n
            P = R(P)         
            
            di  = coppersmith([P],monomials,2^n,l,1)
            if di != 0 and di.denominator()==1: 
                vi_1 = Ring(ZZ(H[i-1]) + di[1])
                vi_2 = Ring(ZZ(H[i-2]) + di[2])
                
                
                y = a*vi_1-vi_2
                
                flag = check_consistency_FKG(H,n,l,z,i-2,vi_2,y)
                if flag :
                    return y,z 

            #Case n7: vi-1 = avi +z^ny, vi-2 = avi-1 -y + z^(n)y    
            P = (H[i-2] + d2 + ZZ(a^n-a-1)*(H[i-1] + d1) + ZZ(a*(1-a^n))*vi) % 2^n
            P = R(P)         
            
            di  = coppersmith([P],monomials,2^n,l,1)
            if di != 0 and di.denominator()==1: 
                vi_1 = Ring(ZZ(H[i-1]) + di[1])
                vi_2 = Ring(ZZ(H[i-2]) + di[2])
                
                
                y = a^n*(vi_1-a*vi)
                
                flag = check_consistency_FKG(H,n,l,z,i-2,vi_2,y)
                if flag :
                    return y,z 

            #Case n8: vi-1 = avi - y +z^ny, vi-2 = avi-1 + z^(n)y
            P = (ZZ(1-a^n)*(H[i-2] + d2) + ZZ(a^(n+1)-a-1)*(H[i-1] + d1) + ZZ(a)*vi) % 2^n
            P = R(P)         
            
            di  = coppersmith([P],monomials,2^n,l,1)
            if di != 0 and di.denominator()==1: 
                vi_1 = Ring(ZZ(H[i-1]) + di[1])
                vi_2 = Ring(ZZ(H[i-2]) + di[2])
                
                
                y = a^n*(vi_2-a*vi_1)
                
                flag = check_consistency_FKG(H,n,l,z,i-2,vi_2,y)
                if flag :
                    return y,z                    
                    
                               
    return 0
        
############
### Test ###
############

def test_coppersmith(n,ell,m,feedback_polynomial,k,run):
    instances = []
    for i in range(run):
        x0,y,z,v,Y = FKG(n,ell,m,feedback_polynomial)
        instances.append([x0,y,z,v,Y])
    res=0
    T = time()
    for i in range(run):
        [x0,y,z,v,Y] = instances.pop()
        temp = attack_FKG_consecutive(Y,n,ell,k)
        if temp !=0:
            res+=1
    T = time() - T 
    return(T/run, RR(res/run))


def test_stern(n,ell,m,feedback_polynomial,k,run):
    instances = []
    for i in range(run):
        x0,y,z,v,Y = FKG(n,ell,m,feedback_polynomial)
        instances.append([x0,y,z,v,Y])
    res=0
    T = time()
    for i in range(run):
        [x0,y,z,v,Y] = instances.pop()
        temp = attack_FKG_stern(n,ell,k,k,Y)
        if temp !=0:
            res+=1
    T = time() - T 
    return(T/run, RR(res/run))