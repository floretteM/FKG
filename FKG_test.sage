def test_attack_FKG_consecutive(n,ell,k,m):
    instances = []
    if n == 32:
        poly = poly32
    if n == 64 :
        poly = poly64
    if n == 1024 :
        poly = poly1024

    for i in range(10):
        x0,y,z,v,Y = FKG(n,ell,m,poly)
        instances.append([x0,y,z,v,Y])
    res = 0
    T = time()
    for i in range(10):
        x0,y,z,v,Y = instances.pop()
        tmp = attack_FKG_consecutive(Y,n,ell,k)
        if tmp != 0:
            res += 1
    T = time() - T 
    return(1.0*res/10,T/10)

def test_attack_FKG_stern(n,ell,k,m):
    instances = []
    if n == 32:
        poly = poly32
    if n == 64 :
        poly = poly64
    if n == 1024 :
        poly = poly1024

    for i in range(100):
        x0,y,z,v,Y = FKG(n,ell,m,poly)
        instances.append([x0,y,z,v,Y])
    res = 0
    T = time()
    for i in range(100):
        x0,y,z,v,Y = instances.pop()
        tmp = attack_FKG_stern(Y,n,ell,k)
        if tmp != 0:
            res += 1
    T = time() - T 
    return(1.0*res/100,T/100)

def test_attack_LCG_sparse(n,ell,k):
    m = 4*k
    index = [3*i+1 for i in range(k)]
    instances = []
    N=2^n
    for i in range(100):
        a = ZZ.random_element(1,N)
        while a%2 != 1 :
           a = ZZ.random_element(1,N) 
        x0,Y = LCG(a,N,m,ell,0)
        H = transform(Y,ell)
        instances.append([x0,a,H,N])
    res = 0
    T = time()
    for i in range(100):
        [x0,a,H,N] = instances.pop()
        x0bis = attack_LCG_sparse(H,n,ell,index)
        if ZZ(x0) == ZZ(x0bis):
            res+=1
    T = time()-T 
    return(1.0*res/100,T/100)

def test_attack_FKG_sparse(n,ell,k,m):
    instances = []
    if n == 32:
        poly = poly32
    if n == 64 :
        poly = poly64
    if n == 1024 :
        poly = poly1024

    for i in range(20):
        x0,y,z,v,Y = FKG(n,ell,m,poly)
        instances.append([x0,y,z,v,Y])
    res = 0
    T = time()
    for i in range(1):
        x0,y,z,v,Y = instances.pop()
        tmp = attack_FKG_sparse(Y,n,ell,k)
        if tmp != 0:
            res += 1
    T = time() - T 
    return(1.0*res,T)
