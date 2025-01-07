from collections import deque
from itertools import chain


R = GF(101)
variables = 20
names = 'x'


P = PolynomialRing(R, variables, names, order = 'degrevlex')
PP = PolynomialRing(ZZ, variables, names, order = 'degrevlex')

import time

#Gro = [P.1^2+P.2^2,P.1*P.2]
Gro = [P.1^5 + P.2^4 + P.3^3 - 1, P.1^3+P.2^3+P.3^2-1]
#Gro = [P.1^2 - 2*P.2^2, P.1*P.2 - 3]



def without_index(iterable, skip_index):
    for i, item in enumerate(iterable):
        if i != skip_index:
            yield item

            
def compareMonoms(f,g):
    return P(f+g).lm()


def multiVarDiv(f, G):
    """
    Reduce a multivariate polynomial by the a working groebner basis.

    :param f  : Multivariate polynomial 
    :param G  : Working groebner basis containing multiple multivariate polynomials
    :return qP: List of quotient polynomials
    :return r : Remainder
    """ 
    qP = [P(0) for _ in range(len(G))]  # Quotient polynomials
    r = P(0)  # Remainder polynomial
    p = f  # Current polynomial
    t = len(G)

    # Filter out zero polynomials in G
    non_zero_indices = [i for i in range(t) if G[i] != 0]
    
    while p != 0:
        division_occurred = False
        p_lt = p.lt()  # Leading term of p

        for i in non_zero_indices:
            g_lt = G[i].lt()  # Leading term of G[i]

            # Check divisibility of leading terms
            if p_lt % g_lt == 0:
                quotient_term = p_lt / g_lt
                qP[i] += P(quotient_term)
                p -= P(quotient_term) * G[i]
                division_occurred = True
                break  # Exit the inner loop after successful division

        if not division_occurred:
            # Add the leading term of p to the remainder
            r += p_lt
            p -= p_lt

    return qP, r


def multiVarDiv(f, G):
    """
    Reduce a multivariate polynomial by the a working groebner basis.

    :param  f: Multivariate polynomial 
    :param  G: Working groebner basis containing multiple multivariate polynomials
    :return r: Remainder
    """ 
    r = P(0)  # Remainder polynomial
    p = f  # Current polynomial
    t = len(G)

    # Filter out zero polynomials in G
    non_zero_indices = [i for i in range(t) if G[i] != 0]

    while p != 0:
        division_occurred = False
        p_lt = p.lt()  # Leading term of p

        for i in non_zero_indices:
            g_lt = G[i].lt()  # Leading term of G[i]

            # Check divisibility of leading terms
            if p_lt % g_lt == 0:
                quotient_term = p_lt / g_lt
                p -= P(quotient_term) * G[i]
                division_occurred = True
                break  # Exit the inner loop after successful division

        if not division_occurred:
            # Add the leading term of p to the remainder
            r += p_lt
            p -= p_lt

    return 0,r


# Reduce the polynomial system, before solving using the f4 algorithm in case of common leading terms. 
G = Gro
G2 = []
for j in range(len(G)):
    ele = G[j]
    ele, r = multiVarDiv(ele,G[:j] + G[j+1:])
    if r != 0:
        G2.append(r/r.lc())
G = G2

def sPol(f,g):
    """
    Compute the s-polynomial of two polynomials f and g

    :param f: Polynomial
    :param g: Polynomial
    :return : S-polynomial
    """ 
    u = lcm(f.lm(),g.lm()) 
    return P((u*f)/(f.lt())) - P((u*g)/(g.lt()))

def s_half(f,g):
    """
    Compute the s-polynomial of two polynomials f and g

    :param f: Polynomial
    :param g: Polynomial
    :return : S-half
    """ 
    u = lcm(f.lm(),g.lm()) 
    if f == 0 or g == 0:
        print(f,g,u)
    return P((u*f)/(f.lt()))
   

def comb(xss):
    """
    Combine a list of lists into one list

    :param xss: List of lists
    :return   : Combined lists
    """ 
    return [x for xs in xss for x in xs]


def leadingTerms(F):
    """
    Find the leading terms of a set of polynomials

    :param  F  : Polynomial set
    :return lts: List containing the leading terms of all the polynomials in the set F
    """ 
    lts = {}
    for i in F:
        ele = i.lt()
        if ele not in lts:
            lts[ele] = 1
    return lts

def leadingMonomials(F):
    """
    Find the leading monomials of a set of polynomials

    :param  F  : Polynomial set
    :return lts: List containing the leading monomials of all the polynomials in the set F
    """ 
    lms = []
    for i in F:
        ele = i.lm()
        if ele not in lms:
            lms.append(ele)
    return lms



def getMonomials(f):
    """
    Find all the monomials of a polynomial 

    :param f: Polynomial
    :return : List containing the monomials of the polynomial f
    """ 
    out = f.monomials()
    if out != []:
        if out[-1].degree() == 0:
            out.pop()
        return out
    return 0


def getTerms(f):
    """
    Find all the terms of a polynomial 

    :param f: Polynomial
    :return : List containing the terms of the polynomial f
    """ 
    terms = []
    poly = f
    while poly != 0:
        lead = poly.lt()
        terms.append(P(lead))
        poly = poly - lead
    
    return terms


def maCols(sHalf):
    """
    Given a list of polynomials, find all terms ordered by a term order 

    :param sHalf: List of polynomials
    :return     : Ordered list of all terms in sHalf according to the specified term order in the polynomial ring. 
                  This list is used for constructing the sub-macualay matrix.
    """ 
    cols = []
    checkPol = P(0)
    for i in range(len(sHalf)):
        terms = getMonomials(sHalf[i])
        for j in terms:
            if j.degree() > 0:
                cols.append(j.lm())
                
    cols = list(dict.fromkeys(cols))  
       
    for i in range(len(cols)):
        checkPol = checkPol + cols[i]
    
    return getMonomials(checkPol)


def maCols2(sHalf):
    """
    Given a list of polynomials, find all terms ordered by a term order 

    :param sHalf: List of polynomials
    :return     : Ordered list of all terms in sHalf according to the specified term order in the polynomial ring. 
                  This list is used for constructing the sub-macualay matrix.
    """ 
    cols = []
    checkPol = PP(0)
    for i in range(len(sHalf)):
        checkPol = checkPol + PP(sHalf[i])
        
    return getMonomials(checkPol)


def allS(sHalf,B):
    """
    Compute all s-halves of a working groebner basis, given a list of critical pairs.

    :param  sHalf: Working groebner basis
    :param  B    : List of critical pairs according to some selectiong strategy
    :return ss   : List containing all s-halves of the critical pairs
    """ 
    ss = []
    
    for i in B: 
        if sHalf[i[0]] != 0 and sHalf[i[1]] != 0:
            ss.append(s_half(sHalf[i[0]],sHalf[i[1]]))
            ss.append(s_half(sHalf[i[1]],sHalf[i[0]]))
    return ss




def macualay(F):
    """
    Construct a sub-macualay matrix from a set of polynomials F. 

    :param  F     : Polynomial set
    :return matr  : Sub-macualay matrix
    :return colInd: Indices of each term
    """ 
    cols = maCols(F)
    colInd = {}
    
    for i in range(len(cols)):
        colInd[cols[i]] = i
    
    
    matr = Matrix(R,len(F),len(colInd)+1)    
    for i in range(len(F)):
        trms = getTerms(F[i])
        for j in trms:
            if j.lm() != 1:
                matr[i,colInd[j.lm()]] = j.lc() 
            else: 
                matr[i,len(colInd)] = j
                
    return matr, colInd





def symPre(sHalf,G):
    """
    Symbolic preprocessing, 
    
    :param sHalf: List of s-halves
    :param G    : Working groebner basis G
    :return     : Prepocessed list of s-halves
    """ 
    
    proc = list((i.lm()) for i in sHalf)                   # List containing all leading monomials of the list of s-halves
    check = maCols(sHalf)                                  # List of all monomials ordered from sHalf
    if check == 0:
        return 0
    proc_set = set(proc)                                   # Remove duplicates
    com = [item for item in check if item not in proc_set] # Find all elements not processed yet
    com = list(com)
        
    while True:
        bef = time.time()
        if com == []:
            break
        else:
            comm = com.pop()                               # Maximum element from com
            proc.append(comm)
            
        af = time.time()
        tt = af - bef
        
        bef = time.time()
        for i in G:                                        # Check if there is an element in G that divide
            if i != 0:
                lead = i.lm()
                if comm % lead == 0:    
                    ele = P(comm/lead)*i 
                    sHalf.append(ele)
                    break
                    
        af = time.time()
        tt = af - bef
    return sHalf
        
               
def f4(F):
    """
    f4 algorithm

    :param  F: Polynomial set 
    :return G: Reduced groebner basis
    """ 
    G = F
    B = []
        
    for i in range(len(F)):
        for j in range(i+1,len(F)):
            B.append([i,j,(lcm(F[i].lm(),F[j].lm())).degree()])
            
                    
    stepDeg = []
    count = 0
    while B != []:   
        selected = []
        smallest = B[0][2]
        
        for i in range(1,len(B)):                
            if B[i][2] < smallest:
                smallest = B[i][2]
        
        for i in range(len(B) - 1, -1, -1):  # Iterate in reverse
            if B[i][2] == smallest:
                selected.append(B[i])
                B.pop(i)  
        

        L = allS(G,selected)
        lmM = leadingTerms(L)
        M = symPre(L,G)
        if M == 0:
            return G
         
        M,colInd = macualay(M)
    
        invCols = {v: k for k, v in colInd.items()}
                
        stepDeg.append((list(colInd.keys()))[0].degree())
            
        N = M.rref()
        gLen = len(G)
        
        for i in range(N.nrows()):
            newPol = False
            for j in range(len(N[i])-1):
                if N[i][j] != 0:
                    value = lmM.get(invCols[j], None)
                    if value == None:
                        newPol = True
                        break
                    break
            
            
            if newPol == True:
                row = N[i]
                poly = P(0)
                for j in range(len(row)-1):
                    if row[j] != 0:
                        poly = poly + invCols[j]*row[j]
                
                
                poly = P(poly + row[len(row)-1])     
                _, poly = multiVarDiv(poly,G) 
                                
                if poly != 0:
                    G.append(poly) 
       
    
        for j in range(len(G)):
            if G[j] != 0:
                ele = G[j]
                ele, r = multiVarDiv(ele, list(without_index(G, j)))
                G[j] = r
            if j < gLen:
                if G[j] != 0:
                    for ii in range(gLen,len(G)):
                        degr = (lcm(G[j].lm(),G[ii].lm())).degree()
                        B.append([j,ii,degr])  
        
        count = count + 1

    G2 = []
    for j in range(len(G)):
        ele = G[j]
        ele, r = multiVarDiv(ele,G[:j] + G[j+1:])
        if r != 0:
            G2.append(r/r.lc())
    G = G2
        
    print(stepDeg)
    print(G)
    return G



kk = ((f4(Gro)))


# Sage built in for Groebner Basis below
#Gro = Ideal(Gro)
#B = Gro.groebner_basis()
#print(B)




