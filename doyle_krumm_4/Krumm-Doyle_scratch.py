from sage.rings.number_field.bdd_height import bdd_norm_pr_ideal_gens
from sage.rings.number_field.bdd_height import integer_points_in_polytope


##How to compute h_K(x) if we are given lists of log`    (N(a_l)) and Lamba(g)



##End of functions to work on

##Input: Real numbers a and b such that x<y
##Output: Rational number q such that x<q<y
def rationalIn(x,y):
    z=y-x
    n=ceil(1/z)+1
    if ceil(n*y)==n*y:
        m=n*y-1
    else:
        m=floor(n*y)
    return m/n

##Input: A vector v=(v1,...,vn) and delta>0
##Output: A rational vector w=(w1,...,wn) such that |vi-wi|<delta for all i
def vectorDeltaApproximation(v,delta):
    n=len(v)
    w=[]
    for i in range(n):
        w.append(deltaApproximation(v[i],delta))
    return w

##Input: A real number x and a delta>0
##Output: A rational number q such that |x-q|<delta
def deltaApproximation(x,delta):
    return rationalIn(x-delta,x+delta)

## inputs: number field K, and element x of K
## output: (r+1)-tuple of absolute values of x under different embeddings of K into RR and CC
def Lambda(x,K):
    embed=K.embeddings(QQbar)
    n=len(embed)
    removed=[False]*n
    realEmbeddings=[]
    generator=K.gen()
    for i in range(n):
        if conjugate(embed[i](generator))==embed[i](generator): ##This means that embed[i] has codomain==RR
            realEmbeddings.append(embed[i])
            removed[i]=True
    complexEmbeddings=[]
    for i in range(n):
        if removed[i]==false:
            for j in range(i+1,n):
                if(embed[i](generator)==conjugate(embed[j](generator))):  ##This means embed[i] is a complex conjugate of embed[j]
                    complexEmbeddings.append(embed[j])
                    removed[i]=True
                    removed[j]=True
    output=[]
    for sigma in realEmbeddings:
        output.append(log(abs(sigma(x)),hold=True))
    for sigma in complexEmbeddings:
        output.append(2*log(abs(sigma(x)),hold=True))
    return output

##input: An array
##output: The array with the last entry removed
def removeLastEntryOfList(list):
    n=len(list)                        ##Define n to be the length of the list you inputted
    newList=[]                         ##Set newList to the the empty list
    if n>0:                            ##If n>0
        for i in range(n-1):                ##For every i in 0,...,n-1
            newList.append(list[i])              ##Append the i'th entry of list to the end of newList
        return newList                      ##return newList

##Displayed equation on page 2869 on line 11
def LambdaPrimed(x,K):
    return removeLastEntryOfList(Lambda(x,K))

##Description on page 2872 on line 7
##input: A number field K
##output: An rxr matrix with column vectors gammaPrimed(epsilonj) where epsilonj is the 
##jth fundamental unit generated in fundamentalUnits(K)
def S(K):
    matrixColumnList=[]
    fundamental_Units=UnitGroup(K).fundamental_units()
    r=len(fundamental_Units)
    for i in range(r):
        matrixColumnList.append(LambdaPrimed(fundamental_Units[i],K))
    M=matrix(matrixColumnList)
    M=M.transpose()
    return M

def SS(K,fundamental_units):
    matrixColumnList=[]
    r=len(fundamental_Units)
    for i in range(r):
        matrixColumnList.append(LambdaPrimed(fundamental_Units[i],K))
    M=matrix(matrixColumnList)
    M=M.transpose()
    return M
    

##Input: A number field K
##Output: A complete set of ideal class representatives of K
def completeSetOfIdealClassRepresentatives(K):
    
    ##Compute the class group of K
    classGroup=K.class_group()
    
    ##Define reps to be an empty list.  We want this to have a representative for each element in classGroup
    reps=[]
    
    ##For every element g of the class group of K
    for g in classGroup:
        ##Find a representative of g and add it to the list reps.
        reps.append(g.representative_prime())
    
    ##Return the collection of representatives
    return reps






##Input:A number field K, a bound B>=1, and a theta in (0,1] where B and theta are in Q.
##Output:
def algorithm4(K,B,theta):
    
    ##This is the ring of integers of the number field K
    O_K=K.ring_of_integers()
    print "O_K =",O_K
    
    #This computes the group of units of the number field K
    unitGroup=K.unit_group()
    
    ##This compute the fundamental units of the number field K
    fund_units = UnitGroup(K).fundamental_units()
    print "fund_units =",fund_units
    
    ##This compute the number of fundamental units.
    r=len(fund_units)
    print "There are ", r , " fundamental units in ", K
    
    ##if(r==0):
        ##Write what to do in this case
        ##Apparantly this case is easy
        
    ##
    ##
    ##This is the beginning of step 1
    ##
    ##
    
    print "Step (1)"
    
    ##This is the definition of t in step (1)
    t=theta/(3*B)
    print "t =", t
    
    ##This is the definition of \delta_1 in step (1)
    delta_1=t/(6*r+12)
    print "delta_1 =", delta_1
    
    ##Computes a complete set of ideal class representatives {a_1,...,a_h}
    ##Uses a previously defined function to do the computation
    class_group_reps=completeSetOfIdealClassRepresentatives(K)
    print "class_group_reps =",class_group_reps
    
    ##This is the definition of h in step (1)
    ##This is the number of ideal class representatives
    h=len(class_group_reps)
    print "There are ", h , " class representatives."
    
    ##Creates an empty list to store the \delta_1-approximations of \log(N(a_n))
    class_group_rep_norm_log_approx=[]
    
    ##Creates an empty list to store the norm of each ideal (a_n)
    ##Will have class_group_rep_norms[n]=N(a_n)
    class_group_rep_norms=[]
    
    ##Will use this for loop to fill in class_group_rep_norm_log_approx and class_group_rep_norms
    for n in range(h):
        print "n =", n
        
        ##Computes the norm of (a_n)
        ##Is the norm exact??
        norm=class_group_reps[n].norm()
        print "norm=",norm
        
        ##Adds norm to class_group_rep_norms
        class_group_rep_norms.append(norm)
        print "Adding ", norm , " to class_group_rep_norms"
        
        ##Computes log(N(a_n))
        log_norm=log(norm,hold=True)
        print "log_norm =", log_norm
        
        ##Computes a \delta_1-approximation of log(N(a_n))
        approx_log_norm=deltaApproximation(log_norm,delta_1)
        print "approx_log_norm=", approx_log_norm
        
        ##Add approx_log_norm to class_group_rep_norm_log_approx
        class_group_rep_norm_log_approx.append(approx_log_norm)
        print "Adding ", approx_log_norm , " to class_group_rep_norm_log_approx"
    
    ##class_group_rep_norms now has the property that class_group_rep_norms[n]=N(a_n)
    print "class_group_rep_norms=",class_group_rep_norms
    
    ##class_group_rep_norm_log_approx[n] is \delta_1-approximation of \log(N(a_n))
    print "class_group_rep_norm_log_approx =", class_group_rep_norm_log_approx
    
    ##
    ##
    ##This is the beginning of step 2
    ##
    ##
    
    print "Step (2)"
    
    ##Create an empty list to construct the set \mathcal{N} described in step (2)
    possible_norm_set=[]
    
    ##Use this for loop to build possible_norm_set
    for n in range(h):
        print "n =", n
        
        ##Recalls N(a_n)
        norm=class_group_rep_norms[n]
        
        ##Use this for loop to add m*norm to possible_norm_set for every m \leq B
        ##range(1,B+1,1)=1,2,...,B
        for m in range(1,B+1,1):
            print "m =",m
            
            ##Add m*norm to possible_norm_set
            possible_norm_set.append(m*norm)
            print "Adding ",(m*norm)," to normMultiplies"
            
    ##possible_norm_set is now mathcal{N} as described in step (2)
    print "possible_norm_set =", possible_norm_set
    
    ##Computes a dictionary whos key values (domain) are normMuliples.
    ##Given a key value v, bdd_ideals[v] is a collection of generators g
    ##representing a nonzero principal ideal of O_K whos norm is v.
    bdd_ideals=bdd_norm_pr_ideal_gens(K,possible_norm_set)
    print "bdd_ideals =", bdd_ideals

    ##Create an empty list to store \delta_1-approximations of each generator g.
    ##Will use this to build a dicitonary later
    lambda_gens_approx_builder=[]
    
    ##Use the following for loop to build lambda_gens_approx
    for norm in possible_norm_set:
        print "norm=",norm
        
        ##Recall the collection of generators who generate ideals of size norm.
        generators_of_size_norm=bdd_ideals[norm]
        
        ##Find the number of generators who generate ideals of size norm.
        m=len(generators_of_size_norm)
        print "m=",m
        
        ##Use the following for loop to build lambda_gens_approx
        ##for generators who have size norm
        for k in range(m):
            
            ##Find the k'th generator who has size is norm.
            gen=generators_of_size_norm[k]
            print "gen=",gen
            
            ##Compute a delta_1 approximation of Lambda(gen)
            approx_lambda_g=vectorDeltaApproximation(Lambda(gen,K),delta_1)
            print "approx_lambda_g=",approx_lambda_g
            
            ##Include (gen,approx_lambda_g) in the dictionary lambda_gens_approx
            lambda_gens_approx_builder.append((gen,approx_lambda_g))
            print "Include the pair (",gen,",",approx_lambda_g,") in lambda_gens_approx_builder"
    
    print "lambda_gens_approx_builder=",lambda_gens_approx_builder
    
    lambda_gens_approx=dict(lambda_gens_approx_builder)
    print "lambda_gens_approx=",lambda_gens_approx
    
    ##
    ##
    ##This is the beginning of step 3
    ##
    ##
    
    print "Step (3)"
    
    ##An empty list where we would like generator_lists[n] to be the generators g in bdd_ideals
    ##where (g)\subset a_n whos norms are at norm B*N(a_n)
    generator_lists=[]
    
    ##An empty list where we would like s[n] to the the number of things in generator_lists[n]
    s=[]
    
    ##Use the for loop to build generator_lists and s.
    for l in range(h):
        print "l =",l
        
        ##Recall the ideal a_l
        ideal = class_group_reps[l]
        print "ideal =",ideal
        
        ##Create an empty list to build generator_lists[l]
        sublist=[]
        
        ##Use the for loop to build sublist.
        for norm in possible_norm_set:
            print "norm =", norm
            
            ##If norm \leq B*N(a_l), then everything in bdd_ideals[norm] will have size
            ##less than B*N(a_l)
            if norm <= B*class_group_rep_norms[l]:
                
                ##Add everything in bdd_ideals[norm] to sublist
                for g in bdd_ideals[norm]:
                    sublist.append(g)
        
        ##Find the size of sublist
        sublist_length=len(sublist)
        print "sublist_length=",sublist_length
        
        ##Add sublist_length to s
        s.append(sublist_length)
        print "Adding ",sublist_length, "to s"
        
        ##Add sublist to generator_lists
        generator_lists.append(sublist)
        print "Adding ", sublist , " to generator_lists"
    
    print "s=", s
    print "generator_lists =", generator_lists
    
    ##Input: alpha!=0 and beta!=0 in the number field K with llambda>0
    ##Output: A llambda approximation of h_K(alpha/beta)
    ##Information in lemma 4.1
    def log_height_for_generators_approx(alpha,beta,llambda):
        dellta=llambda/(r+2)
        nTilde=deltaApproximation(log(O_K.ideal(alpha,beta).norm(),hold=True),dellta)
        s=vectorDeltaApproximation(Lambda(alpha,K),dellta)
        t=vectorDeltaApproximation(Lambda(beta,K),dellta)
        hTilde=-nTilde
        for i in range(r):
            hTilde=hTilde+max(s[i],t[i])
        return hTilde
    
    ##
    ##
    ##This is the beginning of step 4
    ##
    ##
    
    print "Step 4"
    
    ##Define an empty list.  This list will have the property that relevant_pair_lists[n]=R_n as described in step (4)(b)
    relevant_pair_lists=[]
    
    ##Use the following for loop to build relevant_pair_lists
    for l in range(h):
        print "l =",l
        
        ##Make an empty list to build relevant_pair_lists[l]
        relevant_pair_lists_l=[]
        
        ##Use the following for loop to build relevant_pair_lists_l
        ##Everytime there is 0 \leq i < j \leq s[l]-1 with (g_li,g_lj)=a_l, 
        ##append (i,j) to relevant_pair_lists_l
        ##j=1,2,...,s[l]-1
        for j in range(1,s[l],1):
            ##i=0,...,j-1
            for i in range(j):
                ##Check to see if (g_li,g_lj)=a_l
                if O_K.ideal(generator_lists[l][i],generator_lists[l][j])==class_group_reps[l]:
                    relevant_pair_lists_l.append([i,j])
        print "relevant_pair_lists_l =",relevant_pair_lists_l
        
        ##Add relevant_pair_lists_l to relevant_pair_lists
        relevant_pair_lists.append(relevant_pair_lists_l)
        print "Appending ",relevant_pair_lists_l, " to relevant_pair_lists"
        
    print "relevant_pair_lists=",relevant_pair_lists
    
    ##
    ##Now we will build a container to store the data for step 12(b)
    ##
    
    ##Find what the largest value of i and j are
    imax=0;
    jmax=0;
    for n in range(h):
        for p in relevant_pair_lists[n]:
            imax=max(p[0],imax)
            jmax=max(p[1],jmax)
    print "imax =",imax
    print "jmax =",jmax
    
    ##Build a h by imax by jmax "cube" where all entries are zero.
    gen_height_approx_dictionary=[[[0]*(jmax+1) for i in range(imax+1)] for j in range(h)]
    print "gen_height_approx_dictionary=",gen_height_approx_dictionary
    
    ##
    ##This is the end of building the container to store the data for step 12(b)
    ##Now we can easily store the data
    ##If we make a dictionary where the key values are triples of numbers, then the previous step
    ##where we built a container is uncessessary.
    ##
    
    ##Use the for loop to store data from step 12(b) into gen_height_approx_dictionary with the
    ##property that gen_height_approx_dictionary[n][i][j]=r_nij where r_nij is described in the paper
    ##in step 12(b)
    for n in range(h):
        print "n=",n

        for p in relevant_pair_lists[n]:
            i=p[0]
            j=p[1]
            gni=generator_lists[n][i]
            gnj=generator_lists[n][j]
            
            ##Computes what r_nij can be and stores it
            gen_height_approx_dictionary[n][i][j]=log_height_for_generators_approx(gni,gnj,t/6)

    print "gen_height_approx_dictionary=",gen_height_approx_dictionary
    
    ##
    ##
    ##This is the beginning of step 5
    ##
    ##
    
    print "Step 5"
    
    ##Computes b as descibed in step (5)
    b=rationalIn(t/12+log(B,hold=True),t/4+log(B,hold=True))
    print "b =",b
    
    ##Here we will initialize maximum to be one of the values of r_nij.
    
    ##Initialized maximum
    ##At the end, we want this to be the max value of gen_height_approx_dictionary over all relevant_pair_lists
    maximum=0;
    
    ##Define maximumInitialized to be False.  When we redefine maximum, we will set this to True
    maximumInitialized=False;
    
    ##Use the while loop to look for something to set maximum to.
    ##The while loop will end one we have set maximum to a new value.
    for n in range(h):
            
        ##If relevant_pair_lists[l] isn't empty, do the following things
        if len(relevant_pair_lists[n])!=0:
                
            ##Set p to be the first pair in relevant_pair_lists[l]
            p=relevant_pair_lists[n][0]
                
            i=p[0]
            j=p[1]
                
            ##Redefine maximum
            maximum=gen_height_approx_dictionary[n][i][j]
            print "Initial Maximum =",maximum
                
            ##Say that we have found something to set maximum to.
            ##This will end the while loop.
            maximumInitialized=True
                
            ##ends the for loop
            break
    
    ##Now we want to find the maximum value of gen_height_approx_dictionary over all relevant_pair_lists
    if maximumInitialized==True:
        ##We will use the for loop to make maximum as large as possible.
        for l in range(h):
            for p in relevant_pair_lists[l]:
                i=p[0]
                j=p[1]

                ##Update the maximum value.
                maximum=max(maximum,gen_height_approx_dictionary[l][i][j])
    ##maximumInitialized==False if and only if R[n] is empty for all n
    else:
        maximum=0
    
    ##Now maximum is the largest value of gen_height_approx_dictionary over all relevant_pair_lists.
    print "maximum=",maximum
    
    ##Set d_tilde to be the value defined in the paper in step (5)
    d_tilde=b+t/6+maximum
    print "d_tilde=",d_tilde
    
    ##
    ##
    ##This is the beginning of step 6
    ##
    ##
    
    print "Step 6"
    
    mat=S(K)
    mat_norm=mat.norm(Infinity)
    mat_inverse=mat.inverse()
    mat_inverse_norm=mat_inverse.norm(Infinity)
    
    ##Define upper_bound as m as described in the paper in step (6)
    ##We don't use the letter m because we may want to use it as a variable later.
    ##If S(K).inverse() is an approximation of (S(K))^{-1}, maybe this value of m will cause problems?
    upper_bound=r^2*max(mat_norm,mat_inverse_norm)
    print "m=",upper_bound
    upper_bound=ceil(upper_bound)+1
    print "m=",upper_bound
    
    ##
    ##
    ##This is the beginning of step 7
    ##
    ##
    
    print "Step 7"
    
    ##Define lamdaTilde as described in step (7)
    lambda_tilde=(t/12)/(d_tilde*r*(1+upper_bound))
    print "lambda_tilde=",lambda_tilde
    
    ##Define delta_tilde as described in step (7)
    delta_tilde=min(lambda_tilde/(r^2*(upper_bound^2+upper_bound*lambda_tilde)),1/(r^2))
    print "delta_tilde=",delta_tilde
    
    ##Define M as described in step (7)
    M=d_tilde*(upper_bound+lambda_tilde*sqrt(r))
    print "M=",M
    M=ceil(M)
    print "M=",M
    
    ##Define delta_2 as described in step (7)
    if M==0:
        delta_2 = delta_tilde
    else:
        delta_2=min(delta_tilde,(t/6)/(r*(r+1)*M))
    print "delta_2=",delta_2
    
    ##
    ##
    ##This is the beginning of step 8
    ##
    ##
    
    print "Step 8"
    
    ##Make an empty list to assist with building the matrix descibed in step (8)
    ##This will have the property that v[i]=v_i as described in step (8)
    v=[]
    ##Use the for loop to build v
    for i in range(r):
        ##LambdaPrimed is Lambda with the last coordinate deleted
        v.append(vectorDeltaApproximation(Lambda(fund_units[i],K),delta_2))
    print "v=",v
    
    matrix_builder=[]
    for i in range(r):
        matrix_builder.append(removeLastEntryOfList(v[i]))
        
    print "matrix_builder=",matrix_builder
    
    ##This is the matrix as descibed in step (8)
    STilde=transpose(matrix(matrix_builder))
    print "STilde=",STilde
    
    ##Compute the inverse
    STildeInverse=STilde.inverse()
    print "STildeInverse=",STildeInverse
    
    ##
    ##
    ##This is the beginning of step 9
    ##
    ##
    
    print "Step 9"
    
    ##This computes all integers in the polytope STildeInverse([-d_tilde,d_tilde]^r)
    U=integer_points_in_polytope(STildeInverse,d_tilde)
    print "U=",U
    
    ##
    ##
    ##This is the beginning of step 10
    ##
    ##
    
    print "Step 10"
    
    ##This is the set L in the paper
    LL=[0]
    
    ##This is the set U_0 in the paper
    U0=[]
    
    ##This is the set U_0' in the paper
    U0_tilde=[]
    
    ##This is the set L_0 in the paper
    L0=[]
    
    ##This is the set L_0' in the paper
    L0_tilde=[]
    
    ##
    ##
    ##This is the beginning of step 11
    ##
    ##
    
    print "Step 11"
    
    ##Build a list so that we can define a dictionary with key values u \in U
    ##which store the data from (11)(a)
    Lambda_tildeU=[]
    for u in U:
        print "u=",u
        list=[]
        list.append(u)
        value=vector((r+1)*[0])
        for j in range(r):
            "j=",j
            print "v[j]=",v[j]
            print "u[j]=",u[j]
            print "value=",value
            value=value+u[j]*vector(v[j])
        list.append(value)
        Lambda_tildeU.append(list)
    print "Lambda_tildeU=",Lambda_tildeU
    
    ##Computes a dictionary.  Has the property that if u \in U, then
    ##unit_log_dict[u] is the sum described in step (11)(a)
    unit_log_dict=dict(Lambda_tildeU)
    print "unit_log_dict=",unit_log_dict

    
    ##Input: An element u of U
    ##Output: A rational number r(u) such that |r(u)-e_1^u[1]*...*e_r^u[r]|<t/6
    ##This is using the algorithm suggested in Lemma 4.2
    def rr(u):
        llambda=t/6
        abs_u=[]
        for i in range(r):
            abs_u.append(abs(u[i]))
        MM=max(abs_u)+1
        dellta=llambda/(r*(r+1)*MM)
        ss=[]
        for j in range(r):
            ss.append(vectorDeltaApproximation(Lambda(fund_units[j],K),dellta))
        output=0
        for i in range(r):
            summation=0
            for j in range(r-1):
                summation=summation+u[j]*ss[j][i]
            output=output+max(summation,0)
        return output
    
    ##Create an empty dictionary to store the data generated from rr(u)
    unit_height_dict={}
    
    ##Make a copy of U.  We do this because as we do a loop over U, we are going to want to remove things from U.
    copyU=copy(U)
    
    ##Use the for loop to build unit_height_dict and to do steps (c)(d)(e)
    for u in copyU:
        
        ##Compute rr(u)
        height_u=rr(u)
        
        ##Include the pair (u,height_u) in the dictionary for future
        unit_height_dict.update({u:height_u})
        
        ##Do step (11)(c)
        if height_u<b-(5/12)*t:
            U0.append(u)
            
        ##Do step (11)(d)
        if b-(5/12)*t <= height_u and height_u < b+(1/12)*t:
            U0_tilde.append(u)
            
        ##Do step (11)(e)
        if height_u > (t/12)+d_tilde:
            U.remove(u)
    
    ##This is r_u in the paper
    print "unit_height_dict=",unit_height_dict
    print "U0=",U0
    print "U0_tilde=",U0_tilde
    print "U=",U
    
    def packet_height_approx(P):
        n=P[0]
        pair=P[1]
        i=pair[0]
        j=pair[1]
        u=P[2]
        ##Compute log norm
        log_norm_approx=class_group_rep_norm_log_approx[n]
        print "log_norm_approx=",log_norm_approx
        ##COmpute lambda(gli) and lambda(glj)
        lambda_gni=lambda_gens_approx[generator_lists[n][i]]
        print "lambda_gni=",lambda_gni
        lambda_gnj=lambda_gens_approx[generator_lists[n][j]]
        print "lambda_gnj=",lambda_gnj
        ##compute lambda_tildeu
        lambda_tildeu=unit_log_dict[u]
        print "lambda_tildeu=",lambda_tildeu
        lambda_u_gni=vector(lambda_gni)+lambda_tildeu
        print "lambda_u_gni=",lambda_u_gni
        arch_sum=0
        for k in xrange(r+1):
            arch_sum +=max(lambda_u_gni[k],lambda_gnj[k])
        return(arch_sum-log_norm)

    
    ##This is an attempt to a cheaty way to do step 12(b)
    ##Given a packet P, finds a (t/3)-approximation of h_K(c(P)).
    def packetLogHeightApproximation(P):
        l=P[0]
        pair=P[1]
        i=pair[0]
        j=pair[1]
        u=P[2]
        product=1
        for k in range(r):
            product=product*fund_units[k]^u[k]
        numerator=product*generator_lists[l][i]
        return log_height_for_generators_approx(numerator,generator_lists[l][j],t/3)
    
    ##
    ##
    ##This is the beginning of step 12
    ##
    ##
    
    print "Step 12"
    
    ##Use this for loop to fill out packet_height_dictionary and to do steps (c) and (d)
    for l in range(h):
        print "l=",l
        for p in relevant_pair_lists[l]:
            i=p[0]
            j=p[1]
            
            ##Define w as defined in the paper on step (12)
            w=b+gen_height_approx_dictionary[l][i][j]+t/4
            for u in U:
                ##Check to see if r_u<w.
                if unit_height_dict[u]<w:
                    
                    ##Step 12(a), Define a packet
                    P=[l,[i,j],u]
                    
                    ##Step 12(b), compute r_P as desribed in step 12(b) by using the function packetLogHeightApproximation(P)
                    r_P=packet_height_approx(P)
                    
                    ##Do step 12(c)
                    if r_P <= b-(7/12)*t:
                        L0.append(P)
                        
                    ##Do step 12(d)
                    if b-(7/12)*t<r_P and r_P<b+(1/4)*t:
                        L0_tilde.append(P)
    
    print "L0=",L0
    print "L0_tilde=",L0_tilde
    
    ##
    ##
    ##This is the beginning of step 13
    ##
    ##
    
    print "Step 13"
    
    ##Make an empty list to store distinct tuples in U0, U0_tilde, or in some
    ##Packet P in L0 or L0_tilde.
    relevant_tuples=[]
    
    ##Append everything in U0 and U0_tilde.  This won't have copies because they are disjoint.
    relevant_tuples=U0+U0_tilde
    
    ##Look for distinct tuples in L0
    print "Searching for relevant tuples in L0"
    for P in L0:
        u=P[2]
        if u not in relevant_tuples:
            print "Appending ",u," to relevant_tuples"
            relevant_tuples.append(u)
            
    ##Look for distinct tuples in L0_tilde
    print "Searching for relevant tuples in L0_tilde"
    for P in L0_tilde:
        u=P[2]
        if u not in relevant_tuples:
            print "Appending ",u," to relevant_tuples"
            relevant_tuples.append(u)
            
    print "relevant_tuples=",relevant_tuples
    
    ##Make a dictionary that maps (n1,...,nr) to e_1^n_1*...*e_r^n_r
    tuples_to_unit_dictionary={}
    
    ##Use the for loop to build the tuples_to_unit_dictionary
    for u in relevant_tuples:
        print "u=",u
        unit=1
        
        ##Use this for loop to build the unit
        for k in range(r):
            unit=unit*fund_units[k]^u[k]
        
        print "unit=",unit
        
        ##Append the pair (u,unit) to the dictionary
        tuples_to_unit_dictionary.update({u : unit})
    
    print "tuples_to_unit_dictionary=",tuples_to_unit_dictionary
    
    ##
    ##
    ##This is the beginning of step 14
    ##
    ##
    
    print "step (14)"
    
    ##Compute the roots of unity of K
    roots=K.roots_of_unity()
    print "roots=",roots
    
    for u in U0:
        for root in roots:
            LL.append(root*tuples_to_unit_dictionary[u])

    print "LL=",LL        
    
    LPrimed=[]
    
    for u in U0_tilde:
        for root in roots:
            LPrimed.append(root*tuples_to_unit_dictionary[u])
            
    ##
    ##
    ##This is the beginning of step 14
    ##
    ##
    
    print "Step (15)"
    
    for P in L0:
        n=P[0]
        pair=P[1]
        i=pair[0]
        j=pair[1]
        u=P[2]
        c_P=tuples_to_unit_dictionary[u] * (generator_lists[n][i]/generator_lists[n][j])
        for root in roots:
            LL.append(root*c_P)
            LL.append(root/c_P)
    
    print "LL=",LL
    
    for P in L0_tilde:
        n=P[0]
        pair=P[1]
        i=pair[0]
        j=pair[1]
        u=P[2]
        c_P=tuples_to_unit_dictionary[u] * (generator_lists[n][i]/generator_lists[n][j])
        for root in roots:
            LPrimed.append(root*c_P)
            LPrimed.append(root/c_P)
    
    print "LPrimed=",LPrimed
    
    
    return [LL,LPrimed]


    
    
    
    

    print "Step 12b"
    def _packet_height(n, pair, u):
        gen_logs = generator_logs[n]

        i = pair[0]
        j = pair[1]
        Log_gi = gen_logs[i]; Log_gj = gen_logs[j]
        Log_u_gi = Log_gi + unit_log_dictionary[u]
        arch_sum = 0
        for k in xrange(r + 1):
            arch_sum += max(Log_u_gi[k], Log_gj[k])
        return (arch_sum - class_group_rep_norm_logs[n])


    # This is where the function _packet_height is called... to build the list of packets L0.
    ## We need to make this Algorithm 4 friendly
    for n in xrange(h):
        relevant_pair_lists = relevant_pair_lists[n]
        for pair in relevant_pair_lists:
            i = pair[0] ; j = pair[1]

            ##u_height_bound =


    for n in xrange(h):
        relevant_pair_lists = relevant_pair_lists[n]
        for pair in relevant_pair_lists:
            i = pair[0] ; j = pair[1]
            gen_height = gen_height_dictionary[(n, i, j)]
            u_height_bound = logB + gen_height
            for k in xrange(U_length):
                u = U[k]
                u_height = unit_height_dictionary[u]
                if u_height <= u_height_bound:
                    candidate_height = _packet_height(n, pair, u)
                    if candidate_height <= logB:
                        L0.append([n, pair, u])
                        all_unit_tuples.add(u)
                else:
                    break