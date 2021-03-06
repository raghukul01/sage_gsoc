##Input:A number field K, a bound B>=1, and a theta in (0,1] where B and theta are in Q.
##Output:
def algorithm4(K,B,theta):
    
    ##This is the ring of integers of the number field K
    O_K=K.ring_of_integers()
    
    #This computes the group of units of the number field K
    unitGroup=K.unit_group()
    
    ##This compute the fundamental units of the number field K
    fundamentalUnits=unitGroup.fundamental_units()
    
    ##This compute the number of fundamental units.
    r=len(fundamentalUnits)
    
    ##if(r==0):
        ##Write what to do in this case
        ##Apparantly this case is easy
        
    ##
    ##
    ##This is the beginning of step 1
    ##
    ##
    
    
    ##This is the definition of t in step (1)
    t=theta/(3*B)
    
    ##This is the definition of \delta_1 in step (1)
    delta1=t/(6*r+12)
    
    ##Computes a complete set of ideal class representatives {a_1,...,a_h}
    ##Uses a previously defined function to do the computation
    classRepresentatives=completeSetOfIdealClassRepresentatives(K)
    
    ##This is the definition of h in step (1)
    ##This is the number of ideal class representatives
    h=len(classRepresentatives)
    
    ##Creates an empty list to store the \delta_1-approximations of \log(N(a_n))
    approx_log_norm_class_rep=[]
    
    ##Creates an empty list to store the norm of each ideal (a_n)
    ##Will have norm_class_rep[n]=N(a_n)
    norm_class_rep=[]
    
    ##Will use this for loop to fill in approx_log_norm_class_rep and norm_class_rep
    for n in range(h):
        
        ##Computes the norm of (a_n)
        ##Is the norm exact??
        norm=classRepresentatives[n].norm()
        
        ##Adds norm to norm_class_rep
        norm_class_rep.append(norm)
        
        ##Computes log(N(a_n))
        log_norm=log(norm,hold=True)
        
        ##Computes a \delta_1-approximation of log(N(a_n))
        approx_log_norm=deltaApproximation(log_norm,delta1)
        
        ##Add approx_log_norm to approx_log_norm_class_rep
        approx_log_norm_class_rep.append(approx_log_norm)
    
    ##norm_class_rep now has the property that norm_class_rep[n]=N(a_n)
    
    ##approx_log_norm_class_rep[n] is \delta_1-approximation of \log(N(a_n))
    
    ##
    ##
    ##This is the beginning of step 2
    ##
    ##
    
    
    ##Create an empty list to construct the set \mathcal{N} described in step (2)
    normMultiples=[]
    
    ##Use this for loop to build normMultiples
    for n in range(h):
        
        ##Recalls N(a_n)
        norm=norm_class_rep[n]
        
        ##Use this for loop to add m*norm to normMultiples for every m \leq B
        ##range(1,B+1,1)=1,2,...,B
        for m in range(1,B+1,1):
            
            ##Add m*norm to normMultiples
            normMultiples.append(m*norm)
            
    ##normMultiples is now mathcal{N} as described in step (2)
    
    ##Computes a dictionary whos key values (domain) are normMuliples.
    ##Given a key value v, mathcalP[v] is a collection of generators g
    ##representing a nonzero principal ideal of O_K whos norm is v.
    mathcalP=bdd_norm_pr_ideal_gens(K,normMultiples)

    ##Create an empty list to store \delta_1-approximations of each generator g.
    ##Will use this to build a dicitonary later
    approx_lambda_gens_dictionary_builder=[]
    
    ##Use the following for loop to build approx_lambda_gens_dictionary
    for norm in normMultiples:
        
        ##Recall the collection of generators who generate ideals of size norm.
        generators_of_size_norm=mathcalP[norm]
        
        ##Find the number of generators who generate ideals of size norm.
        m=len(generators_of_size_norm)
        
        ##Use the following for loop to build approx_lambda_gens_dictionary
        ##for generators who have size norm
        for k in range(m):
            
            ##Find the k'th generator who has size is norm.
            gen=generators_of_size_norm[k]
            
            ##Compute a delta_1 approximation of Lambda(gen)
            approx_lambda_g=vectorDeltaApproximation(Lambda(gen,K),delta1)
            
            ##Include (gen,approx_lambda_g) in the dictionary approx_lambda_gens_dictionary
            approx_lambda_gens_dictionary_builder.append((gen,approx_lambda_g))
    
    
    approx_lambda_gens_dictionary=dict(approx_lambda_gens_dictionary_builder)
    
    ##
    ##
    ##This is the beginning of step 3
    ##
    ##
    
    
    ##An empty list where we would like boundedGenerators[n] to be the generators g in mathcalP
    ##where (g)\subset a_n whos norms are at norm B*N(a_n)
    boundedGenerators=[]
    
    ##An empty list where we would like s[n] to the the number of things in boundedGenerators[n]
    s=[]
    
    ##Use the for loop to build boundedGenerators and s.
    for l in range(h):
        
        ##Recall the ideal a_l
        ideal = classRepresentatives[l]
        
        ##Create an empty list to build boundedGenerators[l]
        sublist=[]
        
        ##Use the for loop to build sublist.
        for norm in normMultiples:
            
            ##If norm \leq B*N(a_l), then everything in mathcalP[norm] will have size
            ##less than B*N(a_l)
            if norm <= B*norm_class_rep[l]:
                
                ##Add everything in mathcalP[norm] to sublist
                for g in mathcalP[norm]:
                    sublist.append(g)
        
        ##Find the size of sublist
        sublist_length=len(sublist)
        
        ##Add sublist_length to s
        s.append(sublist_length)
        
        ##Add sublist to boundedGenerators
        boundedGenerators.append(sublist)
    
    
    ##Input: alpha!=0 and beta!=0 in the number field K with llambda>0
    ##Output: A llambda approximation of h_K(alpha/beta)
    ##Information in lemma 4.1
    def relativeLogHeightQuotient(alpha,beta,llambda):
        dellta=llambda/(r+2)
        nTilde=deltaApproximation(log(O_K.ideal(alpha,beta).norm(),hold=True),dellta)
        s=vectorDeltaApproximation(Lambda(alpha,K),dellta)
        t=vectorDeltaApproximation(Lambda(beta,K),dellta)
        hTilde=-nTilde
        for i in range(r+1):
            hTilde=hTilde+max(s[i],t[i])
        return hTilde
    
    ##
    ##
    ##This is the beginning of step 4
    ##
    ##
    
    
    ##Define an empty list.  This list will have the property that relevant_pairs[n]=R_n as described in step (4)(b)
    relevant_pairs=[]
    
    ##Use the following for loop to build relevant_pairs
    for l in range(h):
        
        ##Make an empty list to build relevant_pairs[l]
        relevant_pairs_l=[]
        
        ##Use the following for loop to build relevant_pairs_l
        ##Everytime there is 0 \leq i < j \leq s[l]-1 with (g_li,g_lj)=a_l, 
        ##append (i,j) to relevant_pairs_l
        ##j=1,2,...,s[l]-1
        for j in range(1,s[l],1):
            ##i=0,...,j-1
            for i in range(j):
                ##Check to see if (g_li,g_lj)=a_l
                if O_K.ideal(boundedGenerators[l][i],boundedGenerators[l][j])==classRepresentatives[l]:
                    relevant_pairs_l.append([i,j])
        
        ##Add relevant_pairs_l to relevant_pairs
        relevant_pairs.append(relevant_pairs_l)
        
    
    ##
    ##Now we will build a container to store the data for step 12(b)
    ##
    
    ##Find what the largest value of i and j are
    imax=0;
    jmax=0;
    for n in range(h):
        for p in relevant_pairs[n]:
            imax=max(p[0],imax)
            jmax=max(p[1],jmax)
    
    ##Build a h by imax by jmax "cube" where all entries are zero.
    logHeightQuotientApproximation=[[[0]*(jmax+1) for i in range(imax+1)] for j in range(h)]
    
    ##
    ##This is the end of building the container to store the data for step 12(b)
    ##Now we can easily store the data
    ##If we make a dictionary where the key values are triples of numbers, then the previous step
    ##where we built a container is uncessessary.
    ##
    
    ##Use the for loop to store data from step 12(b) into logHeightQuotientApproximation with the
    ##property that logHeightQuotientApproximation[n][i][j]=r_nij where r_nij is described in the paper
    ##in step 12(b)
    for n in range(h):

        for p in relevant_pairs[n]:
            i=p[0]
            j=p[1]
            gni=boundedGenerators[n][i]
            gnj=boundedGenerators[n][j]
            
            ##Computes what r_nij can be and stores it
            logHeightQuotientApproximation[n][i][j]=relativeLogHeightQuotient(gni,gnj,t/6)

    
    ##
    ##
    ##This is the beginning of step 5
    ##
    ##
    
    
    ##Computes b as descibed in step (5)
    b=rationalIn(t/12+log(B,hold=True),t/4+log(B,hold=True))
    
    ##Here we will initialize maximum to be one of the values of r_nij.
    
    ##Initialized maximum
    ##At the end, we want this to be the max value of logHeightQuotientApproximation over all relevant_pairs
    maximum=0;
    
    ##Define maximumInitialized to be False.  When we redefine maximum, we will set this to True
    maximumInitialized=False;
    
    ##Use the while loop to look for something to set maximum to.
    ##The while loop will end one we have set maximum to a new value.
    for n in range(h):
            
        ##If relevant_pairs[l] isn't empty, do the following things
        if len(relevant_pairs[n])!=0:
                
            ##Set p to be the first pair in relevant_pairs[l]
            p=relevant_pairs[n][0]
                
            i=p[0]
            j=p[1]
                
            ##Redefine maximum
            maximum=logHeightQuotientApproximation[n][i][j]
                
            ##Say that we have found something to set maximum to.
            ##This will end the while loop.
            maximumInitialized=True
                
            ##ends the for loop
            break
    
    ##Now we want to find the maximum value of logHeightQuotientApproximation over all relevant_pairs
    if maximumInitialized==True:
        ##We will use the for loop to make maximum as large as possible.
        for l in range(h):
            for p in relevant_pairs[l]:
                i=p[0]
                j=p[1]

                ##Update the maximum value.
                maximum=max(maximum,logHeightQuotientApproximation[l][i][j])
    ##maximumInitialized==False if and only if R[n] is empty for all n
    else:
        maximum=0
    
    ##Now maximum is the largest value of logHeightQuotientApproximation over all relevant_pairs.
    
    ##Set dTilde to be the value defined in the paper in step (5)
    dTilde=b+t/6+maximum
    
    ##
    ##
    ##This is the beginning of step 6
    ##
    ##
    
    
    mat=S(K)
    mat_norm=mat.norm(Infinity)
    mat_inverse=mat.inverse()
    mat_inverse_norm=mat_inverse.norm(Infinity)
    
    ##Define upper_bound as m as described in the paper in step (6)
    ##We don't use the letter m because we may want to use it as a variable later.
    ##If S(K).inverse() is an approximation of (S(K))^{-1}, maybe this value of m will cause problems?
    upper_bound=r^2*max(mat_norm,mat_inverse_norm)
    upper_bound=ceil(upper_bound)+1
    
    ##
    ##
    ##This is the beginning of step 7
    ##
    ##
    
    
    ##Define lamdaTilde as described in step (7)
    lambdaTilde=(t/12)/(dTilde*r*(1+upper_bound))
    
    ##Define deltaTilde as described in step (7)
    deltaTilde=min(lambdaTilde/(r^2*(upper_bound^2+upper_bound*lambdaTilde)),1/(r^2))
    
    ##Define M as described in step (7)
    M=dTilde*(upper_bound+lambdaTilde*sqrt(r))
    M=ceil(M)
    
    ##Define delta2 as described in step (7)
    if M==0:
        delta2 = deltaTilde
    else:
        delta2=min(deltaTilde,(t/6)/(r*(r+1)*M))
    
    ##
    ##
    ##This is the beginning of step 8
    ##
    ##
    
    
    ##Make an empty list to assist with building the matrix descibed in step (8)
    ##This will have the property that v[i]=v_i as described in step (8)
    v=[]
    ##Use the for loop to build v
    for i in range(r):
        ##LambdaPrimed is Lambda with the last coordinate deleted
        v.append(vectorDeltaApproximation(Lambda(fundamentalUnits[i],K),delta2))
    
    matrix_builder=[]
    for i in range(r):
        matrix_builder.append(removeLastEntryOfList(v[i]))
        
    
    ##This is the matrix as descibed in step (8)
    STilde=transpose(matrix(matrix_builder))
    
    ##Compute the inverse
    STildeInverse=STilde.inverse()
    
    ##
    ##
    ##This is the beginning of step 9
    ##
    ##
    
    
    ##This computes all integers in the polytope STildeInverse([-dTilde,dTilde]^r)
    U=integer_points_in_polytope(STildeInverse,dTilde)
    
    ##
    ##
    ##This is the beginning of step 10
    ##
    ##
    
    
    ##This is the set L in the paper
    LL=[0]
    
    ##This is the set U_0 in the paper
    U0=[]
    
    ##This is the set U_0' in the paper
    U0Primed=[]
    
    ##This is the set L_0 in the paper
    L0=[]
    
    ##This is the set L_0' in the paper
    L0Primed=[]
    
    ##
    ##
    ##This is the beginning of step 11
    ##
    ##
    
    
    ##Build a list so that we can define a dictionary with key values u \in U
    ##which store the data from (11)(a)
    LambdaTildeU=[]
    for u in U:
        list=[]
        list.append(u)
        value=vector((r+1)*[0])
        for j in range(r):
            "j=",j
            value=value+u[j]*vector(v[j])
        list.append(value)
        LambdaTildeU.append(list)
    
    ##Computes a dictionary.  Has the property that if u \in U, then
    ##lambda_tilde_dictionary[u] is the sum described in step (11)(a)
    lambda_tilde_dictionary=dict(LambdaTildeU)

    
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
            ss.append(vectorDeltaApproximation(Lambda(fundamentalUnits[j],K),dellta))
        output=0
        for i in range(r):
            summation=0
            for j in range(r-1):
                summation=summation+u[j]*ss[j][i]
            output=output+max(summation,0)
        return output
    
    ##Create an empty dictionary to store the data generated from rr(u)
    log_height_units_dictionary={}
    
    ##Make a copy of U.  We do this because as we do a loop over U, we are going to want to remove things from U.
    copyU=copy(U)
    
    ##Use the for loop to build log_height_units_dictionary and to do steps (c)(d)(e)
    for u in copyU:
        
        ##Compute rr(u)
        u_log = sum([u[j]*vector(v[j]) for j in range(r)])
	height_u = sum([max(u_log[k], 0) for k in range(r + 1)])
        
        ##Include the pair (u,height_u) in the dictionary for future
        log_height_units_dictionary.update({u:height_u})
        
        ##Do step (11)(c)
        if height_u<b-(5/12)*t:
            U0.append(u)
            
        ##Do step (11)(d)
        if b-(5/12)*t <= height_u and height_u < b+(1/12)*t:
            U0Primed.append(u)
            
        ##Do step (11)(e)
        if height_u > (t/12)+dTilde:
            U.remove(u)
    
    ##This is r_u in the paper
    
    def packet_height_approx(P):
        n=P[0]
        pair=P[1]
        i=pair[0]
        j=pair[1]
        u=P[2]
        ##Compute log norm
        log_norm_approx=approx_log_norm_class_rep[n]
        ##COmpute lambda(gli) and lambda(glj)
        lambda_gni=approx_lambda_gens_dictionary[boundedGenerators[n][i]]
        lambda_gnj=approx_lambda_gens_dictionary[boundedGenerators[n][j]]
        ##compute lambdaTildeu
        lambdaTildeu=lambda_tilde_dictionary[u]
        lambda_u_gni=vector(lambda_gni)+lambdaTildeu
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
            product=product*fundamentalUnits[k]^u[k]
        numerator=product*boundedGenerators[l][i]
        return relativeLogHeightQuotient(numerator,boundedGenerators[l][j],t/3)
    
    ##
    ##
    ##This is the beginning of step 12
    ##
    ##
    
    
    ##Use this for loop to fill out packet_height_dictionary and to do steps (c) and (d)
    for l in range(h):
        for p in relevant_pairs[l]:
            i=p[0]
            j=p[1]
            
            ##Define w as defined in the paper on step (12)
            w=b+logHeightQuotientApproximation[l][i][j]+t/4
            for u in U:
                ##Check to see if r_u<w.
                if log_height_units_dictionary[u]<w:
                    
                    ##Step 12(a), Define a packet
                    P=[l,[i,j],u]
                    
                    ##Step 12(b), compute r_P as desribed in step 12(b) by using the function packetLogHeightApproximation(P)
                    r_P=packet_height_approx(P)
                    
                    ##Do step 12(c)
                    if r_P <= b-(7/12)*t:
                        L0.append(P)
                        
                    ##Do step 12(d)
                    if b-(7/12)*t<r_P and r_P<b+(1/4)*t:
                        L0Primed.append(P)
    
    
    ##
    ##
    ##This is the beginning of step 13
    ##
    ##
    
    
    ##Make an empty list to store distinct tuples in U0, U0Primed, or in some
    ##Packet P in L0 or L0Primed.
    relevant_tuples=[]
    
    ##Append everything in U0 and U0Primed.  This won't have copies because they are disjoint.
    relevant_tuples=U0+U0Primed
    
    ##Look for distinct tuples in L0
    for P in L0:
        u=P[2]
        if u not in relevant_tuples:
            relevant_tuples.append(u)
            
    ##Look for distinct tuples in L0Primed
    for P in L0Primed:
        u=P[2]
        if u not in relevant_tuples:
            relevant_tuples.append(u)
            
    
    ##Make a dictionary that maps (n1,...,nr) to e_1^n_1*...*e_r^n_r
    tuples_to_unit_dictionary={}
    
    ##Use the for loop to build the tuples_to_unit_dictionary
    for u in relevant_tuples:
        unit=1
        
        ##Use this for loop to build the unit
        for k in range(r):
            unit=unit*fundamentalUnits[k]^u[k]
        
        
        ##Append the pair (u,unit) to the dictionary
        tuples_to_unit_dictionary.update({u : unit})
    
    
    ##
    ##
    ##This is the beginning of step 14
    ##
    ##
    
    
    ##Compute the roots of unity of K
    roots=K.roots_of_unity()
    
    for u in U0:
        for root in roots:
            LL.append(root*tuples_to_unit_dictionary[u])

    
    LPrimed=[]
    
    for u in U0Primed:
        for root in roots:
            LPrimed.append(root*tuples_to_unit_dictionary[u])
            
    ##
    ##
    ##This is the beginning of step 14
    ##
    ##
    
    
    for P in L0:
        n=P[0]
        pair=P[1]
        i=pair[0]
        j=pair[1]
        u=P[2]
        c_P=tuples_to_unit_dictionary[u]*(boundedGenerators[n][i]/boundedGenerators[n][j])
        for root in roots:
            LL.append(root*c_P)
            LL.append(root/c_P)
    
    
    for P in L0Primed:
        n=P[0]
        pair=P[1]
        i=pair[0]
        j=pair[1]
        u=P[2]
        c_P=tuples_to_unit_dictionary[u]*(boundedGenerators[n][i]/boundedGenerators[n][j])
        for root in roots:
            LPrimed.append(root*c_P)
            LPrimed.append(root/c_P)
    
    
    
    return [LL,LPrimed]


    
    
    
    

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
        relevant_pairs = relevant_pairs[n]
        for pair in relevant_pairs:
            i = pair[0] ; j = pair[1]

            ##u_height_bound =


    for n in xrange(h):
        relevant_pairs = relevant_pair_lists[n]
        for pair in relevant_pairs:
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