import time

############################################################################
#                                                                          #
#                           Buildings.sage                                 #
#                                                                          #
#                       (c) Matthew Dawes 2022                             #
#                                                                          #
#                       matthew.r.dawes@bath.edu                           #
#                                                                          #
############################################################################

############################################################################
#                                                                          #
#         Class of the principal congruence subgroup Gamma(N)              #
#                                                                          #
############################################################################

class Ell:
    '''
    class of the principal congruence subgroup Gamma(N) in SL(2, Z)
    '''
    def __init__(self, N):
        self.N=N
        self.cosets=self.make_gamma_N()
    
    def in_gamma_N(self, x):
        '''
        INPUT: an element x in SL(2, Z)
        
        OUTPUT: True if x belongs to Gamma(N); False otherwise
        '''
        if x[0,1] % self.N != 0 or x[1,0] % self.N != 0:
            return False
        if x[0,0] % self.N != 1 or x[1,1] % self.N != 1:
            return False
        return True

    def in_gens(self, x, gens):
        '''
        INPUT: 
              - an element x in SL(2, Z)
              - a list gens of elements of SL(2, Z)
        OUTPUT: 
              - True if x.Gamma(N) in gens.Gamma(n); 
              - False otherwise.
        '''
        z=matrix(ZZ, [[x[1,1],-x[0,1]],[-x[1,0], x[0,0]]])
        for y in gens:
            if self.in_gamma_N(z*y)==True:
                return True
        return False

    def expected_size(self):
        '''
        OUTPUT: the expected size of SL(2, Z) / Gamma(N) 
        '''
        x=1
        for p in prime_divisors(self.N):
            x*=(1-1/p^2)
        return x*self.N^3

    def make_gamma_N(self):
        '''
        OUTPUT: a list of representatives for the left cosets of Gamma(N) \\ SL(2, Z).
        '''
        start=time.time()
        S=matrix([[0, -1], [1,0]])
        T=matrix([[1,1],[0,1]])
        aye=matrix([[1,0],[0,1]])
        gens=[aye]
        old_count=-1

        while (old_count!=len(gens)):
            old_count=len(gens)
            for x in gens:
                z=x*S
                if self.in_gens(z, gens)==False:
                    gens.append(z)
                z=x*T
                if self.in_gens(z, gens)==False:
                    gens.append(z)
        end=time.time()
        print("we expected index = ", self.expected_size(), ". We got ", len(gens), " in ", end-start, "seconds.\n")
        return gens

############################################################################
#                                                                          #
#                   Class of the group O^(2U+A2)                           #
#                                                                          #
############################################################################

class BigGp:
    '''
    class of the group O^+(2U + A_2)
    '''
    def __init__(self):
        self.gm=matrix(ZZ, [[0,1,0,0,0,0],
                           [1,0,0,0,0,0],
                           [0,0,0,1,0,0],
                           [0,0,1,0,0,0],
                           [0,0,0,0,-2,-1],
                           [0,0,0,0,-1,-2]])

        self.gens_stab_e=self.make_gens_stab_e()
        self.gens_stab_E=self.make_gens_stab_E()
        self.gens=self.make_gens()
        
    def ip(self, x, y):
        '''
        INPUT: vectors x, y in 2U + A_2
        OUTPUT: the inner product of x and y in 2U+A_2
        '''
        return (x.transpose()*self.gm*y)[0,0]

    
    def make_eichler(self, e,a):
        '''
        INPUT:
              - isotropic e in 2U+A_2
              - a vector a in e^{perp}/e
        OUTPUT: 
              - matrix of the Eichler transvection t(e,a).
        '''
        m=zero_matrix(6)
        for i in range(0,6):
            ei=zero_matrix(6,1)
            vee=zero_matrix(6,1)
            ei[i,0]=1
            vee[i,0]=1
            vee-=self.ip(a,ei)*e
            vee+=self.ip(e,ei)*a
            vee-=(1/2)*self.ip(a,a)*self.ip(e,ei)*e
            
            for j in range(0,6):
                m[j,i]=vee[j,0]
        return m

    def make_reflection(self, a):
        '''
        INPUT: a reflective vector a in 2U+A2
        OUTPUT: the matrix of the reflection in a
        ''' 
        m=zero_matrix(6)
        for i in range(0,6):
            ei=zero_matrix(6,1)
            ei[i,0]=1
            ei-=(2*self.ip(a,ei)/self.ip(a, a))*a
       
            for j in range(0,6):
                m[j,i]=ei[j,0]
        return m

    def SL_emb_left(self, A):
        M=matrix(6)
        M[4,4]=1
        M[5,5]=1
        M[0,0]=A[1,1]
        M[2,0]=A[0,1]
        M[1,1]=A[0,0]
        M[3,1]=-A[1,0]
        M[0,2]=A[1,0]
        M[2,2]=A[0,0]
        M[1,3]=-A[0,1]
        M[3,3]=A[1,1]
        return M
    
    def SL_emb_right(self, B):
        M=matrix(6)
        M[4,4]=1
        M[5,5]=1
        M[0,0]=B[1,1]
        M[3,0]=-B[0,1]
        M[1,1]=B[0,0]
        M[2,1]=B[1,0]
        M[1,2]=B[0,1]
        M[2,2]=B[1,1]
        M[0,3]=-B[1,0]
        M[3,3]=B[0,0]
        return M
    
    def make_gens(self):
        '''
        OUTPUT: a list of generators for O(2U + A_2)
        '''
        e1=matrix([[1,0,0,0,0,0]]).transpose()
        f1=matrix([[0,1,0,0,0,0]]).transpose()
        e2=matrix([[0,0,1,0,0,0]]).transpose()
        f2=matrix([[0,0,0,1,0,0]]).transpose()
        w1=matrix([[0,0,0,0,1,0]]).transpose()
        w2=matrix([[0,0,0,0,0,1]]).transpose()
        v1=matrix([[0,0,1,-1,0,0]]).transpose()
        v2=-w1
        v3=w2
        v4=matrix([[0,0,0,1,1,-1]]).transpose()
        jay=matrix(6,6)     # diagram automorphism
        idd=matrix.identity(6)
        jay[0,0]=jay[1,1]=jay[2,2]=jay[3,3]=1
        jay[5,4]=jay[4,5]=-1

        gens=[idd,
              self.make_eichler(e1,e2),
              self.make_eichler(e1,f2),
              self.make_eichler(e1,w1),
              self.make_eichler(e1,w2),
              self.make_eichler(f1,e2),
              self.make_eichler(f1,f2),
              self.make_eichler(f1,w1),
              self.make_eichler(f1,w2),

              self.make_eichler(e1,-e2),
              self.make_eichler(e1,-f2),
              self.make_eichler(e1,-w1),
              self.make_eichler(e1,-w2),
              self.make_eichler(f1,-e2),
              self.make_eichler(f1,-f2),
              self.make_eichler(f1,-w1),
              self.make_eichler(f1,-w2),
              
              self.make_reflection(v1),
              self.make_reflection(v2),
              self.make_reflection(v3),
              self.make_reflection(v4),

              jay

        ]
        return gens

    def make_gens_stab_E(self):
        '''
         OUTPUT: return a list of generators for Stab_{BigGp)}(E) 
        '''
        # we're going to construct as semi-direct product of the Jacobi group and O(L_0)
                
        # For Jacobi-like generators
        e1=matrix([[1,0,0,0,0,0]]).transpose()
        f1=matrix([[0,1,0,0,0,0]]).transpose()
        e2=matrix([[0,0,1,0,0,0]]).transpose()
        f2=matrix([[0,0,0,1,0,0]]).transpose()
        w1=matrix([[0,0,0,0,1,0]]).transpose()
        w2=matrix([[0,0,0,0,0,1]]).transpose()
                
        # finite elements
        ref1=self.make_reflection(w1)
        ref2=self.make_reflection(w2)
        jay=matrix(6,6)                    # diagram automorphism
        jay[0,0]=jay[1,1]=jay[2,2]=jay[3,3]=1
        jay[5,4]=jay[4,5]=-1

        idd=matrix.identity(6)
        
        gens = [idd,

                self.make_eichler(e1, f2),
                self.make_eichler(f1, e2),
                self.make_eichler(e1, e2),
                self.make_eichler(e1, w1),
                self.make_eichler(e2, w2),
                
                ref1, ref2, jay]
        return gens

    def make_gens_stab_e(self):
        '''
        OUTPUT: return a list of generators for Stab_{O^+(L')}(e) 
        '''
        e1=matrix([[1,0,0,0,0,0]]).transpose()
        e2=matrix([[0,0,1,0,0,0]]).transpose()
        f2=matrix([[0,0,0,1,0,0]]).transpose()
        w1=matrix([[0,0,0,0,1,0]]).transpose()
        w2=matrix([[0,0,0,0,0,1]]).transpose()
        v1=matrix([[0,0,1,-1,0,0]]).transpose()
        v2=-w1
        v3=w2
        v4=matrix([[0,0,0,1,1,-1]]).transpose()
        idd=matrix.identity(6)
        d_aut=matrix.identity(6)   # diagram automorphism
        d_aut[4,4]=d_aut[5,5]=0
        d_aut[4,5]=d_aut[5,4]=-1

        jay=-matrix.identity(6)
        jay[4,4]=jay[5,5]=1
        
        gens=[idd,
              jay,
              self.make_eichler(e1,e2),
              self.make_eichler(e1,f2),
              self.make_eichler(e1,w1),
              self.make_eichler(e1,w2),
              
              self.make_eichler(e1,-e2),
              self.make_eichler(e1,-f2),
              self.make_eichler(e1,-w1),
              self.make_eichler(e1,-w2),
              
              self.make_reflection(v1),
              self.make_reflection(v2),
              self.make_reflection(v3),
              self.make_reflection(v4),
              d_aut

        ]
        
        return gens
############################################################################
#                                                                          #
#                   Classes of subgroups of O^(2U+A2)                      #
#                                                                          #
############################################################################

    
class SubGp_A2t:
    '''
     class of the subgroup \\tilde{O}^+(2U + A_2) in  O^+(2U+A_2)
    '''
    def __init__(self):
        self.bgp=BigGp()
        self.ellg=Ell(6)
        self.gamma_N=self.ellg.cosets
        
    # return true if m is an integer matrix, false otherwise
    def is_integer_matrix(self, m):    
        for i in range(0, m.dimensions()[0]):
            for j in range(0, m.dimensions()[1]):
                if m[i,j].is_integer()==False:
                    return False
        return True

    # return true if a matrix x in O^+(2U+A_2) belongs to the subgroup
    # false otherwise.
    def in_gp(self, x):
        u3=matrix(QQ, [[0],[0],[0],[0],[-2/3], [1/3]])
        vee3=x*u3-u3
        return self.is_integer_matrix(vee3)
    
    def in_right_cosets(self, x, cosets):
        '''
        OUTPUT: return True if SubGp.x is in SubGp.cosets; False otherwise
        '''
        for y in cosets:
            if self.in_gp(x*y.inverse())==True:
                return True
        return False

    def in_left_cosets(self, x, cosets):
        '''
        OUTPUT: return True if x.SubGp is in cosets.SubGp; False otherwise
        '''
        for y in cosets:
            if self.in_gp(x.inverse()*y)==True:
                return True
        return False
    
    def make_right_cosets(self):
        '''
        return a list of representative for the cosets SubGp \\ BigGp 
        '''
        print("Making cosets ")
        start=time.time()
        gen_set=self.bgp.gens
        cosets=[matrix.identity(6)]
        old_count=-1

        while (old_count!=len(cosets)):
            old_count=len(cosets)
            for x in cosets:
                for y in gen_set:
                    z=x*y
                    if self.in_right_cosets(z, cosets)==False:
                        cosets.append(z)
                        print(len(cosets), "cosets")
        end=time.time()
        print("")
        print("We got ", len(cosets), "cosets in ", end-start, "seconds .\n")
        return cosets

    def make_left_cosets(self):
        '''
        return a list of representative for the cosets BigGp/SubGp 
        '''
        print("Making cosets ")
        start=time.time()
        gen_set=self.bgp.gens
        cosets=[matrix.identity(6)]
        old_count=-1

        while (old_count!=len(cosets)):
            old_count=len(cosets)
            for x in cosets:
                for y in gen_set:
                    z=x*y
                    if self.in_left_cosets(z, cosets)==False:
                        cosets.append(z)
                        print(len(cosets), "cosets")
        end=time.time()
        print("")
        print("We got ", len(cosets), "cosets in ", end-start, "seconds .\n")
        return cosets

    def make_right_cosets_stab_e_cong(self, g):
        '''
        OUTPUT: a list of representatives for the cosets Stab_{SubGp}(ge) \\ Stab_{BigGp}(ge) 
     
        '''
        gen_set0=copy(self.bgp.gens_stab_e)
        gen_set=[]
        ginv=g.inverse()
        for x in gen_set0:     # conjugated generating set
            gen_set.append(g*x*ginv)
        
        cosets=[matrix.identity(6)]
        old_count=-1

        while (old_count!=len(cosets)):
            old_count=len(cosets)
            for x in cosets:
                for y in gen_set:
                    z=x*y
                    if self.in_right_cosets(z, cosets)==False:
                        cosets.append(z)
        return cosets

    def make_left_cosets_stab_e_cong(self, g):
        '''
        OUTPUT: a list of representatives for the cosets Stab_{SubGp}(ge) \\ Stab_{BigGp}(ge) 
     
        '''
        gen_set0=copy(self.bgp.gens_stab_e)
        gen_set=[]
        ginv=g.inverse()
        for x in gen_set0:     # conjugated generating set
            gen_set.append(g*x*ginv)
        
        cosets=[matrix.identity(6)]
        old_count=-1

        while (old_count!=len(cosets)):
            old_count=len(cosets)
            for x in cosets:
                for y in gen_set:
                    z=x*y
                    if self.in_left_cosets(z, cosets)==False:
                        cosets.append(z)
        return cosets
    
    def make_right_cosets_stab_E_cong(self, g):
        '''
        OUTPUT: return a list of representatives for the cosets Stab_{SubGp}(gE) \\ Stab_{BigGp}(gE) 
        '''
        start=time.time()
        gen_set0=copy(self.bgp.gens_stab_E)
        gen_set=[]
        ginv=g.inverse()
        for x in gen_set0:     # conjugated generating set
            gen_set.append(g*x*ginv)
        
        cosets=[matrix.identity(6)]
        old_count=-1

        while (old_count!=len(cosets)):  # form all words in generating set until 
            old_count=len(cosets)        # set if cosets stop growing
            for x in cosets:
                for y in gen_set:
                    z=x*y     
                    if self.in_right_cosets(z, cosets)==False:
                        cosets.append(z)
        end=time.time()
        return cosets

    def make_left_cosets_stab_E_cong(self, g):
        '''
        OUTPUT: return a list of representatives for the cosets  Stab_{BigGp}(gE) / Stab_{SubGp}(gE)
        '''
        start=time.time()
        gen_set0=copy(self.bgp.gens_stab_E)
        gen_set=[]
        ginv=g.inverse()
        for x in gen_set0:     # conjugated generating set
            gen_set.append(g*x*ginv)
        
        cosets=[matrix.identity(6)]
        old_count=-1

        while (old_count!=len(cosets)):  # form all words in generating set until 
            old_count=len(cosets)        # set if cosets stop growing
            for x in cosets:
                for y in gen_set:
                    z=x*y     
                    if self.in_left_cosets(z, cosets)==False:
                        cosets.append(z)
        end=time.time()
        return cosets

        
    def identify_bc_e(self):
        ''' 
        OUTPUT: return a list [g_i] such that [g_i e] are inequivalent lines.
        '''
        start=time.time()                  # start the timer
        ell=copy(self.left_cosets)         # cosets BigGp / SubGp
        i=0                                # an index for i
        while i<len(ell):                  # find all g_j such that g_i e ~ g_j e
            if ell[i]!=0:
                # make cosets of conjugated stabiliser
                stabe=self.make_right_cosets_stab_e_cong(ell[i])  
                j=i+1                      # WLOG test only j>i
                while j<len(ell):
                    if ell[j]!=0:
                        for x in stabe:
                            # ell[i] ~ ell[j], so remove
                            if (self.in_gp(x*ell[i]*ell[j].inverse())==True):
                                ell[j]=0
                                print("identify line ", j+1, "of", len(ell))
                                break
                    j+=1         # no equivalent elements found: try next
            i+=1                 # increment i
        end=time.time()     
        out=[]
        for x in ell:
            if x!=0:
                out.append(x)
        print("length of old list = ", len(ell), "length of new list = ", len(out), "completed in ", end-start, "seconds")
        return out


    def identify_bc_E(self):
        '''
        OUTPUT: a list [g_i] such that [g_iE] is a list of inequivalent 
        isotropic planes in L=2U+A2 under O^+(L).
        '''
        start=time.time()
        ell=copy(self.left_cosets)
        j=0
        while(j<len(ell)):
            if ell[j]!=0:                                  # not marked for deletion
                stabE=self.make_right_cosets_stab_E_cong(ell[j]) # make cosets for conjugate stabiliser
                i=j+1                                      # WLOG consider only j>i
                while(i<len(ell)):
                    for x in stabE:
                        if ell[i]!=0:   # not marked for deletion
                            if (self.in_gp(x*ell[j]*ell[i].inverse())==True): # ell[i] ~ ell[j], so remove
                                ell[i]=0
                                print("identify plane", i+1, "of", len(ell))
                                break
                    i+=1         # no equivalent elements found: try next
            j+=1                 # increment i
        end=time.time()          # stop the clock
        out=[]
        for x in ell:
            if x!=0:
                out.append(x)
        print("length of old list = ", len(ell), "length of new list = ", len(out), "completed in ", end-start, "seconds")

        return out

    def red_L1(self, x):
        '''
        INPUT: a vector x in L=2U+A2
        OUTPUT: the matrix of an element in O^+(L) such that gx = ^t(0,0,*,*,*,*).
        '''

        """
        We construct g from an element an of O^(2U).
        Elements of  SL(2,Z) x SL(2, Z) defube elements of O^+(2U).
        The correct (X, Y) in SL(2, Z) x SL(2, Z) comes from the
        Smith normal form.
        """
        if not (x[0,0]==0 and x[1,0]==0):     # otherwise, we are already reduced.
            M=matrix( [[x[2,0], -x[1,0]], [x[0,0], x[3,0]]])
            A=M.smith_form()[1]
            B=(M.smith_form()[2]).inverse()
            gx=self.bgp.SL_emb_left(A)*self.bgp.SL_emb_right(B)
        else:
            gx=matrix.identity(6)

        return gx

    def coprime_comb(self, x):
        ''' 
        INPUT: a list [y_i] of coprime integers
        
        OUTPUT: a list [x_i] of coprime integers such that \\sum x_i*y_i  = 1
        '''
        # this is essentially the Euclidean algorithm/B\'ezout's Lemma
        
        if len(x)==1 and x[0]>=0:
            return [1]
        if len(x)==1 and x[0]<0:
            return [-1]
        
        if len(x)==2:
            z=xgcd(x[0], x[1])
            return [z[1], z[2]]
        
        if len(x)>2:
            y0=self.coprime_comb(x[0:len(x)-1])
            gcd0=gcd(x[0:len(x)-1])
            z=xgcd(gcd0, x[len(x)-1])
            y=[]
            for i in y0:
                y.append(i*z[1])
            y.append(z[2])
            return y    

    
    # We apply the Eichler criterion, following 'Abelianisation of orthogonal groups and the fundamental group of modular varieties',
    # Gritsenko-Hulek-Sankaran, Journal of Algebra, 2009.
    	
    def eichler_equiv(self, x, y):
        '''
        INPUT: two primitive isotropic vectors x and y in 2U+A2
        OUTPUT:  an element g in O^+(2U+A2) such that gx=y.
        '''
        # zero first two coordinates
        gx=self.red_L1(x)
        gy=self.red_L1(y)
      
        # assume x and y belong to L1
        x=gx*x
        y=gy*y
        
        # calculate u and v
        xd=(x.transpose()*self.bgp.gm)
        xd=xd[0]
        u=matrix([self.coprime_comb(xd)]).transpose()
    
        yd=y.transpose()*self.bgp.gm
        yd=yd[0]
        v=matrix([self.coprime_comb(yd)]).transpose()
    
        # [e, f] is canonical basis for U
        e=matrix([[1,0,0,0,0,0]]).transpose()
        f=matrix([[0,1,0,0,0,0]]).transpose()

        t=gy.inverse()*self.bgp.make_eichler(e, -v)*self.bgp.make_eichler(f, x-y)*self.bgp.make_eichler(e, u)*gx
        
        return t

    def iso_classes_in_E(self, e1, e2):
        '''
        INPUT: generators [e1, e2] for an isotropic plane E
        OUPUT:  SL(2, Z)/Gamma(N) representatives for primitive isotropic
        vectors in E.
        '''   
        l=[]
        for x in self.gamma_N:
            l.append(x[1,1]*e1 + x[0,1]*e2)  # this comes from SL_emb_left 
        return l

    def line_plane_incid(self, e1, e2, gk, u):
        '''
        INPUT: 
               - generators [e1, e2] for an isotropic plane E
               - An element gk of SubGp
               - A list of cosets u for Stab_{SubGp}(gk e) \\ Stab_{BigGp}(gk e) 
        OUPUT: 
               - True of E contains a vector equivalent to gke under SubGp;
               - False otherwise.
        '''
        
        e=matrix([[1,0,0,0,0,0]]).transpose()   # the element e
        gke=gk*e
        y=self.iso_classes_in_E(e1, e2)         # representatives for 
                                                # Gamma(N) orbits of primitive 
                                                # vectors in E.  

        # test if gke equivalent to element of E under SubGp.
        for m in range(0, len(u)):
            for yi in y:
                t=self.eichler_equiv(yi, gke)
                if self.in_gp(u[m]*t)==True:
                    return True
                t=self.eichler_equiv(-yi, gke)
                if self.in_gp(u[m]*t)==True:
                    return True
            print("         tested ", m+1, "um of ", len(u))
        return False

    def incid_rels(self):
        '''
        OUTPUT: a list of pairs (i, j) such that plane i is incident to line j.
                i and j refer to indices in self.plane and self.line, respectively.
        '''
        start=time.time()
        out=[]
        line_cos=[]
        # canonical basis for E
        eee1=matrix([[1,0,0,0,0,0]]).transpose()
        eee2=matrix([[0,0,1,0,0,0]]).transpose()

        # make list of cosets for Stab_{SubGp}(lines[j] e) \ Stab_{BigGp}(lines[j]e)
        for j in range(0, len(self.lines)): 
            line_cos.append(self.make_right_cosets_stab_e_cong(self.lines[j]))
            print("made cosets", j+1, "of", len(self.lines))
            print("   coset consists of", len(line_cos[j]), "representatives")

        # test incidence of planes with lines
        for i in range(0, len(self.planes)):
            print("starting plane ", i+1, "...")
            p_start=time.time()
            # [e1, e2] is a basis for planes[i]E
            e1=self.planes[i]*eee1
            e2=self.planes[i]*eee2
            for j in range(0, len(self.lines)):
                # test incidence with each line
                if self.line_plane_incid(e1, e2, self.lines[j], line_cos[j])==True:
                    out.append((i,j))
                    print("   we added", (i,j))
                print("   tested line ", j+1, "of ", len(self.lines))
            p_end=time.time()
            print("tested plane ", i+1, " of ", len(self.planes), "in ", p_end-p_start, "seconds")
        end=time.time()
        print(out)
        print("\n")
        print("completed in ", end-start, "seconds")
        return out

    def building(self):
        ''' OUTPUT: calculate orbits of isotropic lines and planes and output associated incidence relations.
        '''
        print("making cosets")
       # self.right_cosets=self.make_right_cosets()
        self.left_cosets=self.make_left_cosets()

        print("Identifying lines")
        self.lines=self.identify_bc_e()

        print("Identifying planes")
        self.planes=self.identify_bc_E()

        print("Calculating incidence relations")
        self.incid=self.incid_rels()

        return [self.lines, self.planes, self.incid]
    
class SubGp_GK(SubGp_A2t):
    '''
    class of \\tilde{O}^+(2U+<-6>+<-2>)
    '''
    def __init__(self):
        self.bgp=BigGp()
        self.ellg=Ell(6)
        self.theta=matrix.identity(6)    # embed 2U+<-6>+<-2> in 2U+A2
        self.theta[4,4]=-2
        self.theta[5,4]=1
        self.theta_inv=self.theta.inverse()
        self.gamma_N=self.ellg.cosets
                
    def in_gp(self, x):
        '''
        INPUT: an element x in BigGp
        OUTPUT: True if x belongs to SubGp; False otherwise.
        '''
        ud=matrix(QQ, [[0,0,0,0,0,1/2]]).transpose()  # dual of <-2>
        wd=matrix(QQ, [[0,0,0,0,1/6,0]]).transpose()  # dual of <-6>
        z=self.theta_inv*x*self.theta
        if self.is_integer_matrix(z)==True: # then x acts on 2U+<-6>+<-2>
            u=z*ud
            w=z*wd
            if self.is_integer_matrix(u-ud)==True and self.is_integer_matrix(w-wd)==True:
                return True                 # then x belongs to stable subgroup
        return False

    def in_right_cosets(self, x, cosets):
        '''
        OUTPUT: return True if SubGp.x is in SubGp.cosets; False otherwise
        '''
        for y in cosets:
            if self.in_gp(x*y.inverse())==True:
                return True
        return False

    def in_left_cosets(self, x, cosets):
        '''
        OUTPUT: return True if x.SubGp is in cosets.SubGp; False otherwise
        '''
        for y in cosets:
            if self.in_gp(x.inverse()*y)==True:
                return True
        return False

    
    def same_right_coset(self, x, y):
        '''
        INPUT: elements x, y of BigGp
        OUTPUT: True if x and y define the same right coset of SubGp; False otherwise.
        '''
        return self.in_gp(x*y.inverse())

    def same_left_coset(self, x, y):
        '''
        INPUT: elements x, y of BigGp
        OUTPUT: True if x and y define the same left coset of SubGp; False otherwise.
        '''
        return self.in_gp(x.inverse()*y)

    
class SubGp_UU2A2t(SubGp_A2t):    
    '''
    class of \\tilde{O}^+(U+U(2)+A_2)
    '''
    def __init__(self):
        self.bgp=BigGp()
        self.ellg=Ell(6)
        self.gamma_N=self.ellg.cosets
        self.theta=matrix.identity(6)    # embed U+U(2)+A_2 in 2U+A2
        self.theta[3,3]=2
        self.theta_inv=self.theta.inverse()
        
    def in_gp(self, x):
        '''
        INPUT: an element x in BigGp
        OUTPUT: True if x belongs to SubGp; False otherwise.
        '''
        ud1=matrix(QQ, [[0,0,1/2,0,0,0]]).transpose()  # duals of U(2)
        ud2=matrix(QQ, [[0,0,0,1/2,0,0]]).transpose()
        wd=matrix(QQ, [[0,0,0,0,2/3,-1/3]]).transpose()  # dual of A2

        z=self.theta_inv*x*self.theta

        if self.is_integer_matrix(z)==True: # then x acts on U+U(2)+A2
            u1=z*ud1
            u2=z*ud2
            w=z*wd
            if self.is_integer_matrix(u1-ud1)==True and self.is_integer_matrix(u2-ud2)==True and self.is_integer_matrix(w-wd)==True:
                return True                 # then x belongs to stable subgroup
        return False
        
    def in_right_cosets(self, x, cosets):
        '''
        OUTPUT: return True if SubGp.x is in SubGp.cosets; False otherwise
        '''
        xinv=x.inverse()
        for y in cosets:
            if self.in_gp(y*xinv)==True:
                return True
        return False

    def in_left_cosets(self, x, cosets):
        '''
        OUTPUT: return True if x.SubGp is in cosets.SubGp; False otherwise
        '''
        xinv=x.inverse()
        for y in cosets:
            if self.in_gp(xinv*y)==True:
                return True
        return False

    
    def same_right_coset(self, x, y):
        return self.in_gp(x*y.inverse())

    def same_left_coset(self, x, y):
        return self.in_gp(x.inverse()*y)


class SubGp_UUmA2t(SubGp_UU2A2t):    
    '''
    Class of \\tilde{O}^+(U+U(m)+A2). N referes to Gamma(N) used to test incidence relations.
    '''
    def __init__(self, m, N):
        # check input is valid.
        if not m in NN:
            raise Exception("m is not a natural number.")
        if m==0:
            raise Exception("m cannot be zero.")
        if not N in NN:
            raise Exception("N is not a natural number.")
        if N==0:
            raise Exception("N cannot be zero.")
        # setup data
        self.m=m
        self.bgp=BigGp()
        self.ellg=Ell(N)
        self.gamma_N=self.ellg.cosets
        self.theta=matrix.identity(6)    # embed U+U(m)+A_2 in 2U+A2
        self.theta[3,3]=m
        self.theta_inv=self.theta.inverse()
        
    def in_gp(self, x):
        '''
        INPUT: an element x in BigGp
        OUTPUT: True if x belongs to SubGp; False otherwise.
        '''
        ud1=matrix(QQ, [[0,0,1/self.m,0,0,0]]).transpose()  # duals of U(m)
        ud2=matrix(QQ, [[0,0,0,1/self.m,0,0]]).transpose()
        wd=matrix(QQ, [[0,0,0,0,2/3,-1/3]]).transpose()  # dual of A2

        z=self.theta_inv*x*self.theta

        if self.is_integer_matrix(z)==True: # then x acts on U+U(m)+A2
            u1=z*ud1
            u2=z*ud2
            w=z*wd
            if self.is_integer_matrix(u1-ud1)==True and self.is_integer_matrix(u2-ud2)==True and self.is_integer_matrix(w-wd)==True:
                return True                 # then x belongs to stable subgroup
        return False
    

class SubGp_U2U2A2t(SubGp_UU2A2t):
    '''
    class of \\tilde{O}^+(U(2)+U(2)+A_2)
    '''
    def __init__(self):
        self.bgp=BigGp()
        self.ellg=Ell(6)
        self.gamma_N=self.ellg.cosets
        self.theta=matrix.identity(6)    # embed 2U(2)+A_2 in 2U+A2
        self.theta[1,1]=2
        self.theta[3,3]=2
        self.theta_inv=self.theta.inverse()
  
        def in_gp(self, x):
            '''
            INPUT: an element x in BigGp
            OUTPUT: True if x belongs to SubGp; False otherwise.
            '''
            ud0=matrix(QQ, [[1/2,0,0,0,0,0]]).transpose()  # duals of U(2)
            ud1=matrix(QQ, [[0,1/2,0,0,0,0]]).transpose() 
            ud2=matrix(QQ, [[0,0,1/2,0,0,0]]).transpose()
            ud3=matrix(QQ, [[0,0,0,1/2,0,0]]).transpose()
        
            wd=matrix(QQ, [[0,0,0,0,2/3,-1/3]]).transpose()  # dual of A2
            
            z=self.theta_inv*x*self.theta
            
            if self.is_integer_matrix(z)==True: # then x acts on 2U(2)+A2
                u0=z*ud0
                u1=z*ud1
                u2=z*ud2
                u3=z*ud3
                w=z*wd
                if self.is_integer_matrix(u0-ud0)==True and self.is_integer_matrix(u1-ud1)==True and self.is_integer_matrix(u2-ud2)==True and self.is_integer_matrix(u3-ud3)==True and self.is_integer_matrix(w-wd)==True:
                    return True                 # then x belongs to stable subgroup
            return False
        
