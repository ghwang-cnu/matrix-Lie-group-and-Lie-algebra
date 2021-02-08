needs "Multivariate/transcendentals.ml";;
needs "Multivariate/cross.ml";;
needs "Multivariate/realanalysis.ml";;
needs "Library/grouptheory.ml";;
needs "Multivariate/cvectors.ml";;

(* ------------------------------------------------------------------------- *)
(* Operation Definitions of Complex Matrix                            *)
(* ------------------------------------------------------------------------- *)
let COND_LMUL = prove
 (`!b x1 x2 y. (if b then x1 else x2) * y = (if b then x1 * y else x2 * y)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;
  
let COND_RMUL = prove
 (`!b x1 x2 y. y * (if b then x1 else x2) = (if b then y * x1 else y * x2)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;
  
let COND_LMUL_0 = prove
 (`!b x y. (if b then x else &0) * y = (if b then x * y else &0)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[REAL_MUL_LZERO]);;
  
let COND_RMUL_0 = prove
 (`!b x y. y * (if b then x else &0) = (if b then y * x else &0)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[REAL_MUL_RZERO]);;


overload_interface ("--",`(cmatrix_neg):complex^N^M->complex^N^M`);;
overload_interface ("+",`(cmatrix_add):complex^N^M->complex^N^M->complex^N^M`);;
overload_interface ("-",`(cmatrix_sub):complex^N^M->complex^N^M->complex^N^M`);;

overload_interface ("**",`(vector_cmatrix_mul):complex^M->complex^N^M->complex^N`);;
overload_interface ("**",`(cmatrix_mul):complex^N^M->complex^P^N->complex^P^M`);;
overload_interface ("**",`(cmatrix_vector_mul):complex^N^M->complex^N->complex^M`);;

make_overloadable "%%%" `:A->B->C`;;

overload_interface ("%%%",`(cmatrix_cmul):complex->complex^N^M->complex^N^M`);;

parse_as_infix("%%%",(21,"right"));;


let RE_MATRIX_DEF = new_definition
    `(Re_matrix:complex^N^M->real^N^M) M  = lambda i j. Re(M$i$j)`;;

let IM_MATRIX_DEF = new_definition
    `(Im_matrix:complex^N^M->real^N^M) M  = lambda i j. Im(M$i$j)`;;
    
let CX_MATRIX_DEF = new_definition
    `(Cx_matrix:real^N^M->complex^N^M) A  = lambda i j.  Cx(A$i$j)`;;
    
let ii_MATRIX_DEF = new_definition
    `(ii_matrix:real^N^M->complex^N^M) B  = lambda i j. complex(&0,B$i$j)`;;
    
let cmatrix_cmul = new_definition
  `!c:complex A:complex^N^M. c %%% A = lambda i j. c * A$i$j`;;
  
let cmatrix_neg = new_definition
    `!A:complex^N^M. --A = lambda i j. --(A$i$j)`;;

let cmatrix_add = new_definition
    `!A:complex^N^M B:complex^N^M. A + B = lambda i j. A$i$j + B$i$j`;;
    
let cmatrix_sub = new_definition
    `!A:complex^N^M B:complex^N^M. A - B = lambda i j. A$i$j - B$i$j`;;
    
let cmatrix_mul = new_definition
    `!A:complex^N^M B:complex^P^N. A ** B = lambda i j. vsum(1..dimindex(:N)) (\k. A$i$k * B$k$j)`;;
    
let cmatrix_vector_mul = new_definition
  `!A:complex^N^M x:complex^N.
        A ** x = lambda i. vsum(1..dimindex(:N)) (\j. A$i$j * x$j)`;;

let vector_cmatrix_mul = new_definition
  `!A:complex^N^M x:complex^M.
        x ** A = lambda j. vsum(1..dimindex(:M)) (\i. A$i$j * x$i)`;;
    
let cmat = new_definition
  `(cmat:num->complex^N^M) k = lambda i j. if i = j then Cx(&k) else Cx(&0)`;;
  
let ctransp = new_definition
  `(ctransp:complex^N^M->complex^M^N) A = lambda i j. A$j$i`;;
  
let cmatrix_cnj = new_definition
    `(cmatrix_cnj:complex^N^M->complex^N^M) A = lambda i j. cnj(A$i$j)`;;
    
let adjoint_matrix = new_definition
    `(adjoint_matrix:complex^N^M->complex^M^N) A = lambda i j. cnj(A$j$i)`;;

(* ------------------------------------------------------------------------- *)
(* Basic properties of complex matrix.                         *)
(* ------------------------------------------------------------------------- *)

let CMATRIX_ARITH_TAC =
  let SUM_DELTA1 = prove
    (`!s:A->bool a P. sum s (\x. if a = x then P x else &0) = if a IN s then P a else &0`,
    SIMP_TAC[GSYM SUM_RESTRICT_SET] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> {x | x IN s /\ a = x} = {}`;SET_RULE `(a IN s) ==> {x | x IN s /\ a = x} = {a}`;SUM_SING;SUM_CLAUSES]) in
  let FINITE_INDEX_INRANGE_2 = prove
 (`!i. ?k. 1 <= k /\ k <= dimindex(:N) /\
           (!x:A^N. x$i = x$k) /\ (!y:B^N. y$i = y$k)`,
  REWRITE_TAC[finite_index] THEN MESON_TAC[FINITE_INDEX_WORKS]) in
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT(GEN_TAC ORELSE CONJ_TAC ORELSE EQ_TAC) THEN
  TRY
  (GEN_REWRITE_TAC REDEPTH_CONV [CART_EQ] THEN
  SIMP_TAC[LAMBDA_BETA;matrix_mul;matrix_vector_mul;vector_matrix_mul] THEN
  SIMP_TAC[LAMBDA_BETA;
            RE_MATRIX_DEF; IM_MATRIX_DEF; CX_MATRIX_DEF; ii_MATRIX_DEF;
              cmatrix_cmul;cmatrix_cnj;ctransp;adjoint_matrix;
              cmatrix_vector_mul;vector_cmatrix_mul;
              cmatrix_neg; cmatrix_add; cmatrix_sub; cmatrix_mul;
              cmat] THEN
  SIMP_TAC[LAMBDA_BETA;matrix_cmul;vector_const;cvector_cnj;vsum;
            cvector_zero;cdot;vector_to_cvector;vector_map;
            cvector_neg;cvector_sub;cvector_add;cvector_mul;
            vector_map2;cvector_re;cvector_im;complex_vector;
             vector_neg;vector_sub;vector_add;vec;dot;
              matrix_neg; matrix_add; matrix_sub;mat;transp;
              RE_DEF; IM_DEF; CX_DEF;complex;cnj;ii;
              complex_add; complex_neg; complex_sub; complex_mul;
              complex_inv; complex_div;
              DIMINDEX_2;FORALL_2;SUM_2;
              VECTOR_2;ARITH;
              COND_COMPONENT;COND_ID;COND_RMUL;COND_LMUL;
              REAL_MUL_LZERO;REAL_MUL_RZERO;REAL_MUL_LID;
              REAL_MUL_RID;REAL_ADD_LID;REAL_ADD_RID;
              REAL_SUB_RZERO] THEN
  SIMP_TAC[FINITE_NUMSEG;GSYM SUM_ADD;GSYM SUM_SUB;GSYM SUM_LMUL;
        GSYM SUM_RMUL;GSYM SUM_NEG;SUM_DELTA;SUM_DELTA1;IN_NUMSEG] THEN
  TRY (GEN_TAC THEN DISCH_THEN(fun th1 -> REPEAT STRIP_TAC THEN GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM SUM_SWAP_NUMSEG])) THEN
  TRY ((MATCH_MP_TAC SUM_EQ_NUMSEG ORELSE
        MATCH_MP_TAC SUM_EQ_0_NUMSEG ORELSE
        GEN_REWRITE_TAC ONCE_DEPTH_CONV [CART_EQ]) THEN
        GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
        (MATCH_MP_TAC SUM_EQ_NUMSEG ORELSE
        MATCH_MP_TAC SUM_EQ_0_NUMSEG ORELSE
        GEN_REWRITE_TAC ONCE_DEPTH_CONV [CART_EQ])) THEN
  TRY (REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
       MATCH_MP_TAC(TAUT `(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)`) THEN DISCH_TAC)) THEN
  TRY (REWRITE_TAC[AND_FORALL_THM;
              TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`;
              TAUT `(a ==> b) \/ (a ==> c) <=> a ==> b \/ c`]) THEN
  TRY (SIMP_TAC[EQ_SYM_EQ]) THEN
  CONV_TAC REAL_FIELD) THEN
  TRY
  (SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ (!A:complex^N^M. A$i = A$k)`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ (!z:complex^N. z$j = z$l)`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
   SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ (!A:complex^N^M. A$j = A$k)  /\ (!z:complex^M. z$j = z$k)`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE_2]; ALL_TAC] THEN
    SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:N) /\ (!A:complex^M^N. A$i = A$l) /\ (!z:complex^N. z$i = z$l)`
    CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE_2]; ALL_TAC] THEN 
    ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;cmatrix_cmul;cmatrix_add;cmatrix_neg;cmatrix_sub;cmat;ctransp;COND_ID]);;
    
let CMATRIX_ARITH tm = prove(tm,CMATRIX_ARITH_TAC);;

let CMATRIX = prove
    (`!A:complex^N^M. Cx_matrix(Re_matrix(A)) + ii_matrix(Im_matrix(A)) = A`,
    CMATRIX_ARITH_TAC);;
    
let CMATRIX_EQ_ALT = prove
    (`!A:complex^N^M B. A = B <=> Re_matrix A = Re_matrix B /\ Im_matrix A = Im_matrix B`,
    CMATRIX_ARITH_TAC);;
    
let RE_MATRIX = prove
 (`!x y. (Re_matrix(Cx_matrix x + ii_matrix y) = x)`,
  CMATRIX_ARITH_TAC);;

let IM_MATRIX = prove
 (`!x y. Im_matrix(Cx_matrix x + ii_matrix y) = y`,
  CMATRIX_ARITH_TAC);;
  
let RE_MATRIX_CX_MATRIX = prove
    (`!x. (Re_matrix(Cx_matrix x) = x)`,
    CMATRIX_ARITH_TAC);;
    
let RE_MATRIX_II_MATRIX = prove
    (`!y. (Re_matrix(ii_matrix y) = mat 0)`,
    CMATRIX_ARITH_TAC);;
    
let IM_MATRIX_CX_MATRIX = prove
    (`!x. (Im_matrix(Cx_matrix x) = mat 0)`,
    CMATRIX_ARITH_TAC);;
    
let IM_MATRIX_II_MATRIX = prove
    (`!y. (Im_matrix(ii_matrix y) = y)`,
    CMATRIX_ARITH_TAC);;

let FORALL_CMATRIX = prove
 (`(!z. P z) <=> (!x y. P(Cx_matrix x + ii_matrix y))`,
  MESON_TAC[CMATRIX]);;

let EXISTS_CMATRIX = prove
 (`(?z. P z) <=> (?x y. P(Cx_matrix x + ii_matrix y))`,
  MESON_TAC[CMATRIX]);;
    
let CMATRIX_CMUL = prove
    (`!c:complex A:complex^N^M. c %%% A = Cx_matrix(Re c %% Re_matrix A - Im c %% Im_matrix A) + ii_matrix(Re c %% Im_matrix A + Im c %% Re_matrix A)`,
    CMATRIX_ARITH_TAC);;

let CMATRIX_NEG = prove
    (`!A:complex^N^M. --A = Cx_matrix(--(Re_matrix(A))) + ii_matrix(--(Im_matrix(A)))`,
    CMATRIX_ARITH_TAC);;

let CMATRIX_ADD = prove
    (`!A:complex^N^M B. A + B = Cx_matrix(Re_matrix A + Re_matrix B) + ii_matrix(Im_matrix A + Im_matrix B)`,
    CMATRIX_ARITH_TAC);;

let CMATRIX_SUB = prove
    (`!A:complex^N^M B. A - B = Cx_matrix(Re_matrix A - Re_matrix B) + ii_matrix(Im_matrix A - Im_matrix B)`,
    CMATRIX_ARITH_TAC);;

let CMATRIX_MUL = prove
    (`!A:complex^N^M B:complex^P^N. A ** B = Cx_matrix(Re_matrix A ** Re_matrix B - Im_matrix A ** Im_matrix B) + ii_matrix(Re_matrix A ** Im_matrix B + Im_matrix A ** Re_matrix B)`,
    CMATRIX_ARITH_TAC);;
    
let CMATRIX_VECTOR_MUL = prove
    (`!A:complex^N^M B:complex^N. A ** B = complex_vector((Re_matrix A ** cvector_re B - Im_matrix A ** cvector_im B),(Re_matrix A ** cvector_im B + Im_matrix A ** cvector_re B))`,
    CMATRIX_ARITH_TAC);;
    
let VECTOR_CMATRIX_MUL = prove
    (`!A:complex^N^M B:complex^M. B ** A = complex_vector((cvector_re B ** Re_matrix A - cvector_im B ** Im_matrix A),(cvector_re B ** Im_matrix A + cvector_im B ** Re_matrix A))`,
    CMATRIX_ARITH_TAC);;

let CMAT = prove
    (`!k. cmat k = Cx_matrix (mat k)`,
    CMATRIX_ARITH_TAC);;
    
let CTRANSP = prove
    (`!A:complex^N^M. ctransp A = Cx_matrix(transp(Re_matrix(A))) + ii_matrix(transp(Im_matrix(A)))`,
    CMATRIX_ARITH_TAC);;
    
let CMATRIX_CNJ = prove
    (`!A:complex^N^M. cmatrix_cnj A = Cx_matrix(Re_matrix(A)) - ii_matrix(Im_matrix(A))`,
    CMATRIX_ARITH_TAC);;
    
let ADJOINT_MATRIX = prove
    (`!A:complex^N^M. adjoint_matrix A = Cx_matrix(transp(Re_matrix(A))) - ii_matrix(transp(Im_matrix(A)))`,
    CMATRIX_ARITH_TAC);;
    
let ADJOINT_MATRIX_ALT = prove
    (`!A:complex^N^M. adjoint_matrix A = cmatrix_cnj(ctransp A)`,
    CMATRIX_ARITH_TAC);;
    
let ADJOINT_MATRIX_ALT2 = prove
    (`!A:complex^N^M. adjoint_matrix A = ctransp(cmatrix_cnj A)`,
    CMATRIX_ARITH_TAC);;
    
let CMATRIX_CMUL_COMPONENT = prove
    (`!c A:complex^N^M i j. (c %%% A)$i$j = c * A$i$j`,
    CMATRIX_ARITH_TAC);;

let CMATRIX_ADD_COMPONENT = prove
    (`!A B:complex^N^M i j. (A + B)$i$j = A$i$j + B$i$j`,
    CMATRIX_ARITH_TAC);;

let CMATRIX_SUB_COMPONENT = prove
    (`!A B:complex^N^M i j. (A - B)$i$j = A$i$j - B$i$j`,
    CMATRIX_ARITH_TAC);;

let CMATRIX_NEG_COMPONENT = prove
    (`!A:complex^N^M i j. (--A)$i$j = --(A$i$j)`,
    CMATRIX_ARITH_TAC);;

let CTRANSP_COMPONENT = prove
 (`!A:complex^N^M i j. (ctransp A)$i$j = A$j$i`,
  CMATRIX_ARITH_TAC);;    
    
let CMAT_COMPONENT = prove
 (`!n i j.
        1 <= i /\ i <= dimindex(:M) /\
        1 <= j /\ j <= dimindex(:N)
        ==> (cmat n:complex^N^M)$i$j = if i = j then Cx(&n) else Cx(&0)`,
  CMATRIX_ARITH_TAC);;

let CMAT_0_COMPONENT = prove
 (`!i j. (cmat 0:complex^N^M)$i$j = Cx(&0)`,
  CMATRIX_ARITH_TAC);;

let CMATRIX_ADD_ROW = prove
 (`!X:complex^M^N Y:complex^M^N i. (X + Y)$i = X$i + Y$i`,
  REWRITE_TAC[CART_EQ_FULL;VECTOR_ADD_COMPONENT;CVECTOR_ADD_COMPONENT;CMATRIX_ADD_COMPONENT]);; 

let CMATRIX_SUB_ROW = prove
 (`!X Y:complex^M^N i. (X - Y)$i = X$i - Y$i`,
  REWRITE_TAC[CART_EQ_FULL;VECTOR_SUB_COMPONENT; CVECTOR_SUB_COMPONENT;CMATRIX_SUB_COMPONENT]);;

let CMATRIX_NEG_ROW = prove
  (`!X:complex^M^N i. (--X)$i = --(X$i)`,
  REWRITE_TAC[CART_EQ_FULL; VECTOR_NEG_COMPONENT; CVECTOR_NEG_COMPONENT;CMATRIX_NEG_COMPONENT]);;

let CMAT_0_ROW = prove
 (`!i. cmat 0:complex^M^N$i = mat 0`,
  SIMP_TAC[CART_EQ; MAT_0_COMPONENT; CMAT_0_COMPONENT] THEN
  SIMP_TAC[CX_DEF;complex;DIMINDEX_2;FORALL_2;ARITH;VECTOR_2]);;
  
let CMATRIX_ADD_SYM = CMATRIX_ARITH `!x y:complex^N^M. x + y = y + x`;;

let VECTOR_ADD_LID = CMATRIX_ARITH `!x. cmat 0 + x = x`;;

let CMATRIX_ADD_RID = CMATRIX_ARITH `!x. x + cmat 0 = x`;;

let CMATRIX_SUB_REFL = CMATRIX_ARITH `!x. x - x = cmat 0`;;

let CMATRIX_ADD_LINV = CMATRIX_ARITH `!x. --x + x = cmat 0`;;

let CMATRIX_ADD_RINV = CMATRIX_ARITH `!x. x + --x = cmat 0`;;

let CMATRIX_SUB_RADD = CMATRIX_ARITH `!x y. x - (x + y) = --y:complex^N^M`;;

let CMATRIX_NEG_SUB = CMATRIX_ARITH `!x:complex^N^M y. --(x - y) = y - x`;;

let CMATRIX_SUB_EQ = CMATRIX_ARITH `!x y. (x - y = cmat 0) <=> (x = y)`;;

let CMATRIX_CMUL_ASSOC = CMATRIX_ARITH `!a b x. a %%% (b %%% x) = (a * b) %%% x`;;

let CMATRIX_CMUL_LID = CMATRIX_ARITH `!x. Cx(&1) %%% x = x`;;

let CMATRIX_CMUL_LZERO = CMATRIX_ARITH `!x. Cx(&0) %%% x = cmat 0`;;

let CMATRIX_SUB_ADD = CMATRIX_ARITH `!x y. (x - y) + y = x:complex^N^M`;;

let CMATRIX_SUB_ADD2 = CMATRIX_ARITH `!x y. y + (x - y) = x:complex^N^M`;;

let CMATRIX_CMUL_ADD_LDISTRIB = CMATRIX_ARITH `!c x y. c %%% (x + y) = c %%% x + c %%% y`;;

let CMATRIX_CMUL_SUB_LDISTRIB = CMATRIX_ARITH `!c x y. c %%% (x - y) = c %%% x - c %%% y`;;

let CMATRIX_CMUL_ADD_RDISTRIB = CMATRIX_ARITH `!a b x. (a + b) %%% x = a %%% x + b %%% x`;;

let CMATRIX_CMUL_SUB_RDISTRIB = CMATRIX_ARITH `!a b x. (a - b) %%% x = a %%% x - b %%% x`;;

let CMATRIX_ADD_SUB = CMATRIX_ARITH `!x y. (x + y:complex^N^M) - x = y`;;

let CMATRIX_EQ_ADDR = CMATRIX_ARITH `!x y. (x + y = x) <=> (y = cmat 0)`;;

let CMATRIX_SUB = CMATRIX_ARITH `!x y. x - y = x + --(y:complex^N^M)`;;

let CMATRIX_SUB_RZERO = CMATRIX_ARITH `!x. x - cmat 0 = x`;;

let CMATRIX_CMUL_RZERO = CMATRIX_ARITH `!c. c %%% cmat 0 = cmat 0`;;

let CMATRIX_NEG_MINUS1 = CMATRIX_ARITH `!x. --x = (--Cx(&1)) %%% x`;;

let CMATRIX_ADD_ASSOC = CMATRIX_ARITH `!x y z. (x:complex^N^M) + y + z = (x + y) + z`;;

let CMATRIX_SUB_LZERO = CMATRIX_ARITH `!x. cmat 0 - x = --x`;;

let CMATRIX_NEG_NEG = CMATRIX_ARITH `!x. --(--(x:complex^N^M)) = x`;;

let CMATRIX_CMUL_LNEG = CMATRIX_ARITH `!c x. --c %%% x = --(c %%% x)`;;

let CMATRIX_CMUL_RNEG = CMATRIX_ARITH `!c x. c %%% --x = --(c %%% x)`;;

let CMATRIX_NEG_0 = CMATRIX_ARITH `--(cmat 0) = cmat 0`;;

let CMATRIX_NEG_EQ_0 = CMATRIX_ARITH `!x. --x = cmat 0 <=> x = cmat 0`;;

let CMATRIX_EQ_NEG2 = CMATRIX_ARITH `!x y:complex^N^M. --x = --y <=> x = y`;;

let CMATRIX_ADD_AC = CMATRIX_ARITH
  `(m + n = n + m:complex^N^M) /\
   ((m + n) + p = m + n + p) /\
   (m + n + p = n + m + p)`;;
   
let CMAT_CMUL = CMATRIX_ARITH `!a. cmat a = Cx(&a) %%% cmat 1`;;

let CMATRIX_MUL_ASSOC = CMATRIX_ARITH `!a:complex^N^M b:complex^P^N x:complex^Q^P. a ** b ** x = (a ** b) ** x`;;

let CMATRIX_MUL_LID = CMATRIX_ARITH `!x:complex^N^M. cmat 1 ** x = x`;;

let CMATRIX_MUL_RID = CMATRIX_ARITH `!x. x ** cmat 1 = x`;;

let CMATRIX_MUL_LZERO = CMATRIX_ARITH `!x. cmat 0 ** x = cmat 0`;;

let CMATRIX_MUL_RZERO = CMATRIX_ARITH `!x. x ** cmat 0 = cmat 0`;;

let CMATRIX_ADD_LDISTRIB = CMATRIX_ARITH `!c:complex^N^M x:complex^P^N y. c ** (x + y) = c ** x + c ** y`;;

let CMATRIX_SUB_LDISTRIB = CMATRIX_ARITH `!c:complex^N^M x:complex^P^N y. c ** (x - y) = c ** x - c ** y`;;

let CMATRIX_ADD_RDISTRIB = CMATRIX_ARITH `!a:complex^N^M b x:complex^P^N.(a + b) ** x = a ** x + b ** x`;;

let CMATRIX_SUB_RDISTRIB = CMATRIX_ARITH `!a:complex^N^M b x:complex^P^N. (a - b) ** x = a ** x - b ** x`;;

let CMATRIX_MUL_LMUL = CMATRIX_ARITH `!A:complex^N^M B:complex^P^N c. (c %%% A) ** B = c %%% (A ** B)`;;

let CMATRIX_MUL_RMUL = CMATRIX_ARITH `!A:complex^N^M B:complex^P^N c. A ** (c %%% B) = c %%% (A ** B)`;;

let CMATRIX_MUL_LNEG = CMATRIX_ARITH `!A:complex^N^M B:complex^P^N. (--A) ** B = --(A ** B)`;;

let CMATRIX_MUL_RNEG = CMATRIX_ARITH `!A:complex^N^M B:complex^P^N. A ** --B = --(A ** B)`;;

let CMATRIX_NEG_NEG = CMATRIX_ARITH `!A:complex^N^M. --(--A) = A`;;

let CMATRIX_VECTOR_MUL_ASSOC = CMATRIX_ARITH `!A:complex^N^M B:complex^P^N x:complex^P. A ** B ** x = (A ** B) ** x`;;

let CMATRIX_VECTOR_MUL_LID = CMATRIX_ARITH `!x:complex^N. cmat 1 ** x = x`;;

let CMATRIX_VECTOR_MUL_LZERO = CMATRIX_ARITH `!x:complex^N. cmat 0 ** x = cvector_zero`;;

let CMATRIX_VECTOR_MUL_RZERO = CMATRIX_ARITH `!A:complex^M^N. A ** cvector_zero = cvector_zero`;;

let CMATRIX_VECTOR_MUL_ADD_LDISTRIB = CMATRIX_ARITH `!A:complex^M^N x:complex^M y. A ** (x + y) = A ** x + A ** y`;;

let CMATRIX_VECTOR_MUL_SUB_LDISTRIB = CMATRIX_ARITH `!A:complex^M^N x:complex^M y. A ** (x - y) = A ** x - A ** y`;;

let CMATRIX_VECTOR_MUL_ADD_RDISTRIB = CMATRIX_ARITH `!A:complex^M^N B x:complex^M. (A + B) ** x = (A ** x) + (B ** x)`;;

let CMATRIX_VECTOR_MUL_SUB_RDISTRIB = CMATRIX_ARITH `!A:complex^M^N B x:complex^M. (A - B) ** x = (A ** x) - (B ** x)`;;

let CMATRIX_VECTOR_MUL_LMUL = CMATRIX_ARITH `!A:complex^M^N x:complex^M c. (c %%% A) ** x = c % (A ** x)`;;

let CMATRIX_VECTOR_MUL_LNEG = CMATRIX_ARITH `!A:complex^M^N x:complex^M. --A ** x = --(A ** x)`;;

let CMATRIX_VECTOR_MUL_RNEG = CMATRIX_ARITH `!A:complex^M^N x:complex^M. A ** --x = --(A ** x)`;;

let CMATRIX_TRANSP_MUL = CMATRIX_ARITH `!A B. ctransp(A ** B) = ctransp(B) ** ctransp(A)`;;

let CTRANSP_EQ_0 = CMATRIX_ARITH `!A:complex^N^M. ctransp A = cmat 0 <=> A = cmat 0`;;

let CMATRIX_EQ = prove
(`!A:complex^N^M B. (A = B) = !x:complex^N. A ** x = B ** x`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GEN `i:num` o SPEC `vector_to_cvector(basis i):complex^N`) THEN
  SIMP_TAC[CART_EQ; cmatrix_vector_mul; LAMBDA_BETA;complex_mul; basis;vector_to_cvector;vector_map;complex;CX_DEF;RE_DEF;IM_DEF;VECTOR_2;vsum;DIMINDEX_2;FORALL_2] THEN
  SIMP_TAC[SUM_DELTA;COND_RMUL_0; REAL_MUL_RZERO;REAL_SUB_RZERO;REAL_ADD_LID] THEN
  REWRITE_TAC[TAUT `((if P then b else c) = (if P then a else c)) <=> (P ==> b = a)`] THEN
  SIMP_TAC[REAL_MUL_RID; IN_NUMSEG]);;
  
let CMATRIX_EQ_0 = prove
 (`!A:complex^N^N. A = cmat 0 <=> !x. A ** x = cvector_zero`,
  REWRITE_TAC[CMATRIX_EQ; CMATRIX_VECTOR_MUL_LZERO]);;

let CMATRIX_VECTOR_MUL_COMPONENT = prove
 (`!A:complex^N^M x k.
    1 <= k /\ k <= dimindex(:M) ==> ((A ** x)$k = (A$k) cdot (cvector_cnj x))`,
  SIMP_TAC[CART_EQ;cmatrix_vector_mul; LAMBDA_BETA; cdot;cnj;complex;RE_DEF;IM_DEF;DIMINDEX_2;FORALL_2;VECTOR_2;vsum;complex_mul;cvector_cnj;vector_map;REAL_NEG_NEG]);;

let CDOT_LMUL_CMATRIX = prove
 (`!A:complex^N^M x:complex^M y:complex^N. (x ** A) cdot (cvector_cnj y) = x cdot cvector_cnj (A ** y)`,
  SIMP_TAC[CART_EQ;cdot; cmatrix_vector_mul; vector_cmatrix_mul;cvector_cnj;vector_map; LAMBDA_BETA;cnj;complex_mul;complex;RE_DEF;IM_DEF;VECTOR_2;vsum;DIMINDEX_2;FORALL_2;ARITH_RULE `1 <= 2`;LE_REFL;REAL_NEG_NEG] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL;GSYM SUM_RMUL;GSYM SUM_ADD_NUMSEG;GSYM SUM_SUB_NUMSEG] THEN
  CONJ_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  REPEAT (MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN SIMP_TAC[]) THEN REAL_ARITH_TAC);;

let TRANSP_CMATRIX_CMUL = prove
 (`!A:complex^M^N c. ctransp(c %%% A) = c %%% ctransp A`,
  CMATRIX_ARITH_TAC);;
  
let TRANSP_CMATRIX_ADD = prove
 (`!A B:complex^N^M. ctransp(A + B) = ctransp A + ctransp B`,
  CMATRIX_ARITH_TAC);;
  
let TRANSP_CMATRIX_SUB = prove
 (`!A B:complex^N^M. ctransp(A - B) = ctransp A - ctransp B`,
  CMATRIX_ARITH_TAC);;
  
let TRANSP_CMATRIX_NEG = prove
 (`!A:complex^N^M. ctransp(--A) = --(ctransp A)`,
  CMATRIX_ARITH_TAC);;
  
let TRANSP_CMAT = prove
 (`!n. ctransp(cmat n) = cmat n`,
  CMATRIX_ARITH_TAC);;

let CTRANSP_CTRANSP = prove
 (`!A:complex^N^M. ctransp(ctransp A) = A`,
  CMATRIX_ARITH_TAC);;
  
let CTRANSP_EQ = prove
 (`!A B:complex^M^N. ctransp A = ctransp B <=> A = B`,
  CMATRIX_ARITH_TAC);;
  
let VECTOR_CMATRIX_MUL_TRANSP = prove
 (`!A:complex^M^N x:complex^N. x ** A = ctransp A ** x`,
  CMATRIX_ARITH_TAC);;

let CMATRIX_VECTOR_MUL_TRANSP = prove
 (`!A:complex^M^N x:complex^M. A ** x = x ** ctransp A`,
  CMATRIX_ARITH_TAC);;
  
let CMATRIX_CMUL_EQ_0 = prove
 (`!A:complex^M^N c. c %%% A = cmat 0 <=> c = Cx(&0) \/ A = cmat 0`,
  SIMP_TAC[CART_EQ; CMATRIX_CMUL_COMPONENT; CMAT_COMPONENT; COND_ID] THEN
  ONCE_SIMP_TAC[GSYM CART_EQ] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = Cx(&0)` THEN
  ASM_REWRITE_TAC[COMPLEX_ENTIRE]);;

let CMAT_EQ = prove
    (`!m n. (cmat m = cmat n) <=> (m = n)`,
    SIMP_TAC[CART_EQ; CMAT_COMPONENT;COND_COMPONENT] THEN
    SIMP_TAC[DIMINDEX_2;FORALL_2;CX_DEF;complex;VECTOR_2] THEN
    REPEAT STRIP_TAC THEN
    MESON_TAC[REAL_OF_NUM_EQ; DIMINDEX_GE_1; LE_REFL]);;
    
let MATRIX_ADD_SUB = CMATRIX_ARITH `!A B:real^N^M. (B + A) - B = A`;;

(* ------------------------------------------------------------------------- *)
(* Block Real Matrix Definition and Properties                                      *)
(* ------------------------------------------------------------------------- *)

let blockmatrix = new_definition
  `((blockmatrix:real^N^N->real^N^N->real^N^N->real^N^N->real^(N,N)finite_sum^(N,N)finite_sum) A B C D) = 
    ((lambda i j. if (1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)) 
            then  A$i$j
            else if (1 <= i /\ i <= dimindex(:N) /\ (dimindex(:N)+1) <= j /\ j <= dimindex (:(N,N)finite_sum)) 
            then  B$i$(j-dimindex(:N))
            else if ((dimindex(:N)+1) <= i /\ i <= dimindex (:(N,N)finite_sum) /\ 1 <= j /\ j <= dimindex(:N)) 
            then  C$(i-dimindex(:N))$j
            else if ((dimindex(:N)+1) <= i /\ i <= dimindex (:(N,N)finite_sum) /\ 
                     (dimindex(:N)+1) <= j /\ j <= dimindex (:(N,N)finite_sum)) 
            then  D$(i-dimindex(:N))$(j-dimindex(:N))
            else  &0):real^(N,N)finite_sum^(N,N)finite_sum)`;;

(* ------------------------------------------------------------------------- *)
(*Definition for Matrix From real^2N^2N Tranfer to real^N^N                  *)
(* ------------------------------------------------------------------------- *)

let blockmatrix2a = new_definition
`(blockmatrix2a:real^(N,N)finite_sum^(N,N)finite_sum -> real^N^N) S = (lambda i j. S$i$j)`;;

let blockmatrix2b = new_definition
`(blockmatrix2b:real^(N,N)finite_sum^(N,N)finite_sum -> real^N^N) S = (lambda i j. S$i$(j+dimindex(:N)))`;;

let blockmatrix2c = new_definition
`(blockmatrix2c:real^(N,N)finite_sum^(N,N)finite_sum -> real^N^N) S = (lambda i j. S$(i+dimindex(:N))$j)`;;

let blockmatrix2d = new_definition
`(blockmatrix2d:real^(N,N)finite_sum^(N,N)finite_sum -> real^N^N) S = (lambda i j. S$(i+dimindex(:N))$(j+dimindex(:N)))`;;


(* ------------------------------------------------------------------------- *)
(*Definition for Matrix From real^N^N Tranfer to real^2N^2N                  *)
(* ------------------------------------------------------------------------- *)

let a2blockmatrix = new_definition
`(a2blockmatrix:real^N^N -> real^(N,N)finite_sum^(N,N)finite_sum) A = 
     ((lambda i j. if (1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)) 
            then A$i$j else &0):real^(N,N)finite_sum^(N,N)finite_sum)`;;

let b2blockmatrix = new_definition
`(b2blockmatrix:real^N^N -> real^(N,N)finite_sum^(N,N)finite_sum) B = 
     ((lambda i j. if (1 <= i /\ i <= dimindex(:N) /\ 
                      (dimindex(:N) + 1) <= j /\ j <= dimindex(:(N,N)finite_sum)) 
            then B$i$(j-dimindex(:N)) else &0):real^(N,N)finite_sum^(N,N)finite_sum)`;;

let c2blockmatrix = new_definition
`(c2blockmatrix:real^N^N -> real^(N,N)finite_sum^(N,N)finite_sum) C = 
     ((lambda i j. if ((dimindex(:N)+1) <= i /\ i <= dimindex (:(N,N)finite_sum) /\ 1 <= j /\ j <= dimindex(:N)) 
            then C$(i-dimindex(:N))$j else &0):real^(N,N)finite_sum^(N,N)finite_sum)`;;

let d2blockmatrix = new_definition
`(d2blockmatrix:real^N^N -> real^(N,N)finite_sum^(N,N)finite_sum) D = 
     ((lambda i j. if ((dimindex(:N)+1) <= i /\ i <= dimindex (:(N,N)finite_sum) /\ 
                      (dimindex(:N)+1) <= j /\ j <= dimindex (:(N,N)finite_sum))
            then D$(i-dimindex(:N))$(j-dimindex(:N)) else &0):real^(N,N)finite_sum^(N,N)finite_sum)`;;


let BLOCKMATRIX2A_COMPONENT = prove
(`!A B C D:real^N^N. (blockmatrix2a (blockmatrix A B C D)) = A`,
  REPEAT GEN_TAC THEN REWRITE_TAC[blockmatrix2a;blockmatrix] THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN 
  SUBGOAL_THEN `!x. x <= dimindex (:N) ==> x <= dimindex(:(N,N)finite_sum)` ASSUME_TAC THENL
  [REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN ASM_SIMP_TAC[ARITH_RULE `x:num <= n ==> x <= n + n`];ALL_TAC] THEN 
  ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA]);;

let BLOCKMATRIX2B_COMPONENT = prove
(`!A B C D:real^N^N. (blockmatrix2b (blockmatrix A B C D)) = B`,
  REPEAT GEN_TAC THEN REWRITE_TAC[blockmatrix2b;blockmatrix] THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN 
  SUBGOAL_THEN `!x. x <= dimindex (:N) ==> x <= dimindex(:(N,N)finite_sum)` ASSUME_TAC THENL
  [REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN ASM_SIMP_TAC[ARITH_RULE `x:num <= n ==> x <= n + n`];ALL_TAC] THEN
  ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  SUBGOAL_THEN `!x. 1 <= x ==>1 <= x + dimindex(:N)` ASSUME_TAC THENL
  [ASM_SIMP_TAC [ARITH_RULE `1 <= x ==> 1 <= x + (n:num)`];ALL_TAC] THEN
  SUBGOAL_THEN `!x. 1 <= x ==> dimindex(:N) + 1  <= x + dimindex(:N)` ASSUME_TAC THENL 
  [ASM_SIMP_TAC [ARITH_RULE `1 <= x ==> n + 1 <= x + (n:num)`];ALL_TAC] THEN
  SUBGOAL_THEN `!x. x <= dimindex(:N) ==> x + dimindex(:N) <= dimindex(:(N,N)finite_sum)` ASSUME_TAC THENL
  [REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN 
  ASM_SIMP_TAC [ARITH_RULE `i <= (n:num) ==> i + n <= n + n`];ALL_TAC] THEN
  ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN REWRITE_TAC[ARITH_RULE `((a:num) + n) - n = a`] THEN
  ASM_SIMP_TAC [ARITH_RULE `(n:num) + 1 <= i + n ==> ~(i + n <= n)`]);;

let BLOCKMATRIX2C_COMPONENT = prove
(`!A B C D:real^N^N. (blockmatrix2c (blockmatrix A B C D)) = C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[blockmatrix2c;blockmatrix] THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN 
  SUBGOAL_THEN `!x. x <= dimindex (:N) ==> x <= dimindex(:(N,N)finite_sum)` ASSUME_TAC THENL
  [REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN ASM_SIMP_TAC[ARITH_RULE `x:num <= n ==> x <= n + n`];ALL_TAC] THEN
  ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  SUBGOAL_THEN `!x. 1 <= x ==>1 <= x + dimindex(:N)` ASSUME_TAC THENL
  [ASM_SIMP_TAC [ARITH_RULE `1 <= x ==> 1 <= x + (n:num)`];ALL_TAC] THEN
  SUBGOAL_THEN `!x. 1 <= x ==> dimindex(:N) + 1  <= x + dimindex(:N)` ASSUME_TAC THENL 
  [ASM_SIMP_TAC [ARITH_RULE `1 <= x ==> n + 1 <= x + (n:num)`];ALL_TAC] THEN
  SUBGOAL_THEN `!x. x <= dimindex(:N) ==> x + dimindex(:N) <= dimindex(:(N,N)finite_sum)` ASSUME_TAC THENL
  [REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN 
  ASM_SIMP_TAC [ARITH_RULE `i <= (n:num) ==> i + n <= n + n`];ALL_TAC] THEN
  ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN REWRITE_TAC[ARITH_RULE `((a:num) + n) - n = a`] THEN
  ASM_SIMP_TAC [ARITH_RULE `(n:num) + 1 <= i + n ==> ~(i + n <= n)`]);;

let BLOCKMATRIX2D_COMPONENT = prove
(`!A B C D:real^N^N. (blockmatrix2d (blockmatrix A B C D)) = D`,
  REPEAT GEN_TAC THEN REWRITE_TAC[blockmatrix2d;blockmatrix] THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN 
  SUBGOAL_THEN `!x. 1 <= x ==>1 <= x + dimindex(:N)` ASSUME_TAC THENL
  [ASM_SIMP_TAC [ARITH_RULE `1 <= x ==> 1 <= x + (n:num)`];ALL_TAC] THEN
  SUBGOAL_THEN `!x. x <= dimindex(:N) ==> x + dimindex(:N) <= dimindex(:(N,N)finite_sum)` ASSUME_TAC THENL
  [REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN 
  ASM_SIMP_TAC [ARITH_RULE `i <= (n:num) ==> i + n <= n + n`];ALL_TAC] THEN
  ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  SUBGOAL_THEN `!x. 1 <= x ==> dimindex(:N) + 1  <= x + dimindex(:N)` ASSUME_TAC THENL
  [ASM_SIMP_TAC [ARITH_RULE `1 <= x ==> n + 1 <= x + (n:num)`];ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `((a:num) + n) - n = a`] THEN 
  ASM_SIMP_TAC [ARITH_RULE `(n:num) + 1 <= i + n ==> ~(i + n <= n)`]);;

let A2BLOCKMATRIX_PART = prove
(`!A:real^N^N. (a2blockmatrix A) = (blockmatrix A (mat 0) (mat 0) (mat 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[a2blockmatrix;blockmatrix] THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MAT_0_COMPONENT] THEN
  COND_CASES_TAC THEN CONV_TAC SYM_CONV THEN COND_CASES_TAC THENL
  [REWRITE_TAC[]; ALL_TAC;ASM_MESON_TAC[];ALL_TAC] THEN COND_CASES_TAC THENL
  [ASM_MESON_TAC[];ALL_TAC;REWRITE_TAC[]; ALL_TAC] THEN COND_CASES_TAC THENL
  [ASM_MESON_TAC[];ALL_TAC;REWRITE_TAC[]; ALL_TAC] THEN COND_CASES_TAC THENL
  [ASM_MESON_TAC[];ASM_MESON_TAC[];REWRITE_TAC[];REWRITE_TAC[]]);;

let B2BLOCKMATRIX_PART = prove
(`!B:real^N^N. (b2blockmatrix B) = (blockmatrix (mat 0) B (mat 0) (mat 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[b2blockmatrix;blockmatrix] THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MAT_0_COMPONENT] THEN
  COND_CASES_TAC THEN CONV_TAC SYM_CONV THEN COND_CASES_TAC THENL
  [ASM_ARITH_TAC;ALL_TAC;REWRITE_TAC[];ALL_TAC] THEN COND_CASES_TAC THENL
  [REWRITE_TAC[];ALL_TAC;ASM_ARITH_TAC;ALL_TAC] THEN COND_CASES_TAC THENL
  [ASM_ARITH_TAC;ALL_TAC;REWRITE_TAC[];ALL_TAC] THEN COND_CASES_TAC THENL
  [ASM_ARITH_TAC;ASM_ARITH_TAC;REWRITE_TAC[];REWRITE_TAC[]]);;


let C2BLOCKMATRIX_PART = prove
(`!C:real^N^N. (c2blockmatrix C) = (blockmatrix (mat 0) (mat 0) C (mat 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c2blockmatrix;blockmatrix] THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MAT_0_COMPONENT] THEN
  COND_CASES_TAC THEN CONV_TAC SYM_CONV THEN COND_CASES_TAC THENL
  [ASM_ARITH_TAC;ALL_TAC;REWRITE_TAC[];ALL_TAC] THEN COND_CASES_TAC THENL
  [ASM_ARITH_TAC;ALL_TAC;REWRITE_TAC[];ALL_TAC] THEN COND_CASES_TAC THENL
  [REWRITE_TAC[];ALL_TAC;ASM_ARITH_TAC;ALL_TAC] THEN COND_CASES_TAC THENL
  [ASM_ARITH_TAC;ASM_ARITH_TAC;REWRITE_TAC[];REWRITE_TAC[]]);;


let D2BLOCKMATRIX_PART = prove
(`!D:real^N^N. (d2blockmatrix D) = (blockmatrix (mat 0) (mat 0) (mat 0) D)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[d2blockmatrix;blockmatrix] THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MAT_0_COMPONENT] THEN
  COND_CASES_TAC THEN CONV_TAC SYM_CONV THEN COND_CASES_TAC THENL
  [ASM_ARITH_TAC;ALL_TAC;REWRITE_TAC[];ALL_TAC] THEN COND_CASES_TAC THENL
  [ASM_ARITH_TAC;ALL_TAC;REWRITE_TAC[];ALL_TAC] THEN COND_CASES_TAC THENL
  [ASM_ARITH_TAC;REWRITE_TAC[];REWRITE_TAC[];REWRITE_TAC[]]);;


let BLOCKMATRIX_ADD = prove
(`!A1 B1 C1 D1 A2 B2 C2 D2:real^N^N. blockmatrix A1 B1 C1 D1 + blockmatrix A2 B2 C2 D2 =
  blockmatrix(A1+A2) (B1 + B2) (C1+C2) (D1+D2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[blockmatrix;MATRIX_ADD_COMPONENT;matrix_add] THEN
  ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN CONV_TAC ARITH_RULE);;


let BLOCKMATRIX_SUB = prove
(`!A1 B1 C1 D1 A2 B2 C2 D2:real^N^N. blockmatrix A1 B1 C1 D1 - blockmatrix A2 B2 C2 D2 =
  blockmatrix(A1 - A2) (B1 - B2) (C1 - C2) (D1 - D2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[blockmatrix;MATRIX_SUB_COMPONENT;matrix_sub] THEN
  ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN CONV_TAC ARITH_RULE);;


let BLOCKMATRIX_CMUL = prove
(`!c:real A B C D:real^N^N. c %% (blockmatrix A B C D) =
  blockmatrix(c %% A) (c %% B) (c %% C) (c %% D)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[blockmatrix] THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_CMUL_COMPONENT] THEN
  ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN CONV_TAC ARITH_RULE);;

let BLOCKMATRIX_MUL = prove
(`!A1 B1 C1 D1 A2 B2 C2 D2:real^N^N. blockmatrix A1 B1 C1 D1 ** blockmatrix A2 B2 C2 D2 =
  blockmatrix(A1**A2 + B1**C2) (A1**B2 + B1**D2) (C1**A2+D1**C2) (C1**B2 + D1**D2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_mul] THEN SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[blockmatrix] THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  CONV_TAC SYM_CONV THEN COND_CASES_TAC THENL [ALL_TAC; COND_CASES_TAC THENL 
  [ALL_TAC; COND_CASES_TAC THENL [ALL_TAC; COND_CASES_TAC THENL[ALL_TAC;ASM_ARITH_TAC]]]] THEN 
  REWRITE_TAC[MATRIX_ADD_COMPONENT] THEN
  ASSUME_TAC (prove (`!x. dimindex(:N) + 1 <= x ==> 1 <= x - dimindex(:N)`,ASM_ARITH_TAC)) THEN
  ASSUME_TAC (prove (`!x. x <= dimindex (:(N,N)finite_sum) ==> x - dimindex (:N) <= dimindex (:N)`, 
     REPEAT STRIP_TAC THEN 
     ASM_REWRITE_TAC[ARITH_RULE `(x:num) - n <= n <=> x <= (n + n)`; GSYM DIMINDEX_FINITE_SUM])) THEN
  ASSUME_TAC (prove (`!x. dimindex (:N) + 1 <= x ==> (~(x <= dimindex (:N)))`,
     STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `(n:num) + 1 <= x ==> ~(x <= n)`])) THEN 
  ASSUME_TAC (prove (`!x. 1 <= x ==> (~(x + dimindex (:N) <= dimindex (:N)))`, 
     STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `1 <= (x:num) ==> ~(x + n <= n)`])) THEN
  ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  ASSUME_TAC (prove (`1 <= dimindex(:N) + 1`, 
     REWRITE_TAC [ARITH_RULE `1 <= (m:num) + 1 <=> 0 <= m`] THEN 
     MATCH_MP_TAC (ARITH_RULE `1 <= (m:num) ==> 0 <= m`) THEN REWRITE_TAC [DIMINDEX_GE_1])) THEN
  ASM_SIMP_TAC[DIMINDEX_FINITE_SUM;SUM_ADD_SPLIT] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[SUM_OFFSET;ARITH_RULE `((a:num) + n) - n = a`]);;

let BLOCKMATRIX_NEG = prove
(`!A B C D:real^N^N. -- blockmatrix A B C D = blockmatrix (-- A) (-- B) (-- C) (-- D)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[blockmatrix;matrix_neg] THEN SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN COND_CASES_TAC THENL
  [ASM_ARITH_TAC;COND_CASES_TAC THENL [ALL_TAC;COND_CASES_TAC THENL [ALL_TAC;COND_CASES_TAC THENL
  [ALL_TAC;ASM_ARITH_TAC]]]] THEN 
  ASSUME_TAC (prove (`!x. dimindex(:N) + 1 <= x ==> 1 <= x - dimindex(:N)`,ASM_ARITH_TAC)) THEN
  ASSUME_TAC (prove (`!x. x <= dimindex (:(N,N)finite_sum) ==> x - dimindex (:N) <= dimindex (:N)`, 
     REPEAT STRIP_TAC THEN 
     ASM_REWRITE_TAC[ARITH_RULE `(x:num) - n <= n <=> x <= (n + n)`; GSYM DIMINDEX_FINITE_SUM])) THEN
  ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA]
);;

let BLOCKMATRIX_TRANSP = prove
(`!A B C D:real^N^N. transp (blockmatrix A B C D) = blockmatrix (transp A) (transp C) (transp B) (transp D)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[transp; blockmatrix] THEN SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN 
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL 
       [CONV_TAC SYM_CONV;ALL_TAC] THEN 
  COND_CASES_TAC THENL
       [REWRITE_TAC[];ALL_TAC;CONV_TAC SYM_CONV;ALL_TAC] THEN 
  COND_CASES_TAC THENL
       [ASM_MESON_TAC[];ALL_TAC;ASM_MESON_TAC[];ALL_TAC;CONV_TAC SYM_CONV;ALL_TAC] THEN 
  COND_CASES_TAC THENL 
       [ASM_MESON_TAC[];ALL_TAC;ASM_MESON_TAC[];ALL_TAC;ASM_MESON_TAC[];
       ALL_TAC;CONV_TAC SYM_CONV;CONV_TAC SYM_CONV] THEN
  COND_CASES_TAC THENL 
       [ASM_MESON_TAC[];ASM_MESON_TAC[];REWRITE_TAC[GSYM transp;TRANSP_COMPONENT];ALL_TAC;
        SUBGOAL_THEN `1 <= i' - dimindex(:N) /\ i' - dimindex(:N) <= dimindex(:N)` ASSUME_TAC THEN
        POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN
        REWRITE_TAC[TAUT `(a /\ b) /\ c /\ (d /\ e) /\ f /\ g /\ h /\ i /\ j /\ k ==> l <=> 
                    a /\ c /\ (d /\ e) /\ f /\ g /\ i /\ j /\ k ==> b /\ h  ==> l`] THEN DISCH_TAC THEN
        REWRITE_TAC[DIMINDEX_FINITE_SUM;
                    ARITH_RULE `n + 1 <= a /\ a <= (n + n)  ==> 1 <= (a - n) /\ (a - n) <= n`] THEN
        ASM_SIMP_TAC [LAMBDA_BETA];
        ALL_TAC;ASM_MESON_TAC[];ALL_TAC;ASM_MESON_TAC[];ALL_TAC] THEN
  COND_CASES_TAC THENL
        [ALL_TAC;ALL_TAC;ALL_TAC;COND_CASES_TAC;ALL_TAC;COND_CASES_TAC;ALL_TAC;COND_CASES_TAC] THENL
        [ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;
         ALL_TAC;COND_CASES_TAC;ALL_TAC;ALL_TAC;COND_CASES_TAC] THENL
        [ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;
         REWRITE_TAC[GSYM transp;TRANSP_COMPONENT];ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;REWRITE_TAC[]] THEN
  ASM_MESON_TAC[]);;

let BLOCKMATRIX_EQ_MAT = prove
(`!k:num. blockmatrix ((mat k):real^N^N) (mat 0) (mat 0) (mat k) = mat k`,
let lem1 = MESON [ARITH_RULE `n + 1 = SUC n`;LE_SUC_LT;LET_TRANS;LT_IMP_NE] `!m n p:num. m <= p /\ p + 1 <= n ==> ~(m = n)` in
let lem2 = MESON [ARITH_RULE`!N i:num. N + 1 <= i ==>  N + i - N = i`;ARITH_RULE`!N i:num. N + 1 <= i ==>  i - N + N = i`;LE_ADD_RCANCEL;LE_ADD_LCANCEL] `!N i:num. N + 1 <= i /\ i <= N + N ==> 1 <= i - N /\ i - N <= N` in
SIMP_TAC[CART_EQ;LAMBDA_BETA;blockmatrix;MAT_COMPONENT;MAT_0_COMPONENT] THEN
REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [SIMP_TAC[];ALL_TAC] THEN
COND_CASES_TAC THENL [ASM_MESON_TAC[lem1];ALL_TAC] THEN 
COND_CASES_TAC THENL [ASM_MESON_TAC[lem1];ALL_TAC] THEN
COND_CASES_TAC THENL [ASM_SIMP_TAC[GSYM DIMINDEX_FINITE_SUM;lem2;MAT_COMPONENT];ALL_TAC] THEN ASM_ARITH_TAC);;

let BLOCKMATRIX_UNIQUE = prove 
(`!A1 A2 B1 B2 C1 C2 D1 D2:real^N^N. blockmatrix A1 B1 C1 D1 = blockmatrix A2 B2 C2 D2 <=> A1 = A2 /\ B1 = B2 /\ C1 = C2 /\ D1 = D2`,
let lem1 = MESON [LE_ADD2;ADD_0;LE_REFL] `!n:num. 0 <= n ==> n <= n + n` in
let lem2 =  MESON [DIMINDEX_FINITE_SUM;DIMINDEX_GE_1;ARITH_RULE `1 <= x ==> 0 <= x`;lem1;LE_TRANS] `!i. (i <= dimindex(:N)) ==> (i <= dimindex(:(N,N)finite_sum))` in
REPEAT GEN_TAC THEN EQ_TAC THENL
[SIMP_TAC[blockmatrix;CART_EQ;LAMBDA_BETA] THEN
 REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
 REPEAT STRIP_TAC THENL
 [FIRST_X_ASSUM (MP_TAC o SPECL [`i:num`;`i':num`]);
  FIRST_X_ASSUM (MP_TAC o SPECL [`i:num`;`i' + dimindex (:N)`]);
  FIRST_X_ASSUM (MP_TAC o SPECL [`i + dimindex (:N)`;`i':num`]);
  FIRST_X_ASSUM (MP_TAC o SPECL [`i + dimindex (:N)`;`i' + dimindex (:N)`])] THEN
  ASM_SIMP_TAC[lem2;GSYM (ARITH_RULE `(x:num) - n <= n <=> x <= (n + n)`);DIMINDEX_FINITE_SUM;ARITH_RULE `1 <= i ==> 1 <= i + dimindex(:N)`;GSYM (ARITH_RULE `(x:num) <= 0 <=> x + n <= n`);ARITH_RULE `1 <= i ==> ~(i <= 0)`;ARITH_RULE `n + 1 <= i + n <=> 1 <= i`;ARITH_RULE `((a:num) + n) - n = a`];
  SIMP_TAC[]]);;
  
(* ------------------------------------------------------------------------- *)
(*Flattening Complex square matrix into real block matrix                        *)
(*Equivalent relationship between complex matrix and block matrix                        *)
(* ------------------------------------------------------------------------- *)

let cm2blockmatrix = new_definition
    `cm2blockmatrix (A:complex^N^N) =
    blockmatrix (Re_matrix A) (Im_matrix A) (--(Im_matrix A)) (Re_matrix A)`;;
    
let CMATRIX_EQ_ALT_BLOCK = prove
    (`!A B. A = B <=> cm2blockmatrix A = cm2blockmatrix B`,
    SIMP_TAC[CMATRIX_EQ_ALT;BLOCKMATRIX_UNIQUE;cm2blockmatrix;CMATRIX_ARITH `--(A:real^N^N) = --B <=> A = B`] THEN
    MESON_TAC[]);;
    
let CMATRIX_MUL_EQ_BLOCK_MUL = prove
    (`!A B C. A ** B = C <=> cm2blockmatrix A ** cm2blockmatrix B = cm2blockmatrix C`,
    SIMP_TAC[CMATRIX_MUL;cm2blockmatrix;BLOCKMATRIX_MUL] THEN
    SIMP_TAC[BLOCKMATRIX_UNIQUE;CMATRIX_EQ_ALT;RE_MATRIX;IM_MATRIX] THEN
    SIMP_TAC[MATRIX_MUL_LNEG;MATRIX_MUL_RNEG;CMATRIX_ARITH `--(A:real^N^N) + --B = --C <=> A + B = C`;CMATRIX_ARITH `--(A:real^N^N) + B = C <=> B - A = C`] THEN
    MESON_TAC[MATRIX_ADD_SYM;GSYM MATRIX_SUB]);;

    
(* ------------------------------------------------------------------------- *)
(* Ivertible complex Matrix Definition                                       *)
(* ------------------------------------------------------------------------- *)

let cinvertible = new_definition
  `cinvertible(A:complex^N^M) <=>
        ?A':complex^M^N. (A ** A' = cmat 1) /\ (A' ** A = cmat 1)`;;
    
(*usual inverse in the invertible case*)
    
let cmatrix_inv = new_definition 
    `(cmatrix_inv:complex^N^M->complex^M^N) A = @A'. (A ** A' = cmat 1) /\ (A' ** A = cmat 1)`;;

(*
let cmatrix_inv = new_definition
    `(cmatrix_inv:complex^N^M->complex^M^N) A = lambda i j. (@x. (!w. A ** w = cvector_zero  ==> x cdot w = Cx(&0)) /\
        (!z. (vector_to_cvector (basis j) - A ** x) cdot (A ** z) = Cx(&0)))$i`;;
*)

(* ------------------------------------------------------------------------- *)
(* Invertible complex matrices (not assumed square, but it's vacuous otherwise).     *)
(* ------------------------------------------------------------------------- *)

let CINVERTIBLE_I = prove
 (`cinvertible(cmat 1:complex^N^N)`,
  REWRITE_TAC[cinvertible] THEN MESON_TAC[CMATRIX_MUL_LID; CMATRIX_MUL_RID]);;

let CINVERTIBLE_NEG = prove
 (`!A:complex^N^M. cinvertible(--A) <=> cinvertible A`,
  REWRITE_TAC[cinvertible] THEN
  MESON_TAC[CMATRIX_MUL_LNEG; CMATRIX_MUL_RNEG; CMATRIX_NEG_NEG]);;

let CINVERTIBLE_CMUL = prove
 (`!A:complex^N^M c. cinvertible(c %%% A) <=> ~(c = Cx(&0)) /\ cinvertible(A)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = Cx(&0)` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[cinvertible; CMATRIX_MUL_LZERO; CMATRIX_CMUL_LZERO; CMAT_EQ] THEN SIMP_TAC[ARITH_EQ];ALL_TAC] THEN
  REWRITE_TAC[cinvertible; CMATRIX_MUL_LMUL; CMATRIX_MUL_RMUL] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `B:complex^M^N` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `c %%% B:complex^M^N`;
    EXISTS_TAC `inv c %%% B:complex^M^N`] THEN
  ASM_REWRITE_TAC[CMATRIX_MUL_LMUL; CMATRIX_MUL_RMUL] THEN
  ASM_SIMP_TAC[CMATRIX_CMUL_ASSOC; COMPLEX_MUL_RINV; CMATRIX_CMUL_LID]);;

let CINVERTIBLE_MAT = prove
 (`!a. cinvertible(cmat a:complex^N^N) <=> ~(a = 0)`,
  ONCE_REWRITE_TAC[CMAT_CMUL] THEN
  REWRITE_TAC[CINVERTIBLE_CMUL; CINVERTIBLE_I; REAL_OF_NUM_EQ;CX_INJ]);;

let CMATRIX_ENTIRE = prove
 (`(!A:complex^N^M B:complex^P^N. cinvertible A ==> (A ** B = cmat 0 <=> B = cmat 0)) /\
   (!A:complex^N^M B:complex^P^N. cinvertible B ==> (A ** B = cmat 0 <=> A = cmat 0))`,
  REWRITE_TAC[cinvertible] THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `A':complex^M^N` STRIP_ASSUME_TAC);
    DISCH_THEN(X_CHOOSE_THEN `B':complex^N^P` STRIP_ASSUME_TAC)] THEN
  EQ_TAC THEN SIMP_TAC[CMATRIX_MUL_LZERO; CMATRIX_MUL_RZERO] THENL
   [DISCH_THEN(MP_TAC o AP_TERM `(**) A':complex^P^M->complex^P^N`) THEN
    ASM_REWRITE_TAC[CMATRIX_MUL_ASSOC; CMATRIX_MUL_LID; CMATRIX_MUL_RZERO];
    DISCH_THEN(MP_TAC o AP_TERM `\C:complex^P^M. C ** (B':complex^N^P)`) THEN
    ASM_REWRITE_TAC[GSYM CMATRIX_MUL_ASSOC; CMATRIX_MUL_RID;
                    CMATRIX_MUL_LZERO]]);;

let LEFT_CINVERTIBLE_TRANSP = prove
 (`!A:complex^N^M.
    (?B:complex^N^M. B ** ctransp A = cmat 1) <=> (?B:complex^M^N. A ** B = cmat 1)`,
  MESON_TAC[CMATRIX_TRANSP_MUL; TRANSP_CMAT; CTRANSP_CTRANSP]);;

let RIGHT_CINVERTIBLE_TRANSP = prove
 (`!A:complex^N^M.
    (?B:complex^N^M. ctransp A ** B = cmat 1) <=> (?B:complex^M^N. B ** A = cmat 1)`,
  MESON_TAC[CMATRIX_TRANSP_MUL; TRANSP_CMAT; CTRANSP_CTRANSP]);;

let CINVERTIBLE_TRANSP = prove
 (`!A:complex^N^M. cinvertible(ctransp A) <=> cinvertible A`,
  GEN_TAC THEN REWRITE_TAC[cinvertible] THEN
  GEN_REWRITE_TAC LAND_CONV [MESON[CTRANSP_CTRANSP]
    `(?A:complex^M^N. P A) <=> (?A:complex^N^M. P(ctransp A))`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM TRANSP_CMAT] THEN
  REWRITE_TAC[GSYM CMATRIX_TRANSP_MUL; CTRANSP_EQ] THEN MESON_TAC[]);;

let CVECTOR_ZERO_EQ_MAT_0 = prove
    (`cvector_zero:complex^N = mat 0`,
    CMATRIX_ARITH_TAC);;
    
let CVECTOR_NEG_EQ_MATRIX_NEG = prove
    (`!x. cvector_neg x = matrix_neg x`,
    SIMP_TAC[CART_EQ;LAMBDA_BETA;CVECTOR_NEG_COMPONENT;MATRIX_NEG_COMPONENT;VECTOR_NEG_COMPONENT]);;
    
let CVECTOR_ADD_EQ_MATRIX_ADD = prove
    (`!x y. cvector_add x y = matrix_add x y`,
    SIMP_TAC[CART_EQ;LAMBDA_BETA;CVECTOR_ADD_COMPONENT;MATRIX_ADD_COMPONENT;VECTOR_ADD_COMPONENT]);;
    
let CVECTOR_SUB_EQ_MATRIX_SUB = prove
    (`!x y. cvector_sub x y = matrix_sub x y`,
    SIMP_TAC[CART_EQ;LAMBDA_BETA;CVECTOR_SUB_COMPONENT;MATRIX_SUB_COMPONENT;VECTOR_SUB_COMPONENT]);;
    
let CVECTOR_MUL_EQ_MATRIX_CMUL = prove
    (`!c x. cvector_mul c x = matrix_add ((Re c) %% x) ((Im c) %% (complex_vector(cvector_im (--x), cvector_re x)))`,
    SIMP_TAC[COMPLEX_VECTOR_TRANSPOSE;CVECTOR_ADD_EQ_MATRIX_ADD;MATRIX_CMUL_ADD_LDISTRIB] THEN
    SIMP_TAC[CART_EQ;LAMBDA_BETA;CVECTOR_MUL_COMPONENT;MATRIX_CMUL_COMPONENT;complex_mul;complex;VECTOR_2;DIMINDEX_2;FORALL_2;MATRIX_ADD_COMPONENT;RE_DEF;IM_DEF;VECTOR_TO_CVECTOR_COMPONENT;CVECTOR_RE_COMPONENT;CVECTOR_IM_COMPONENT;CVECTOR_NEG_COMPONENT;CX_DEF;ii;VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC);;
    
(* ------------------------------------------------------------------------- *)
(* The same result in terms of complex square matrices.                              *)
(* ------------------------------------------------------------------------- *)

let CMATRIX_LEFT_RIGHT_INVERSE = prove
 (`!A:complex^N^N A':complex^N^N. (A ** A' = cmat 1) <=> (A' ** A = cmat 1)`,
  SUBGOAL_THEN
    `!A:complex^N^N A':complex^N^N. (A ** A' = cmat 1) ==> (A' ** A = cmat 1)`
    (fun th -> MESON_TAC[th]) THEN
  SIMP_TAC[CMATRIX_MUL;CMAT;CMATRIX_EQ_ALT;RE_MATRIX;RE_MATRIX_CX_MATRIX;IM_MATRIX;IM_MATRIX_CX_MATRIX;FORALL_CMATRIX] THEN
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  (MP_TAC (ISPECL [`blockmatrix (x:real^N^N) y (--y) x`;`blockmatrix (x':real^N^N) y' (--y') x'`] MATRIX_LEFT_RIGHT_INVERSE)) THEN
  SIMP_TAC[BLOCKMATRIX_MUL;MATRIX_MUL_LNEG;MATRIX_MUL_RNEG;MATRIX_NEG_NEG] THEN
  SIMP_TAC[GSYM BLOCKMATRIX_EQ_MAT;BLOCKMATRIX_UNIQUE] THEN
  SIMP_TAC[CMATRIX_ARITH `--x + y = y - x:real^N^N /\ --x + --y = --(x + y):real^N^N`] THEN
  ASM_SIMP_TAC[GSYM MATRIX_SUB;MATRIX_ADD_SYM;MATRIX_NEG_0;MATRIX_NEG_0]);;
                    
let CINVERTIBLE_LEFT_INVERSE = prove
 (`!A:complex^N^N. cinvertible(A) <=> ?B:complex^N^N. B ** A = cmat 1`,
  MESON_TAC[cinvertible; CMATRIX_LEFT_RIGHT_INVERSE]);;

let CINVERTIBLE_RIGHT_INVERSE = prove
 (`!A:complex^N^N. cinvertible(A) <=> ?B:complex^N^N. A ** B = cmat 1`,
  MESON_TAC[cinvertible; CMATRIX_LEFT_RIGHT_INVERSE]);; 

let CMATRIX_INV = prove
 (`!A:complex^N^M.
    cinvertible A ==> A ** cmatrix_inv A = cmat 1 /\ cmatrix_inv A ** A = cmat 1`,
  GEN_TAC THEN REWRITE_TAC[cinvertible] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:complex^M^N` STRIP_ASSUME_TAC) THEN
  SIMP_TAC[cmatrix_inv] THEN SELECT_ELIM_TAC THEN
  ASM_MESON_TAC[]);;
  
let CMATRIX_MUL_LCANCEL = prove
 (`!A:complex^M^N B:complex^P^M C.
        cinvertible A ==> (A ** B = A ** C <=> B = C)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMATRIX_INV) THEN
  EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM
   `cmatrix_mul (cmatrix_inv(A:complex^M^N)):complex^P^N->complex^P^M`) THEN
  ASM_SIMP_TAC[CMATRIX_MUL_ASSOC; CMATRIX_MUL_LID]);;

let CMATRIX_MUL_RCANCEL = prove
 (`!A B:complex^M^N C:complex^P^M.
        cinvertible C ==> (A ** C = B ** C <=> A = B)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMATRIX_INV) THEN
  EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\A:complex^P^N. A ** cmatrix_inv(C:complex^P^M)`) THEN
  ASM_SIMP_TAC[GSYM CMATRIX_MUL_ASSOC; CMATRIX_MUL_RID]);;
  
let CMATRIX_INV_UNIQUE = prove
 (`!A:complex^N^M B. A ** B = cmat 1 /\ B ** A = cmat 1 ==> cmatrix_inv A = B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cinvertible (A:complex^N^M)` ASSUME_TAC THENL
  [ASM_MESON_TAC[cinvertible];ALL_TAC] THEN
  MP_TAC(ISPECL [`cmatrix_inv (A:complex^N^M)`;`B:complex^M^N `;`A:complex^N^M `] CMATRIX_MUL_RCANCEL) THEN
  ASM_SIMP_TAC[CMATRIX_INV]);;

let CMATRIX_INV_I = prove
 (`cmatrix_inv(cmat 1:complex^N^N) = cmat 1`,
  MATCH_MP_TAC CMATRIX_INV_UNIQUE THEN
  REWRITE_TAC[CMATRIX_MUL_LID]);;    
  
let CMATRIX_INV_INV = prove
    (`!A:complex^M^N. 
    cinvertible A ==> cmatrix_inv (cmatrix_inv A) = A`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CMATRIX_INV_UNIQUE THEN
    ASM_SIMP_TAC[CMATRIX_INV]);;

let CINVERTIBLE_MATRIX_INV_IMP = prove
    (`!A:complex^M^N. cinvertible A ==> cinvertible(cmatrix_inv A)`,
    REPEAT STRIP_TAC THEN SIMP_TAC[cinvertible] THEN
    EXISTS_TAC `(A:complex^M^N)` THEN ASM_MESON_TAC[CMATRIX_INV]);;

let CMATRIX_INV_CTRANSP = prove
 (`!A:complex^M^N. cinvertible A ==> cmatrix_inv (ctransp A) = ctransp(cmatrix_inv A)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMATRIX_INV_UNIQUE THEN
  ASM_SIMP_TAC[GSYM CMATRIX_TRANSP_MUL;CMATRIX_INV;TRANSP_CMAT]);;

let CTRANSP_CMATRIX_INV = prove
 (`!A:complex^M^N. cinvertible A ==> ctransp(cmatrix_inv A) = cmatrix_inv(ctransp A)`,
  SIMP_TAC[CMATRIX_INV_CTRANSP]);;    
    
let CMATRIX_INV_CMUL = prove
    (`!c A:complex^M^N. cinvertible(c %%% A) ==> cmatrix_inv (c %%% A) = inv(c) %%% cmatrix_inv A`, 
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CMATRIX_INV_UNIQUE THEN
    SIMP_TAC[CMATRIX_MUL_LMUL;CMATRIX_MUL_RMUL;CMATRIX_CMUL_ASSOC] THEN
    POP_ASSUM MP_TAC THEN
    SIMP_TAC[CINVERTIBLE_CMUL;CMATRIX_INV;COMPLEX_MUL_LINV;COMPLEX_MUL_RINV;GSYM CMAT_CMUL]);;
    
let CMATRIX_INV_LEFT = prove
 (`!A:complex^N^N. cmatrix_inv A ** A = cmat 1 <=> cinvertible A`,
  MESON_TAC[CINVERTIBLE_LEFT_INVERSE; CMATRIX_INV]);;

let CMATRIX_INV_RIGHT = prove
 (`!A:complex^N^N. A ** cmatrix_inv A = cmat 1 <=> cinvertible A`,
  MESON_TAC[CINVERTIBLE_RIGHT_INVERSE; CMATRIX_INV]);;
    
let CINVERTIBLE_MATRIX_MUL = prove
 (`!A:complex^N^N B:complex^N^N.
        cinvertible(A ** B) <=> cinvertible A /\ cinvertible B`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [REPEAT STRIP_TAC THENL 
   [SIMP_TAC[CINVERTIBLE_RIGHT_INVERSE];
    SIMP_TAC[CINVERTIBLE_LEFT_INVERSE]] THEN
   POP_ASSUM MP_TAC THEN
   MESON_TAC[CMATRIX_MUL_ASSOC;cinvertible];ALL_TAC] THEN
  REPEAT STRIP_TAC THEN SIMP_TAC[CINVERTIBLE_RIGHT_INVERSE] THEN
  EXISTS_TAC `(cmatrix_inv (B:complex^N^N)) ** (cmatrix_inv (A:complex^N^N))` THEN
  SIMP_TAC[CMATRIX_MUL_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [GSYM CMATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[CMATRIX_INV;CMATRIX_MUL_RID]);;
  
let CMATRIX_INV_MUL = prove
 (`!A:complex^N^N B:complex^N^N.
        cinvertible A /\ cinvertible B
        ==> cmatrix_inv(A ** B) = cmatrix_inv B ** cmatrix_inv A`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMATRIX_INV_UNIQUE THEN
  ONCE_REWRITE_TAC[CMATRIX_MUL_ASSOC] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o LAND_CONV)
   [GSYM CMATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[CMATRIX_INV;CMATRIX_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* The definition and properties of power of matrix (real and complex)                          *)
(* ------------------------------------------------------------------------- *)

make_overloadable "matrix_pow" `:A^N^N->num->A^N^N`;;

overload_interface("matrix_pow",`real_matrix_pow:real^N^N->num->real^N^N`);;
overload_interface("matrix_pow",`complex_matrix_pow:complex^N^N->num->complex^N^N`);;

let real_matrix_pow = define
    `((real_matrix_pow: real^N^N->num->real^N^N) A 0 = (mat 1:real^N^N)) /\ (real_matrix_pow A (SUC n) = A ** (real_matrix_pow A n))`;;
    
let complex_matrix_pow = define
    `((complex_matrix_pow: complex^N^N->num->complex^N^N) A 0 = (cmat 1:complex^N^N)) /\ (complex_matrix_pow A (SUC n) = A ** (complex_matrix_pow A n))`;;
    
let matrix_pow = prove
    (`(!A. (real_matrix_pow A 0 = (mat 1:real^N^N)) /\ (real_matrix_pow A (SUC n) = A ** (real_matrix_pow A n))) /\
    (!A. (complex_matrix_pow A 0 = (cmat 1:complex^N^N)) /\ (complex_matrix_pow A (SUC n) = A ** (complex_matrix_pow A n)))`,
    SIMP_TAC[real_matrix_pow;complex_matrix_pow]);;
    
parse_as_infix("matrix_pow",(200,"right"));;

(* properties of real matrix pow *)

let MATRIX_POW_1 = prove
    (`!A:real^N^N. A matrix_pow 1 = A`,
     REWRITE_TAC[num_CONV `1`] THEN SIMP_TAC[matrix_pow;MATRIX_MUL_RID]);;

let MATRIX_POW_2 =  prove
    (`!A:real^N^N. A matrix_pow 2 = A ** A`,
    SIMP_TAC[matrix_pow;num_CONV `2`;MATRIX_POW_1]);;
    
let MATRIX_POW_3 =  prove
    (`!A:real^N^N. A matrix_pow 3 = A ** A ** A`,
    SIMP_TAC[matrix_pow;num_CONV `3`;num_CONV `2`;MATRIX_POW_1]);;
     
let MATRIX_POW_0 = prove
    (`!n. (mat 0:real^N^N) matrix_pow SUC n = (mat 0:real^N^N)`,
     SIMP_TAC[matrix_pow;MATRIX_MUL_LZERO]);;

let MATRIX_POW_ONE = prove
    (`!n. (mat 1:real^N^N) matrix_pow n = (mat 1:real^N^N)`,
     INDUCT_TAC THEN ASM_SIMP_TAC [matrix_pow;MATRIX_MUL_LID]);;
    
let MATRIX_POW_ADD = prove
    (`!A:real^N^N m n. A matrix_pow (m + n) = (A matrix_pow m) ** (A matrix_pow n)`,
     GEN_TAC THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC[matrix_pow; ADD_CLAUSES; MATRIX_MUL_LID] THEN REWRITE_TAC[MATRIX_MUL_ASSOC]);; 
     
let MATRIX_POW_CMUL = prove
    (`!k:real A:real^N^N n:num. (k %% A) matrix_pow n = (k pow n) %% (A matrix_pow n)`,
     GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
     [SIMP_TAC [matrix_pow; real_pow; GSYM MAT_CMUL;ARITH];
      SIMP_TAC [matrix_pow;real_pow] THEN
      ASM_SIMP_TAC [MATRIX_MUL_LMUL;MATRIX_MUL_RMUL;MATRIX_CMUL_ASSOC]]);;
      
let MATRIX_POW_TRANSP = prove  
    (`!A:real^N^N n:num. (transp A) matrix_pow n  = transp(A matrix_pow n)`,
    let MATRIX_POW_SUC = prove
    ( `!A:real^N^N n:num.A matrix_pow n ** A = A ** A matrix_pow n`,
    GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[matrix_pow;MATRIX_MUL_RID;MATRIX_MUL_LID]
    THEN SIMP_TAC[matrix_pow] THEN FIRST_ASSUM (SUBST1_TAC o SYM) THEN 
    SIMP_TAC[MATRIX_MUL_ASSOC] THEN FIRST_ASSUM (SUBST1_TAC o SYM) 
    THEN SIMP_TAC[])  in
    GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[matrix_pow;TRANSP_MAT] THEN
    ASM_SIMP_TAC[matrix_pow;GSYM MATRIX_TRANSP_MUL;MATRIX_POW_SUC]);;

(* same properties of complex matrix pow *)

let CMATRIX_POW_1 = prove
    (`!A:complex^N^N. A matrix_pow 1 = A`,
     REWRITE_TAC[num_CONV `1`] THEN SIMP_TAC[matrix_pow;CMATRIX_MUL_RID]);;
     
let CMATRIX_POW_2 =  prove
    (`!A:complex^N^N. A matrix_pow 2 = A ** A`,
    SIMP_TAC[matrix_pow;num_CONV `2`;CMATRIX_POW_1]);;
    
let CMATRIX_POW_3 =  prove
    (`!A:complex^N^N. A matrix_pow 3 = A ** A ** A`,
    SIMP_TAC[matrix_pow;num_CONV `3`;num_CONV `2`;CMATRIX_POW_1]);;
    
let CMATRIX_POW_0 = prove
    (`!n. (cmat 0:complex^N^N) matrix_pow SUC n = (cmat 0:complex^N^N)`,
     SIMP_TAC[matrix_pow;CMATRIX_MUL_LZERO]);;

let CMATRIX_POW_ONE = prove
    (`!n. (cmat 1:complex^N^N) matrix_pow n = (cmat 1:complex^N^N)`,
     INDUCT_TAC THEN ASM_SIMP_TAC [matrix_pow;CMATRIX_MUL_LID]);;
    
let CMATRIX_POW_ADD = prove
    (`!A:complex^N^N m n. A matrix_pow (m + n) = (A matrix_pow m) ** (A matrix_pow n)`,
     GEN_TAC THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC[matrix_pow; ADD_CLAUSES; CMATRIX_MUL_LID] THEN REWRITE_TAC[CMATRIX_MUL_ASSOC]);; 
     
let CMATRIX_POW_CMUL = prove
    (`!k:complex A:complex^N^N n:num. (k %%% A) matrix_pow n = (k pow n) %%% (A matrix_pow n)`,
     GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
     [SIMP_TAC [matrix_pow; complex_pow; GSYM CMAT_CMUL;ARITH];
      SIMP_TAC [matrix_pow;complex_pow] THEN
      ASM_SIMP_TAC [CMATRIX_MUL_LMUL;CMATRIX_MUL_RMUL;CMATRIX_CMUL_ASSOC]]);;
      
let CMATRIX_POW_TRANSP = prove  
    (`!A:complex^N^N n:num. (ctransp A) matrix_pow n  = ctransp(A matrix_pow n)`,
    let CMATRIX_POW_SUC = prove
    ( `!A:complex^N^N n:num.A matrix_pow n ** A = A ** A matrix_pow n`,
    GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[matrix_pow;CMATRIX_MUL_RID;CMATRIX_MUL_LID]
    THEN SIMP_TAC[matrix_pow] THEN FIRST_ASSUM (SUBST1_TAC o SYM) THEN 
    SIMP_TAC[CMATRIX_MUL_ASSOC] THEN FIRST_ASSUM (SUBST1_TAC o SYM) 
    THEN SIMP_TAC[])  in
    GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[matrix_pow;TRANSP_CMAT] THEN
    ASM_SIMP_TAC[matrix_pow;GSYM CMATRIX_TRANSP_MUL;CMATRIX_POW_SUC]);;

(* ------------------------------------------------------------------------- *)
(* The properties of multiple summation                                      *)
(* ------------------------------------------------------------------------- *)

let SUM_SUM_LE = prove
 (`!f g s1:A->bool s2:B->bool.
        FINITE(s1) /\ FINITE(s2) /\ (!x y. x IN s1 /\ y IN s2 ==> f x y <= g x y)
         ==> sum s2 (\y. sum s1 (\x. f x y)) <= sum s2 (\y. sum s1 (\x. g x y))`,
  MESON_TAC [SUM_LE]);;
   
let SUM_SUM_DELTA = prove
    (`!s1 s2 a1 a2. sum s1 (\x1. if x1 = a1:A then (sum s2 (\x2. if x2 = a2:A then b else &0)) else &0) 
    = if ((a1 IN s1) /\ (a2 IN s2)) then b else &0`,
    SIMP_TAC [SUM_DELTA] THEN METIS_TAC []);;
  
let SUM_SUM_BOUND_LT_ALL = prove
    (`!s1:A->bool s2:B->bool f b. FINITE s1 /\ ~(s1 = {}) /\ FINITE s2 /\ ~(s2 = {})
              /\ (!x y. x IN s1 /\ y IN s2 ==> f x y < b)
           ==> sum s2 (\y. sum s1 (\x. f x y)) < &(CARD s1) * &(CARD s2) * b`,
    MESON_TAC [SUM_BOUND_LT_ALL;REAL_ARITH `!a b c:real.a * b * c = b * a * c`]);;    
  
let SUM_SUM_BOUND_LT_GEN = prove
    (`!s1:A->bool s2:B->bool f b. FINITE s1 /\ ~(s1 = {}) /\ FINITE s2 /\ ~(s2 = {})
           /\ (!x y. x IN s1 /\ y IN s2 ==> f x y < b / (&(CARD s1) * &(CARD s2)))
           ==> sum s2 (\y. sum s1 (\x. f x y)) < b`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN 
       `b = &(CARD (s1:A->bool)) * &(CARD (s2:B->bool)) *
        (b / (&(CARD s1) * &(CARD s2)))`
    ASSUME_TAC THENL
    [REWRITE_TAC [REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
     MATCH_MP_TAC REAL_DIV_LMUL THEN 
     UNDISCH_TAC `~(s2:B->bool = {})` THEN
     UNDISCH_TAC `~(s1:A->bool = {})` THEN 
     REWRITE_TAC[GSYM IMP_CONJ] THEN CONV_TAC CONTRAPOS_CONV THEN
     ASM_SIMP_TAC[DE_MORGAN_THM; GSYM HAS_SIZE_0; HAS_SIZE; 
                 GSYM REAL_OF_NUM_EQ; REAL_ENTIRE]; ALL_TAC] THEN 
    ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_SUM_BOUND_LT_ALL THEN ASM_SIMP_TAC[]);;

(*****************lift from R to R^1^1***************************)

let lift_lift = new_definition
 `(lift_lift:real->real^1^1) x = lambda i j. x`;;
 
let drop_drop = new_definition
 `(drop_drop:real^1^1->real) x = x$1$1`;;
 
let LIFT2_COMPONENT = prove
 (`!x. (lift_lift x)$1$1 = x`,
  SIMP_TAC[lift_lift; LAMBDA_BETA; DIMINDEX_1; LE_ANTISYM]);; 

let LIFT2_DROP = prove
 (`(!x. lift_lift(drop_drop x) = x) /\ (!x. drop_drop(lift_lift x) = x)`,
  SIMP_TAC[lift_lift; drop_drop; CART_EQ; LAMBDA_BETA; DIMINDEX_1; LE_ANTISYM]);;
  
let LIFT2_NUM = prove
 (`!n. lift_lift(&n) = mat n`,
  SIMP_TAC[FORALL_1; SUM_1; DIMINDEX_1; ARITH;
           CART_EQ; lift_lift; mat; LAMBDA_BETA]);;
           
let LIFT2_EQ = prove
 (`!x y. (lift_lift x = lift_lift y) <=> (x = y)`,
  MESON_TAC[LIFT2_DROP]);;

let DROP2_EQ = prove
 (`!x y. (drop_drop x = drop_drop y) <=> (x = y)`,
  MESON_TAC[LIFT2_DROP]);;
  
let FORALL_LIFT2 = prove
 (`(!x. P x) = (!x. P(lift_lift x))`,
  MESON_TAC[LIFT2_DROP]);;

let EXISTS_LIFT2 = prove
 (`(?x. P x) = (?x. P(lift_lift x))`,
  MESON_TAC[LIFT2_DROP]);;
  
let FORALL_DROP2 = prove
 (`(!x. P x) = (!x. P(drop_drop x))`,
  MESON_TAC[LIFT2_DROP]);;

let EXISTS_DROP2 = prove
 (`(?x. P x) = (?x. P(drop_drop x))`,
  MESON_TAC[LIFT2_DROP]);;
  
let LIFT2_IN_IMAGE_LIFT2 = prove
 (`!x s. (lift_lift x) IN (IMAGE lift_lift s) <=> x IN s`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[LIFT2_DROP]);;
  
let DROP2_MAT = prove
 (`!n. drop_drop (mat n) = &n`,
  GEN_TAC THEN REWRITE_TAC[drop_drop] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `&n =if 1 = 1 then &n else &0`] THEN
  MATCH_MP_TAC MAT_COMPONENT THEN
  SIMP_TAC [ARITH; DIMINDEX_1]);;
  
let LIFT2_ADD = prove
 (`!x y. lift_lift(x + y) = lift_lift x + lift_lift y`,
  SIMP_TAC[CART_EQ; lift_lift; LAMBDA_BETA; MATRIX_ADD_COMPONENT]);;

let LIFT2_SUB = prove
 (`!x y. lift_lift(x - y) = lift_lift x - lift_lift y`,
  SIMP_TAC[CART_EQ; lift_lift; LAMBDA_BETA; MATRIX_SUB_COMPONENT]);;

let LIFT2_CMUL = prove
 (`!x c. lift_lift(c * x) = c %% lift_lift(x)`,
  SIMP_TAC[CART_EQ; lift_lift; LAMBDA_BETA; MATRIX_CMUL_COMPONENT]);;

let LIFT2_NEG = prove
 (`!x. lift_lift(--x) = --(lift_lift x)`,
  SIMP_TAC[CART_EQ; lift_lift; LAMBDA_BETA; MATRIX_NEG_COMPONENT]);;
  
let DROP2_ADD = prove
 (`!x y. drop_drop(x + y) = drop_drop x + drop_drop y`,
  MESON_TAC[LIFT2_DROP; LIFT2_ADD]);;

let DROP2_SUB = prove
 (`!x y. drop_drop(x - y) = drop_drop x - drop_drop y`,
  MESON_TAC[LIFT2_DROP; LIFT2_SUB]);;

let DROP2_CMUL = prove
 (`!x c. drop_drop(c %% x) = c * drop_drop(x)`,
  MESON_TAC[LIFT2_DROP; LIFT2_CMUL]);;

let DROP2_NEG = prove
 (`!x. drop_drop(--x) = --(drop_drop x)`,
  MESON_TAC[LIFT2_DROP; LIFT2_NEG]);;
  
let DROP2_SET = prove
 (`!x:real^1^1 s. x IN s <=> (drop_drop x) IN {drop_drop x | x IN s}`,
   SET_TAC [DROP2_EQ]);;
   
(*let DROP2_UNIV = prove
 (`!x:real^1^1. x IN (:real^1^1) <=> drop_drop x IN (:real)`,
  SET_TAC [DROP2_EQ]);;*)
  
let DROP2_UNIV = prove
 (`!x:real^1^1. {drop_drop x | x IN (:real^1^1)} = (:real)`,
  SIMP_TAC [EXTENSION] THEN 
  ONCE_REWRITE_TAC [FORALL_DROP2] THEN 
  SET_TAC [DROP2_EQ; FORALL_DROP2]);;  
    
(* ------------------------------------------------------------------------- *)
(* The definition and properties of finite sum of matrix                     *)
(* ------------------------------------------------------------------------- *)  

make_overloadable "msum" `:(A->bool)->(A->B)->B`;;

overload_interface("msum",`real_msum:(A->bool)->(A->real^N^M)->real^N^M`);;
overload_interface("msum",`complex_msum:(A->bool)->(A->complex^N^M)->complex^N^M`);;

let real_msum = new_definition
    `(real_msum:(A->bool)->(A->real^N^M)->real^N^M) s f = lambda i j. sum s (\x. f(x)$i$j)`;;
    
let complex_msum = new_definition
    `(complex_msum:(A->bool)->(A->complex^N^M)->complex^N^M) s f = lambda i j. vsum s (\x. f(x)$i$j)`;;
    
let msum = prove
    (`(!s f. real_msum s f = lambda i j. sum s (\x. f(x)$i$j)) /\
    (!s f. complex_msum s f = lambda i j. vsum s (\x. f(x)$i$j))`,
    SIMP_TAC[real_msum;complex_msum]);;
    
(* properties of finite sum of real matrix *)
  
let MSUM_CLAUSES = prove
    (`(!f. msum {} f = mat 0) /\
        (!x f:A->real^N^M s. FINITE s
            ==> (msum (x INSERT s) f =
                 if x IN s then msum s f else f(x) + msum s f))`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT; SUM_CLAUSES] THEN
    SIMP_TAC[MAT_COMPONENT] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA; MATRIX_ADD_COMPONENT]);; 
  
let MSUM_EQ_0 = prove
    (`!f s. (!x:A. x IN s ==> (f(x) = mat 0)) ==> (msum s f = mat 0)`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; mat] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN SIMP_TAC[SUM_EQ_0]);;
  
let MSUM_0 = prove
    (`msum s (\x. mat 0) = mat 0`,
    SIMP_TAC[MSUM_EQ_0]);;
  
let MSUM_LMUL = prove
    (`!f c s.  msum s (\x. c %% f(x)) = c %% msum s f`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MATRIX_CMUL_COMPONENT; SUM_LMUL]);;
  
let MSUM_RMUL = prove
    (`!c s v. msum s (\x. c x %% v) = (sum s c) %% v`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MATRIX_CMUL_COMPONENT; SUM_RMUL]);;

let MSUM_ADD = prove
    (`!f:A->real^N^M g s. FINITE s ==> (msum s (\x. f x + g x) = msum s f + msum s g)`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT; SUM_ADD]);;

let MSUM_SUB = prove
    (`!f:A->real^N^M g s. FINITE s ==> (msum s (\x. f x - g x) = msum s f - msum s g)`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MATRIX_SUB_COMPONENT; SUM_SUB]);;

let MSUM_CONST = prove
    (`!c s. FINITE s ==> (msum s (\n. c) = &(CARD s) %% c)`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; SUM_CONST; MATRIX_CMUL_COMPONENT]);;

let MSUM_COMPONENT = prove
    (`!s f i j. 1 <= i /\ i <= dimindex(:M) /\
                1 <= j /\ j <= dimindex(:N)
            ==> ((msum s (f:A->real^N^M))$i$j = sum s (\x. f(x)$i$j))`,
    SIMP_TAC[msum; LAMBDA_BETA]);;

let MSUM_UNION = prove
    (`!f:A->real^N^M s t. FINITE s /\ FINITE t /\ DISJOINT s t
            ==> (msum (s UNION t) f = msum s f + msum t f)`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; SUM_UNION; MATRIX_ADD_COMPONENT]);;
    
let MSUM_DIFF = prove
 (`!f:A->real^N^M s t. FINITE s /\ t SUBSET s
           ==> (msum (s DIFF t) f = msum s f - msum t f)`,
  SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; SUM_DIFF; MATRIX_SUB_COMPONENT]);;

let MSUM_DELETE = prove
    (`!f:A->real^N^M s a. FINITE s /\ a IN s
            ==> msum (s DELETE a) f = msum s f - f a`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; SUM_DELETE; MATRIX_SUB_COMPONENT]);;

let MSUM_NEG = prove
    (`!f:A->real^N^M s. msum s (\x. --f x) = --msum s f`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; SUM_NEG; MATRIX_NEG_COMPONENT]);;

let MSUM_EQ = prove
    (`!f:A->real^N^M g s. (!x. x IN s ==> (f x = g x)) ==> (msum s f = msum s g)`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]);;

let MSUM_SUPERSET = prove
    (`!f:A->real^N^M u v.
            u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = mat 0))
            ==> (msum v f = msum u f)`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MAT_COMPONENT] THEN
    ASM_SIMP_TAC[ARITH_RULE `(if k then &0 else &0) = &0`;SUM_SUPERSET]);;

let MSUM_EQ_SUPERSET = prove
    (`!f:A->real^N^M s t:A->bool.
            FINITE t /\ t SUBSET s /\
            (!x. x IN t ==> (f x = g x)) /\
            (!x. x IN s /\ ~(x IN t) ==> f(x) = mat 0)
            ==> msum s f = msum t g`,
    MESON_TAC[MSUM_SUPERSET; MSUM_EQ]);;

let MSUM_RESTRICT = prove
    (`!f s. msum s (\x. if x IN s then f(x) else mat 0) = msum s f`,
    REPEAT GEN_TAC THEN MATCH_MP_TAC MSUM_EQ THEN SIMP_TAC[]);;

let MSUM_CASES = prove
    (`!s P f g. FINITE s
                ==> msum s (\x:A. if P x then (f x):real^N^M else g x) =
                    msum {x | x IN s /\ P x} f + msum {x | x IN s /\ ~P x} g`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT; SUM_CASES;
             COND_COMPONENT]);;

let MSUM_SING = prove
    (`!f:A->real^N^M x. msum {x} f = f(x)`,
    SIMP_TAC[MSUM_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; MATRIX_ADD_RID]);;
  
let MSUM_CLAUSES_NUMSEG = prove
    (`!f:num->real^N^M. (!m. msum(m..0) f = if m = 0 then f(0) else mat 0) /\
    (!m n. msum(m..SUC n) f = if m <= SUC n then msum(m..n) f + f(SUC n)
                                else msum(m..n) f)`,
    REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[MSUM_SING; MSUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; MATRIX_ADD_AC]);;
  
let MSUM_OFFSET = prove
    (`!p f:num->real^N^M m n. msum(m + p..n + p) f = msum(m..n) (\i. f (i + p))`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MAT_COMPONENT; SUM_OFFSET]);;
    
let MSUM_PAIR = prove
    (`!f:num->real^N^M m n.
        msum(2*m..2*n+1) f = msum(m..n) (\i. f(2*i) + f(2*i+1))`,
    SIMP_TAC[CART_EQ; MSUM_COMPONENT; MATRIX_ADD_COMPONENT; SUM_PAIR]);;
    
let SUM_MSUM = prove
 (`!f s. sum s f = drop_drop (msum s (lift_lift o f))`,
  SIMP_TAC[msum; drop_drop; LAMBDA_BETA; DIMINDEX_1; ARITH] THEN
  REWRITE_TAC[o_THM; GSYM drop_drop; LIFT2_DROP; ETA_AX]);; 
    
let LIFT2_SUM = prove
 (`!k x. lift_lift(sum k x) = msum k (lift_lift o x)`,
  REWRITE_TAC[SUM_MSUM; LIFT2_DROP]);;
             
(* ------------------------------------------------------------------------- *)
(* The properties of trace of transp matrix                                  *)
(* ------------------------------------------------------------------------- *)  

let TRACE_TRANSP_POS_LE = prove
    (`!A:real^N^M. &0 <= trace(transp A ** A)`,
    GEN_TAC THEN SIMP_TAC[trace;transp;matrix_mul;CART_EQ;LAMBDA_BETA] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN SIMP_TAC[ETA_AX] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN SIMP_TAC[REAL_LE_SQUARE]);;

let TRACE_TRANSP_SYM = prove
    (`!A:real^N^M B:real^N^M. trace(transp A ** B) = trace(transp B ** A)`,
    METIS_TAC[TRACE_TRANSP; MATRIX_TRANSP_MUL; TRANSP_TRANSP]);;

(* ------------------------------------------------------------------------- *)
(* The definition and properties of the Frobenius norm of matrix             *)
(* ------------------------------------------------------------------------- *) 

make_overloadable "fnorm" `:A^N^M->real`;;

overload_interface("fnorm",`real_fnorm:real^N^M->real`);;
overload_interface("fnorm",`complex_fnorm:complex^N^M->real`);;

let real_fnorm = new_definition
    `real_fnorm A = sqrt(trace(transp A ** A))`;;
    
let complex_fnorm = new_definition
    `complex_fnorm (A:complex^N^M) = sqrt(sum (1..dimindex(:N)) (\i. norm((adjoint_matrix A ** A)$i$i)))`;;
    
let fnorm = prove
    (`(!A. real_fnorm A = sqrt(trace(transp A ** A))) /\
    (!A:complex^N^M. complex_fnorm A = sqrt(sum (1..dimindex(:N)) (\i. norm((adjoint_matrix A ** A)$i$i))))`,
    SIMP_TAC[real_fnorm;complex_fnorm]);;
    
let COMPLEX_FNORM = prove
    (`!A:complex^N^M. complex_fnorm A = real_fnorm((lambda i j. norm(A$i$j)):real^N^M)`,
    SIMP_TAC[fnorm;trace;SQRT_INJ] THEN
    GEN_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[cmatrix_mul;transp;cnj;adjoint_matrix;matrix_mul;LAMBDA_BETA;vector_norm;DOT_2;vsum;DIMINDEX_2;ARITH_RULE `1 <= 2`;LE_REFL;complex;VECTOR_2;RE_DEF;IM_DEF;complex_mul] THEN
    SIMP_TAC[REAL_SUB_RNEG;GSYM real_sub;REAL_MUL_LNEG] THEN
    SIMP_TAC[REAL_MUL_SYM;REAL_SUB_REFL;SUM_0;REAL_ADD_RID;REAL_MUL_LZERO] THEN
    SIMP_TAC[GSYM REAL_POW_2;GSYM SQRT_MUL;POW_2_SQRT_ABS;REAL_SQRT_POW_2] THEN
    SIMP_TAC[REAL_LE_POW_2;REAL_LE_ADD;REAL_ARITH `&0 <= x ==> abs x = x`;SUM_POS_LE]);;
    
(* properties of Frobenius norm of real matrix *)

let FNORM_REAL = prove
    (`!A:real^1^1. fnorm(A) = abs(A$1$1)`,
    SIMP_TAC[fnorm;trace;transp;matrix_mul;DIMINDEX_1;CART_EQ;LAMBDA_BETA;FORALL_1;SUM_1;ARITH; SUM_SING_NUMSEG;GSYM REAL_POW_2; POW_2_SQRT_ABS]);;

let FNORM_LE = prove
    (`!A:real^N^M B. (fnorm A <= fnorm B) <=> (trace(transp A ** A) <= trace(transp B ** B))`,
    REWRITE_TAC[fnorm] THEN MESON_TAC[SQRT_MONO_LE_EQ; TRACE_TRANSP_POS_LE]);;

let FNORM_LT = prove
    (`!A:real^N^M B. (fnorm A < fnorm B) <=> (trace(transp A ** A) < trace(transp B ** B))`,
    REWRITE_TAC[fnorm] THEN MESON_TAC[SQRT_MONO_LT_EQ; TRACE_TRANSP_POS_LE]);;
  
let FNORM_EQ = prove
    (`!A:real^N^M B. (fnorm A = fnorm B) <=> (trace(transp A ** A) = trace(transp B ** B))`,
    REWRITE_TAC[GSYM REAL_LE_ANTISYM; FNORM_LE]);;
  
let FNORM_0 = prove
    (`fnorm(mat 0) = &0`,
    REWRITE_TAC[fnorm; MATRIX_MUL_RZERO; TRACE_0;SQRT_0]);;      

let FNORM_EQ_0 = prove
    (`!A:real^N^M. fnorm A = &0 <=> A = mat 0`,
    GEN_TAC THEN SIMP_TAC[fnorm;SQRT_EQ_0] THEN
    EQ_TAC THENL
    [SIMP_TAC[trace;transp;matrix_mul;mat;CART_EQ;LAMBDA_BETA] THEN
     SIMP_TAC[ARITH_RULE `(if i = j then &0 else &0) = &0`] THEN
     DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
     ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[REAL_ENTIRE] `x * x = &0`)] THEN
     MATCH_MP_TAC SUM_POS_EQ_0_NUMSEG THEN ASM_REWRITE_TAC[REAL_LE_SQUARE] THEN
     UNDISCH_TAC `1 <= i /\ i <= dimindex (:M)` THEN SPEC_TAC (`i:num`,`i:num`) THEN
     MATCH_MP_TAC SUM_POS_EQ_0_NUMSEG THEN
     CONJ_TAC ; ALL_TAC] THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      ASM_REWRITE_TAC[REAL_LE_SQUARE] ; ALL_TAC ; ALL_TAC] THENL
      [ONCE_ASM_SIMP_TAC[GSYM SUM_SWAP_NUMSEG] THEN
       ONCE_ASM_SIMP_TAC[GSYM SUM_SWAP_NUMSEG] THEN
       ASM_SIMP_TAC[] ; ALL_TAC] THEN
       STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_MUL_RZERO;TRACE_0]);;
    
let FNORM_POS_LE = prove
    (`!A:real^N^M. &0 <= fnorm A`,
    GEN_TAC THEN SIMP_TAC[fnorm] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    SIMP_TAC[trace;transp;matrix_mul;CART_EQ;LAMBDA_BETA] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN SIMP_TAC[ETA_AX] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN SIMP_TAC[REAL_LE_SQUARE]);;

let FNORM_POS_LT = prove
    (`!A:real^N^M. &0 < fnorm A <=> ~(A = mat 0)`,
    MESON_TAC[REAL_LT_LE; FNORM_POS_LE; FNORM_EQ_0]);;
    
let FNORM_MUL = prove
 (`!a A:real^N^M. fnorm(a %% A) = abs(a) * fnorm A`,
  REWRITE_TAC[fnorm;TRANSP_MATRIX_CMUL;MATRIX_MUL_LMUL;
              MATRIX_MUL_RMUL;MATRIX_CMUL_ASSOC;TRACE_CMUL] THEN
  REWRITE_TAC[SQRT_MUL; GSYM REAL_POW_2; REAL_SQRT_POW_2]);;

let FNORM_POW_2 = prove
    (`!A:real^N^M. fnorm(A) pow 2 = trace(transp A ** A)`,
    SIMP_TAC[fnorm; SQRT_POW_2; TRACE_TRANSP_POS_LE]);;
    
let FNORM_NEG = prove
    (`!A:real^N^M. fnorm(--A) = fnorm A`,
    REWRITE_TAC[fnorm; TRANSP_MATRIX_NEG; MATRIX_MUL_LNEG; MATRIX_MUL_RNEG; MATRIX_NEG_NEG]);;  

let FNORM_SUB_SYM = prove
    (`!A:real^N^M B:real^N^M. fnorm(A - B) = fnorm(B - A)`,
    MESON_TAC[FNORM_NEG; MATRIX_NEG_SUB]);; 

let FNORM_EQ_0_IMP = prove
    (`!A:real^N^M. (fnorm A = &0) ==> (A = mat 0)`,
    MESON_TAC[FNORM_EQ_0]);;

let FNORM_CAUCHY_SCHWARZ = prove
    (`!A:real^N^M B:real^N^M. trace(transp A ** B) <= fnorm(A) * fnorm(B)`,
    REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC 
     [`fnorm(A:real^N^M) = &0`; `fnorm(B:real^N^M) = &0`] THEN
    ASM_SIMP_TAC[FNORM_EQ_0_IMP; MATRIX_MUL_LZERO; MATRIX_MUL_RZERO;TRANSP_MAT;
                 TRANSP_EQ_0; TRACE_0; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    MP_TAC(ISPEC `fnorm(A:real^N^M) %% B - fnorm(B:real^N^M) %% A`
           TRACE_TRANSP_POS_LE) THEN
    REWRITE_TAC[TRANSP_MATRIX_SUB;TRANSP_MATRIX_CMUL;
                MATRIX_SUB_LDISTRIB;MATRIX_SUB_RDISTRIB;TRACE_ADD;TRACE_SUB;
                TRACE_CMUL;MATRIX_MUL_LMUL;MATRIX_MUL_RMUL;MATRIX_CMUL_ASSOC] THEN
    SIMP_TAC[GSYM FNORM_POW_2;REAL_POW_2;REAL_LE_REFL] THEN
    REWRITE_TAC[TRACE_TRANSP_SYM; REAL_ARITH
     `&0 <= A * (A * B * B - B * t) - B * (A * t - B * A * A) <=>
      A * B * t <= A * B * A * B`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_LE; FNORM_POS_LE]);;

let FNORM_TRIANGLE = prove
    (`!A:real^N^M B:real^N^M. fnorm(A + B) <= fnorm(A) + fnorm(B)`,
    REPEAT GEN_TAC THEN REWRITE_TAC[fnorm] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN
    SIMP_TAC[GSYM fnorm; TRACE_TRANSP_POS_LE; FNORM_POS_LE; REAL_LE_ADD] THEN
    REWRITE_TAC[TRANSP_MATRIX_ADD;MATRIX_ADD_LDISTRIB;
                MATRIX_ADD_RDISTRIB;TRACE_ADD] THEN
    REWRITE_TAC[REAL_POW_2; GSYM FNORM_POW_2] THEN 
    SIMP_TAC[FNORM_CAUCHY_SCHWARZ; TRACE_TRANSP_SYM;REAL_ARITH
             `t <= A * B ==> (A * A + t) + (t + B * B) <= (A + B) * (A + B)`]);;

let FNORM_EQ_NORM_VECTORIZE = prove
    (`!A:real^N^M. fnorm A = norm(vectorize A)`,
    SIMP_TAC[fnorm;vector_norm;DOT_VECTORIZE]);;
             
let FNORM_SUBMULT = prove
    (`!A:real^N^P B:real^M^N. fnorm (A ** B) <= fnorm (A) * fnorm (B)`,
    SIMP_TAC[FNORM_EQ_NORM_VECTORIZE;NORM_VECTORIZE_MUL_LE]);;
    
let COMPATIBLE_FNORM = prove
    (`!A:real^N^M x. norm (A ** x) <= fnorm (A) * norm x`,
    SIMP_TAC[COMPATIBLE_NORM_VECTORIZE;FNORM_EQ_NORM_VECTORIZE]);;
    
let COMPONENT_LE_FNORM = prove
    (`!A:real^N^M i j. abs(A$i$j) <= fnorm A`,
    let sum_square = prove
    (`!s f:A->real. &0 <= sum s (\x. f(x) * f(x))`,
    METIS_TAC[SUM_POS_LE;REAL_LE_SQUARE]) in
    REPEAT GEN_TAC THEN SUBGOAL_THEN
    `?k1 k2. 1 <= k1 /\ k1 <= dimindex(:M) /\ 1 <= k2 /\ k2 <= dimindex(:N)
    /\ !x:real^N^M. x$i$j = x$k1$k2` STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[finite_index] THEN
     MESON_TAC[FINITE_INDEX_WORKS]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[fnorm] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[GSYM REAL_ABS_POW] THEN
    REWRITE_TAC[real_abs; REAL_POW_2; REAL_LE_SQUARE] THEN
    SIMP_TAC [trace;transp;matrix_mul;CART_EQ;LAMBDA_BETA] THEN
    SUBGOAL_THEN
    `A$k1$k2 * (A:real^N^M)$k1$k2 =
        sum(1..dimindex(:N)) (\i.
        if (i = k2)
        then (sum (1..dimindex (:M)) (\k. if k = k1 then A$k1$k2 * A$k1$k2 else &0))
        else &0)` SUBST1_TAC THENL
    [SIMP_TAC [SUM_SUM_DELTA] THEN ASM_SIMP_TAC[IN_NUMSEG]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE THEN SIMP_TAC [FINITE_NUMSEG;IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
    [ALL_TAC; SIMP_TAC[sum_square]] THEN
    MATCH_MP_TAC SUM_LE THEN SIMP_TAC[FINITE_NUMSEG;IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [REAL_LE_REFL; REAL_LE_SQUARE]);;
  
let VECTOR_COMPONENT_LE_FNORM = prove
    (`!A:real^N^M i. norm(A$i) <= fnorm A`,
    REPEAT GEN_TAC THEN SUBGOAL_THEN
    `?k. 1 <= k /\ k <= dimindex(:M) /\ !x:real^N^M. x$i = x$k`
    STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[vector_norm;fnorm] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN 
    SIMP_TAC [SQRT_POW_2; DOT_POS_LE] THEN 
    SIMP_TAC [dot; matrix_mul; transp; trace; LAMBDA_BETA; CART_EQ] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN
    `A$k$i' * (A:real^N^M)$k$i' =
        sum(1..dimindex(:M)) (\i. if i = k then A$k$i' * A$k$i' else &0)`
    SUBST1_TAC THENL
    [REWRITE_TAC[SUM_DELTA] THEN ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_LE_REFL; REAL_LE_SQUARE]);;

let FNORM_LE_L1 = prove
    (`!A:real^N^M. fnorm A <= sum(1..dimindex(:N))(\i.sum(1..dimindex(:M)) (\k. abs(A$k$i)))`,
    REPEAT GEN_TAC THEN REWRITE_TAC[fnorm] THEN 
    MATCH_MP_TAC REAL_LE_LSQRT THEN
    SIMP_TAC[transp;trace;matrix_mul;CART_EQ;LAMBDA_BETA] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    SIMP_TAC[SUM_POS_LE; FINITE_NUMSEG; REAL_LE_SQUARE; REAL_ABS_POS] THEN
    SPEC_TAC(`dimindex(:N)`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THENL
    [REAL_ARITH_TAC;ALL_TAC] THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THEN
    MATCH_MP_TAC(REAL_ARITH `a2 <= a * a /\ &0 <= a * b /\ b2 <= b * b
    ==> a2 + b2 <= (a + b) * (a + b)`) THEN
    ASM_SIMP_TAC[SUM_POS_LE; REAL_LE_MUL; REAL_ABS_POS; FINITE_NUMSEG] THEN
    SPEC_TAC(`dimindex(:M)`,`m:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THENL
    [REAL_ARITH_TAC;ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a2 <= a * a /\ &0 <= a * b /\ b2 <= b * b
    ==> a2 + b2 <= (a + b) * (a + b)`) THEN
    ASM_SIMP_TAC[SUM_POS_LE; REAL_LE_MUL; REAL_ABS_POS; FINITE_NUMSEG] THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC);;
    
let FNORM_MATRIX_POW_LE = prove
 (`!A:real^N^N n. (1 <= n) ==> fnorm (A matrix_pow n) <= (fnorm A) pow n`,
 let lem1 = REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS in
 let lem = ONCE_REWRITE_RULE 
           [TAUT `p ==> q ==> r <=> q ==> p ==> r`] lem1 in
 X_GEN_TAC `A:real^N^N` THEN ASM_CASES_TAC `fnorm (A:real^N^N) = &0` THENL
 [FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE [FNORM_EQ_0]) THEN
  ASM_SIMP_TAC[] THEN INDUCT_TAC; ALL_TAC] THENL
  [ARITH_TAC; ALL_TAC; ALL_TAC] THENL
  [SIMP_TAC [MATRIX_POW_0; real_pow; 
             REAL_MUL_LZERO; FNORM_0;REAL_LE_REFL]; ALL_TAC] THEN 
  INDUCT_TAC THENL
  [ARITH_TAC; ALL_TAC] THEN 
   STRIP_TAC THEN ASM_CASES_TAC `n:num = 0` THEN
   ASM_SIMP_TAC [matrix_pow; real_pow] THENL
   [SIMP_TAC[MATRIX_MUL_RID] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH lhand FNORM_SUBMULT o lhand o snd) THEN
    MATCH_MP_TAC lem THEN
    ASM_METIS_TAC [REAL_LE_LMUL_EQ; REAL_LT_LE; FNORM_POS_LE]);;
    
let FNORM_MATRIX_POW_SUC_LE = prove
    (`!A:real^N^N n. fnorm (A matrix_pow SUC n) <= (fnorm A) pow SUC n`,
    SIMP_TAC[ARITH_RULE `1 <= SUC n`;FNORM_MATRIX_POW_LE]);;
    
let FNORM_MSUM_NUMSEG_LE = prove
 (`!f:num->real^N^M m n. fnorm(msum (m..n) (\k. f(k))) 
                          <= sum (m..n) (\i. fnorm(f(i)))`,
 let lem1 = REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS in
 let lem = ONCE_REWRITE_RULE 
           [TAUT `p ==> q ==> r <=> q ==> p ==> r`] lem1 in
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN 
  SIMP_TAC [MSUM_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG] THENL
  [COND_CASES_TAC;ALL_TAC] THENL 
   [ASM_SIMP_TAC [ REAL_LE_REFL];
    ASM_SIMP_TAC [FNORM_0; REAL_LE_REFL];
    ALL_TAC] THEN
   COND_CASES_TAC THEN
    ASM_SIMP_TAC[] THEN 
    W(MP_TAC o PART_MATCH lhand FNORM_TRIANGLE o lhand o snd) THEN
    MATCH_MP_TAC lem THEN 
    ASM_SIMP_TAC [REAL_LE_RADD]);;
    
let FNORM_REAL = prove
 (`!x:real^1^1. fnorm(x) = abs(x$1$1)`,
  SIMP_TAC[fnorm; transp; trace; matrix_mul; CART_EQ; LAMBDA_BETA;
              SUM_1; DIMINDEX_1; SUM_SING_NUMSEG; FORALL_1; ARITH;
              GSYM REAL_POW_2; POW_2_SQRT_ABS]);;
    
let FNORM_LIFT2 = prove
(`!x. fnorm(lift_lift x) = abs(x)`,
  SIMP_TAC[lift_lift; FNORM_REAL; LIFT2_COMPONENT]);;
  
let MSUM_FNORM = prove
 (`!f:A->real^N^M s. FINITE s ==> fnorm(msum s f) <= sum s (\x. fnorm(f x))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; MSUM_CLAUSES; FNORM_0; REAL_LE_REFL] THEN
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand FNORM_TRIANGLE o lhand o snd) THEN 
  ASM_ARITH_TAC);;
  
let MSUM_FNORM1 = prove
 (`!f:A->B->real^N^M s1 s2. FINITE s1 /\ FINITE s2 ==>   
          fnorm(msum s2 (\y. msum s1 (\x. f x y))) <= 
          sum s2 (\y. sum s1 (\x. fnorm (f x y)))`,
  let lem1 = REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS in
  let lem = ONCE_REWRITE_RULE 
           [TAUT `p ==> q ==> r <=> q ==> p ==> r`] lem1 in        
  REPEAT GEN_TAC THEN SIMP_TAC [IMP_CONJ] THEN STRIP_TAC THEN
  SPEC_TAC (`s2:B->bool`,`s2:B->bool`) THEN  
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; MSUM_CLAUSES; FNORM_0; REAL_LE_REFL] THEN
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand FNORM_TRIANGLE o lhand o snd) THEN 
  MATCH_MP_TAC lem THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  ASM_SIMP_TAC [MSUM_FNORM]);;
  
let MSUM_FNORM2 = prove
 (`!f:A->B->C->real^N^M s1 s2 s3. FINITE s1 /\ FINITE s2  /\ FINITE s3 ==>   
          fnorm(
          msum s3 (\z. 
          msum s2 (\y. 
          msum s1 (\x. f x y z)))) <= 
          sum s3 (\z.
          sum s2 (\y.
          sum s1 (\x. fnorm (f x y z))))`,
  let lem1 = REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS in
  let lem = ONCE_REWRITE_RULE 
           [TAUT `p ==> q ==> r <=> q ==> p ==> r`] lem1 in        
  REPEAT STRIP_TAC THEN UNDISCH_TAC `FINITE (s3:C->bool)` THEN 
  SPEC_TAC (`s3:C->bool`,`s3:C->bool`) THEN  
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; MSUM_CLAUSES; FNORM_0; REAL_LE_REFL] THEN
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand FNORM_TRIANGLE o lhand o snd) THEN 
  MATCH_MP_TAC lem THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  ASM_SIMP_TAC [MSUM_FNORM;MSUM_FNORM1]);;
  
let MSUM_FNORM3 = prove
 (`!f:A->B->C->D->real^N^M s1 s2 s3 s4. 
    FINITE s1 /\ FINITE s2  /\ FINITE s3 /\ FINITE s4 ==>   
          fnorm(
          msum s4 (\w.
          msum s3 (\z. 
          msum s2 (\y. 
          msum s1 (\x. f x y z w))))) <= 
          sum s4 (\w.
          sum s3 (\z.
          sum s2 (\y.
          sum s1 (\x. fnorm (f x y z w)))))`,
  let lem1 = REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS in
  let lem = ONCE_REWRITE_RULE 
           [TAUT `p ==> q ==> r <=> q ==> p ==> r`] lem1 in        
  REPEAT STRIP_TAC THEN UNDISCH_TAC `FINITE (s4:D->bool)` THEN 
  SPEC_TAC (`s4:D->bool`,`s4:D->bool`) THEN  
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; MSUM_CLAUSES; FNORM_0; REAL_LE_REFL] THEN
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand FNORM_TRIANGLE o lhand o snd) THEN 
  MATCH_MP_TAC lem THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  ASM_SIMP_TAC [MSUM_FNORM;MSUM_FNORM1;MSUM_FNORM2]);;
  
let MSUM_FNORM_LE = prove
 (`!s f:A->real^N^M g.
        FINITE s /\ (!x. x IN s ==> fnorm(f x) <= g(x))
        ==> fnorm(msum s f) <= sum s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\x:A. fnorm(f x :real^N^M))` THEN
  ASM_SIMP_TAC[MSUM_FNORM; SUM_LE]);;
  
let MSUM_FNORM_LE1 = prove
 (`!s1 s2 f:A->B->real^N^M g.
        FINITE (s1) /\ FINITE (s2) /\ 
        (!x y. x IN s1 /\ y IN s2 ==> fnorm(f x y) <= g x y)
        ==> fnorm(msum s2 (\y.msum s1 (\x. f x y))) 
             <= sum s2 (\y. sum s1 (\x. g x y))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s2 (\y:B. sum s1 (\x:A. fnorm(f x y:real^N^M)))` THEN
  ASM_SIMP_TAC [SUM_SUM_LE;MSUM_FNORM1]);;  
  
let MSUM_FNORM_LE2 = prove
 (`!s1 s2 s3 f:A->B->C->real^N^M g.
        FINITE (s1) /\ FINITE (s2) /\ FINITE (s3) /\ 
        (!x y z. x IN s1 /\ y IN s2 /\ z IN s3 ==> fnorm(f x y z) <= g x y z)
        ==> fnorm(
            msum s3 (\z. 
            msum s2 (\y.
            msum s1 (\x. f x y z)))) <= 
        sum s3 (\z.
        sum s2 (\y.
        sum s1 (\x. g x y z)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s3 (\z:C. sum s2 (\y:B. sum s1 (\x:A. fnorm(f x y z:real^N^M))))` THEN
  ASM_SIMP_TAC [MSUM_FNORM2] THEN MATCH_MP_TAC SUM_LE THEN 
  ASM_SIMP_TAC [SUM_SUM_LE]);;
  
let MSUM_FNORM_LE3 = prove
 (`!s1 s2 s3 s4 f:A->B->C->D->real^N^M g.
        FINITE (s1) /\ FINITE (s2) /\ FINITE (s3) /\ FINITE (s4) /\
        (!x y z w. x IN s1 /\ y IN s2 /\ z IN s3 /\ w IN s4
        ==> fnorm(f x y z w) <= g x y z w)
        ==> fnorm(
            msum s4 (\w. 
            msum s3 (\z. 
            msum s2 (\y.
            msum s1 (\x. f x y z w))))) <= 
        sum s4 (\w. 
        sum s3 (\z.
        sum s2 (\y.
        sum s1 (\x. g x y z w))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s4 (\w:D. sum s3 (\z:C. sum s2 (\y:B. sum s1 (\x:A. fnorm(f x y z w:real^N^M)))))` THEN
  ASM_SIMP_TAC [SUM_SUM_LE;MSUM_FNORM3]);;
  
let REAL_ABS_FNORM = prove
 (`!x:real^N^M. abs(fnorm x) = fnorm x`,
  REWRITE_TAC[FNORM_POS_LE; REAL_ABS_REFL]);;
  
let FNORM_TRIANGLE_SUB = prove
 (`!x y:real^N^M. fnorm(x) <= fnorm(y) + fnorm(x - y)`,
  MESON_TAC[FNORM_TRIANGLE; MATRIX_SUB_ADD2]);;
  
let FNORM_TRIANGLE_LE = prove
 (`!x y:real^N^M. fnorm(x) + fnorm(y) <= e ==> fnorm(x + y) <= e`,
  MESON_TAC[REAL_LE_TRANS; FNORM_TRIANGLE]);;

let FNORM_TRIANGLE_LT = prove
 (`!x y:real^N^M. fnorm(x) + fnorm(y) < e ==> fnorm(x + y) < e`,
  MESON_TAC[REAL_LET_TRANS; FNORM_TRIANGLE]);;

(* ------------------------------------------------------------------------- *)
(* The definition and properties of the distance in matrix space             *)
(* ------------------------------------------------------------------------- *) 

make_overloadable "matrix_dist" `:A#A->real`;;

overload_interface("matrix_dist",`real_matrix_dist:real^N^M#real^N^M->real`);;

overload_interface("matrix_dist",`complex_matrix_dist:complex^N^M#complex^N^M->real`);;

let real_matrix_dist = new_definition
    `real_matrix_dist (A:real^N^M,B:real^N^M) = real_fnorm(A - B)`;;

let complex_matrix_dist = new_definition
  `complex_matrix_dist (A:complex^N^M,B:complex^N^M) = complex_fnorm(A - B)`;;

let matrix_dist = prove
    (`(!A B:real^N^M. real_matrix_dist(A,B) = real_fnorm(A - B)) /\
    (!A B:complex^N^M. complex_matrix_dist(A,B) = complex_fnorm(A - B))`,
    SIMP_TAC[real_matrix_dist;complex_matrix_dist]);;
    
let COMPLEX_MATRIX_DIST = prove
    (`!A B:complex^N^M. matrix_dist(A,B) = real_fnorm((lambda i j. norm(A$i$j - B$i$j)):real^N^M)`,
    SIMP_TAC[matrix_dist;COMPLEX_FNORM;CMATRIX_SUB_COMPONENT]);;

(* properties of real matrix distance *)
    
let MATRIX_DIST_REFL = prove
    (`!A:real^N^M. matrix_dist(A,A) = &0`,
    SIMP_TAC[matrix_dist;MATRIX_SUB_REFL;FNORM_0]);;

let MATRIX_DIST_POS_LE = prove
    (`!A:real^N^M B. &0 <= matrix_dist(A,B)`,
    REWRITE_TAC [matrix_dist;FNORM_POS_LE]);;
 
let MATRIX_DIST_EQ_0 = prove
    (`!A:real^N^M B. (matrix_dist(A,B) = &0) <=> (A = B)`,
    REPEAT GEN_TAC THEN METIS_TAC[matrix_dist;FNORM_EQ_0;MATRIX_SUB_EQ]);;
 
let MATRIX_DIST_SYM = prove
    (`!A:real^N^M B. matrix_dist(A,B) = matrix_dist(B,A)`,
    REPEAT GEN_TAC THEN METIS_TAC[matrix_dist;FNORM_SUB_SYM]);;

let REAL_ABS_MATRIX_DIST = prove
    (`!A B:real^N^M. abs(matrix_dist(A,B)) = matrix_dist(A,B)`,
    REPEAT GEN_TAC THEN METIS_TAC[matrix_dist;REAL_ABS_REFL;FNORM_POS_LE]);;
  
let MATRIX_DIST_TRIANGLE = prove
    (`!A:real^N^M B C. matrix_dist(A,C) <= matrix_dist(A,B) + matrix_dist(B,C)`,
    let MATRIX_SUB_TRANS = prove
    (`!A:real^N^M B C. A - C = (A - B) + (B - C)`,
    REPEAT GEN_TAC THEN
    SIMP_TAC[matrix_add; CART_EQ; LAMBDA_BETA;matrix_sub] THEN
    ARITH_TAC) in
    REPEAT GEN_TAC THEN SIMP_TAC[matrix_dist] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MATRIX_SUB_TRANS] THEN
    SIMP_TAC[FNORM_TRIANGLE]);;
   
let MATRIX_DIST_TRIANGLE_ALT = prove
    (`!A:real^N^M B C. matrix_dist(B,C) <= matrix_dist(A,B) + matrix_dist(A,C)`,
    METIS_TAC[MATRIX_DIST_SYM;MATRIX_DIST_TRIANGLE]);;

let MATRIX_DIST_POS_LT = prove
    (`!A:real^N^M B. ~(A = B) ==> &0 < matrix_dist(A,B)`,
    METIS_TAC[matrix_dist;MATRIX_SUB_EQ;FNORM_POS_LT]);;
  
let MATRIX_DIST_NZ = prove
    (`!A:real^N^M B. ~(A = B) <=> &0 < matrix_dist(A,B)`,
    METIS_TAC[matrix_dist;MATRIX_SUB_EQ;FNORM_POS_LT]);;

let MATRIX_DIST_EQ = prove
    (`!A:real^N^M B C D:real^N^M. matrix_dist(A,B) = matrix_dist(C,D) <=> matrix_dist(A,B) pow 2 = matrix_dist(C,D) pow 2`,
    REWRITE_TAC[matrix_dist; FNORM_POW_2; FNORM_EQ]);;
    
let MATRIX_DIST_0 = prove
    (`!A:real^N^M. matrix_dist(A,mat 0) = fnorm A /\ matrix_dist(mat 0,A) = fnorm A`,
    METIS_TAC[matrix_dist;MATRIX_SUB_RZERO;MATRIX_SUB_LZERO;MATRIX_DIST_SYM]);;
    
let MATRIX_DIST_REAL = prove
 (`!x:real^1^1 y. matrix_dist(x,y) = abs(x$1$1 - y$1$1)`,
  SIMP_TAC[matrix_dist; FNORM_REAL; matrix_sub; 
           LAMBDA_BETA; LE_REFL; DIMINDEX_1]);;
             
let MATRIX_DIST_LIFT2 = prove
 (`!x y. matrix_dist(lift_lift x,lift_lift y) = abs(x - y)`,
  REWRITE_TAC[MATRIX_DIST_REAL; LIFT2_COMPONENT]);;
  
make_overloadable "matrix_between" `:A->A#A->bool`;;

overload_interface("matrix_between",`real_matrix_between:real^N^M->real^N^M#real^N^M->bool`);;

overload_interface("matrix_between",`complex_matrix_between:complex^N^M->complex^N^M#complex^N^M->bool`);;
  
let real_matrix_between = new_definition
 `real_matrix_between (x:real^N^M) (a,b) <=> 
  matrix_dist(a,b) = matrix_dist(a,x) + matrix_dist(x,b)`;;
  
let complex_matrix_between = new_definition
 `complex_matrix_between (x:complex^N^M) (a,b) <=> 
  matrix_dist(a,b) = matrix_dist(a,x) + matrix_dist(x,b)`;;
  
let matrix_between = prove
    (`(!x a b. real_matrix_between (x:real^N^M) (a,b) <=> 
  matrix_dist(a,b) = matrix_dist(a,x) + matrix_dist(x,b)) /\
  (!x a b. complex_matrix_between (x:real^N^M) (a,b) <=> 
  matrix_dist(a,b) = matrix_dist(a,x) + matrix_dist(x,b))`,
  SIMP_TAC[real_matrix_between;complex_matrix_between]);;
  
let MATRIX_CHOOSE_SIZE = prove
 (`!c. &0 <= c ==> ?x:real^N^M. fnorm(x) = c`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `c %% (lambda i j. if i = 1 /\ j = 1 then &1 else &0):real^N^M` THEN
  ASM_REWRITE_TAC[FNORM_MUL; real_abs] THEN 
  SIMP_TAC[fnorm;trace;transp;matrix_mul;CART_EQ;LAMBDA_BETA;COND_LMUL_0;COND_RMUL_0;REAL_MUL_LID] THEN
  MATCH_MP_TAC (REAL_FIELD `k = &1 ==> c * k = c`) THEN
  SIMP_TAC[SQRT_EQ_1;GSYM (SIMP_RULE [SUM_DELTA] SUM_SUM_DELTA);GSYM IN_SING] THEN
  SIMP_TAC[IN_SING;SUM_DELTA;SUM_SUM_DELTA;IN_NUMSEG;LE_REFL;DIMINDEX_GE_1]);;
  
let MATRIX_CHOOSE_DIST = prove
 (`!x e. &0 <= e ==> ?y:real^N^M. matrix_dist(x,y) = e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?c:real^N^M. fnorm(c) = e` CHOOSE_TAC THENL
   [ASM_SIMP_TAC[MATRIX_CHOOSE_SIZE]; ALL_TAC] THEN
  EXISTS_TAC `x - c:real^N^M` THEN REWRITE_TAC[matrix_dist] THEN
  ASM_REWRITE_TAC[CMATRIX_ARITH `x - (x - c) = c:real^N^M`]);;

(* ------------------------------------------------------------------------- *)
(* The definition and properties of  matrix space                            *)
(* ------------------------------------------------------------------------- *)

make_overloadable "matrix_open" `:(A->bool)->bool`;;

overload_interface("matrix_open",`real_matrix_open:(real^N^M->bool)->bool`);;

overload_interface("matrix_open",`complex_matrix_open:(complex^N^M->bool)->bool`);;

let real_matrix_open = new_definition
    `real_matrix_open s <=> !A:real^N^M. A IN s ==>
        ?e. &0 < e /\ !A'. matrix_dist(A',A) < e ==> A' IN s`;;

let complex_matrix_open = new_definition
    `complex_matrix_open s <=> !A:complex^N^M. A IN s ==>
        ?e. &0 < e /\ !A'. matrix_dist(A',A) < e ==> A' IN s`;;
        
let matrix_open = prove
    (`(!s. real_matrix_open s <=> !A:real^N^M. A IN s ==>
        ?e. &0 < e /\ !A'. matrix_dist(A',A) < e ==> A' IN s) /\
    (!s. complex_matrix_open s <=> !A:complex^N^M. A IN s ==>
        ?e. &0 < e /\ !A'. matrix_dist(A',A) < e ==> A' IN s)`,
    SIMP_TAC[real_matrix_open;complex_matrix_open]);;

make_overloadable "matrix_space" `:(A)topology`;;

overload_interface("matrix_space",`real_matrix_space:(real^N^M)topology`);;

overload_interface("matrix_space",`complex_matrix_space:(complex^N^M)topology`);;
    
let real_matrix_space = new_definition
    `real_matrix_space = topology real_matrix_open`;;
    
let complex_matrix_space = new_definition
    `complex_matrix_space = topology complex_matrix_open`;;
    
let matrix_space = prove
    (`real_matrix_space = topology real_matrix_open /\ complex_matrix_space = topology complex_matrix_open`,
    SIMP_TAC[real_matrix_space;complex_matrix_space]);;
 
make_overloadable "matrix_space_metric" `:(A)metric`;;

overload_interface("matrix_space_metric",`real_matrix_space_metric:(real^N^M)metric`);;

overload_interface("matrix_space_metric",`complex_matrix_space_metric:(complex^N^M)metric`);; 
 
let real_matrix_space_metric = new_definition
    `real_matrix_space_metric = metric ((:real^N^M), real_matrix_dist)`;;
    
let complex_matrix_space_metric = new_definition
    `complex_matrix_space_metric = metric ((:complex^N^M), complex_matrix_dist)`;;
    
let matrix_space_metric = prove
    (`real_matrix_space_metric = metric ((:real^N^M), real_matrix_dist) /\ complex_matrix_space_metric = metric ((:complex^N^M), complex_matrix_dist)`,
    SIMP_TAC[real_matrix_space_metric;complex_matrix_space_metric]);;

(* properties of real matrix entries*)
    
let MATRIX_OPEN_EMPTY = prove
 (`matrix_open ({}:real^N^M->bool)`,
  REWRITE_TAC[matrix_open; NOT_IN_EMPTY]);;

let MATRIX_OPEN_UNIV = prove
 (`matrix_open(:real^N^M)`,
  REWRITE_TAC[matrix_open; IN_UNIV] THEN MESON_TAC[REAL_LT_01]);;
  
let MATRIX_OPEN_UNIONS = prove
 (`(!s:real^N^M->bool. s IN f ==> matrix_open s) ==> matrix_open(UNIONS f)`,
  REWRITE_TAC[matrix_open; IN_UNIONS] THEN MESON_TAC[]);;    
    
let MATRIX_SPACE_METRIC = prove
    (`mdist (matrix_space_metric:(real^N^M)metric) = matrix_dist /\
    mspace matrix_space_metric = (:real^N^M)`,
    SUBGOAL_THEN `is_metric_space ((:real^N^M),matrix_dist)` MP_TAC THENL
    [REWRITE_TAC[is_metric_space; IN_UNIV; MATRIX_DIST_POS_LE; MATRIX_DIST_EQ_0;
                 MATRIX_DIST_SYM; MATRIX_DIST_TRIANGLE];
    SIMP_TAC[matrix_space_metric; MDIST; MSPACE]]);;
    
let OPEN_IN_MATRIX_SPACE_METRIC = prove
    (`open_in (mtopology matrix_space_metric) = matrix_open:(real^N^M->bool)->bool`,
    REWRITE_TAC[FUN_EQ_THM; OPEN_IN_MTOPOLOGY; matrix_open; MATRIX_SPACE_METRIC;
                SUBSET_UNIV; SUBSET; IN_MBALL; IN_UNIV; MATRIX_DIST_SYM]);;
             
let OPEN_IN_MATRIX_SPACE = prove
    (`open_in (matrix_space:(real^N^M)topology) = matrix_open`,
    REWRITE_TAC[matrix_space; GSYM OPEN_IN_MATRIX_SPACE_METRIC] THEN
    MESON_TAC[topology_tybij]);;
 
let MATRIX_OPEN_IN = prove
    (`!s:real^N^M->bool. matrix_open s <=> open_in matrix_space s`,
    REWRITE_TAC[OPEN_IN_MATRIX_SPACE]);;
    
let MATRIX_OPEN_SUBOPEN = prove
 (`!s:real^N^M->bool. matrix_open s <=> !x. x IN s ==> ?t. matrix_open t /\ x IN t /\ t SUBSET s`,
  REWRITE_TAC[MATRIX_OPEN_IN; GSYM OPEN_IN_SUBOPEN]);;
    
let MTOPOLOGY_MATRIX_SPACE_METRIC = prove
    (`mtopology matrix_space_metric = matrix_space:(real^N^M)topology`,
    REWRITE_TAC[TOPOLOGY_EQ; OPEN_IN_MATRIX_SPACE_METRIC; MATRIX_OPEN_IN]);;
    
let TOPSPACE_MATRIX_SPACE = prove
 (`topspace matrix_space = (:real^N^M)`,
  REWRITE_TAC[topspace; EXTENSION; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[MATRIX_OPEN_UNIV; IN_UNIV; MATRIX_OPEN_IN]);;
  
let TOPSPACE_MATRIX_SPACE_SUBTOPOLOGY = prove
 (`!s:real^N^M->bool. topspace (subtopology matrix_space s) = s`,
  REWRITE_TAC[TOPSPACE_MATRIX_SPACE; TOPSPACE_SUBTOPOLOGY; INTER_UNIV]);;

let MATRIX_OPEN_IN_OPEN = prove
 (`!s:real^N^M->bool u.
        open_in (subtopology matrix_space u) s <=> 
                 ?t. matrix_open t /\ (s = u INTER t)`,
  REPEAT STRIP_TAC THEN 
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; GSYM MATRIX_OPEN_IN] THEN
  REWRITE_TAC[INTER_ACI]);;  
  
(* ------------------------------------------------------------------------- *)
(* Closed sets in matrix space                                               *)
(* ------------------------------------------------------------------------- *)

make_overloadable "matrix_closed" `:A->bool`;;

overload_interface("matrix_closed",`real_matrix_closed:(real^N^M->bool)->bool`);;

overload_interface("matrix_closed",`complex_matrix_closed:(complex^N^M->bool)->bool`);; 

let real_matrix_closed = new_definition
  `real_matrix_closed(s:real^N^M->bool) <=> matrix_open(UNIV DIFF s)`;;
  
let complex_matrix_closed = new_definition
  `complex_matrix_closed(s:complex^N^M->bool) <=> matrix_open(UNIV DIFF s)`;;
  
let matrix_closed = prove
    (`(!s. real_matrix_closed s <=> matrix_open(UNIV DIFF s)) /\
    (!s. complex_matrix_closed s <=> matrix_open(UNIV DIFF s))`,
    SIMP_TAC[real_matrix_closed;complex_matrix_closed]);;
    
(* properties of real matrix entries*)

let MATRIX_CLOSED_IN = prove
 (`!s:real^N^M->bool. matrix_closed s <=> closed_in matrix_space s`,
  REWRITE_TAC[matrix_closed; closed_in; TOPSPACE_MATRIX_SPACE; 
              MATRIX_OPEN_IN; SUBSET_UNIV]);;

let CLOSED_IN_MATRIX_SPACE = prove
 (`closed_in matrix_space = matrix_closed:(real^N^M->bool)->bool`,
  REWRITE_TAC[MATRIX_CLOSED_IN; FUN_EQ_THM]);;
  
let MATRIX_CLOSED_INTERS = prove
 (`!f. (!s:real^N^M->bool. s IN f ==> matrix_closed s) 
            ==> matrix_closed(INTERS f)`,
  REWRITE_TAC[MATRIX_CLOSED_IN] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N^M->bool)->bool = {}` THEN
  ASM_SIMP_TAC[CLOSED_IN_INTERS; INTERS_0] THEN
  REWRITE_TAC[GSYM TOPSPACE_MATRIX_SPACE; CLOSED_IN_TOPSPACE]);;
  
let MATRIX_CLOSED_EMPTY = prove
 (`matrix_closed ({}:real^N^M->bool)`,
  REWRITE_TAC[MATRIX_CLOSED_IN; CLOSED_IN_EMPTY]);;
  
let MATRIX_CLOSED_INTER = prove
 (`!s t:real^N^M->bool. matrix_closed s /\ matrix_closed t ==> matrix_closed(s INTER t)`,
  REWRITE_TAC[MATRIX_CLOSED_IN; CLOSED_IN_INTER]);;
  
let MATRIX_CLOSED_UNIV = prove
 (`matrix_closed(UNIV:real^N^M->bool)`,
  REWRITE_TAC[MATRIX_CLOSED_IN; GSYM TOPSPACE_MATRIX_SPACE; CLOSED_IN_TOPSPACE]);;
  
let MATRIX_CLOSED_IN_CLOSED = prove
 (`!s:real^N^M->bool u.
    closed_in (subtopology matrix_space u) s <=> 
        ?t. matrix_closed t /\ (s = u INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY; 
                                    GSYM MATRIX_CLOSED_IN] THEN
  REWRITE_TAC[INTER_ACI]);;
  
let MATRIX_CLOSED_IN_CLOSED_TRANS = prove
 (`!s t:real^N^M->bool. closed_in (subtopology matrix_space t) s /\ matrix_closed t 
         ==> matrix_closed s`,
  REWRITE_TAC[ONCE_REWRITE_RULE[GSYM SUBTOPOLOGY_UNIV] MATRIX_CLOSED_IN] THEN
  REWRITE_TAC[CLOSED_IN_TRANS]);;
  
let MATRIX_CLOSED_IN_CLOSED_INTER = prove
 (`!u s:real^N^M->bool. matrix_closed s ==> closed_in (subtopology matrix_space u) (u INTER s)`,
  REWRITE_TAC[MATRIX_CLOSED_IN_CLOSED] THEN MESON_TAC[]);;
  
let MATRIX_CLOSED_DIFF = prove
 (`!s t:real^N^M->bool. matrix_closed s /\ matrix_open t ==> matrix_closed(s DIFF t)`,
  REWRITE_TAC[MATRIX_OPEN_IN; MATRIX_CLOSED_IN; CLOSED_IN_DIFF]);;  
 
(* ------------------------------------------------------------------------- *)
(* Open and closed intervals in matrix space                         *)
(* ------------------------------------------------------------------------- *) 
 
make_overloadable "matrix_interval" `:A->B`;;

overload_interface("matrix_interval",`open_rmatrix_interval:(real^N^M#real^N^M)->(real^N^M->bool)`);;

overload_interface("matrix_interval",`closed_rmatrix_interval:(real^N^M#real^N^M)list->(real^N^M->bool)`);;

overload_interface("matrix_interval",`open_cmatrix_interval:(complex^N^M#complex^N^M)->(complex^N^M->bool)`);;

overload_interface("matrix_interval",`closed_cmatrix_interval:(complex^N^M#complex^N^M)list->(complex^N^M->bool)`);;

let open_rmatrix_interval = new_definition
  `open_rmatrix_interval(a:real^N^M,b:real^N^M) =
        {x:real^N^M | !i j. (1 <= i /\ i <= dimindex(:M)) /\
                          (1 <= j /\ j <= dimindex(:N))
                        ==> a$i$j < x$i$j /\ x$i$j < b$i$j}`;;

let closed_rmatrix_interval = new_definition
  `closed_rmatrix_interval(l:(real^N^M#real^N^M)list) =
         {x:real^N^M | !i j. (1 <= i /\ i <= dimindex(:M)) /\
                          (1 <= j /\ j <= dimindex(:N))
                         ==> FST(HD l)$i$j <= x$i$j /\ x$i$j <= SND(HD l)$i$j}`;;
                         

let open_cmatrix_interval = new_definition
  `open_cmatrix_interval(a:complex^N^M,b:complex^N^M) =
        {x:complex^N^M | !i j. (1 <= i /\ i <= dimindex(:M)) /\
                          (1 <= j /\ j <= dimindex(:N))
                        ==> Re(a$i$j) < Re(x$i$j) /\ Re(x$i$j) < Re(b$i$j) /\
                        Im(a$i$j) < Im(x$i$j) /\ Im(x$i$j) < Im(b$i$j)}`;;

let closed_cmatrix_interval = new_definition
  `closed_cmatrix_interval(l:(complex^N^M#complex^N^M)list) =
         {x:complex^N^M | !i j. (1 <= i /\ i <= dimindex(:M)) /\
                          (1 <= j /\ j <= dimindex(:N))
                         ==> Re(FST(HD l)$i$j) <= Re(x$i$j) /\ Re(x$i$j) <= Re(SND(HD l)$i$j) /\
                         Im(FST(HD l)$i$j) <= Im(x$i$j) /\ Im(x$i$j) <= Im(SND(HD l)$i$j)}`;;

let matrix_interval = prove
 (`(!a:real^N^M b. (matrix_interval (a,b) = 
           {x:real^N^M | !i j. (1 <= i /\ i <= dimindex(:M)) /\
                          (1 <= j /\ j <= dimindex(:N))
                        ==> a$i$j < x$i$j /\ x$i$j < b$i$j}) /\
   (matrix_interval [a,b] =  
           {x:real^N^M | !i j. (1 <= i /\ i <= dimindex(:M)) /\
                          (1 <= j /\ j <= dimindex(:N))
                         ==> a$i$j <= x$i$j /\ x$i$j <= b$i$j})) /\
(!a:complex^N^M b. (matrix_interval (a,b) = 
           {x:complex^N^M | !i j. (1 <= i /\ i <= dimindex(:M)) /\
                          (1 <= j /\ j <= dimindex(:N))
                        ==> Re(a$i$j) < Re(x$i$j) /\ Re(x$i$j) < Re(b$i$j) /\
                        Im(a$i$j) < Im(x$i$j) /\ Im(x$i$j) < Im(b$i$j)}) /\
   (matrix_interval [a,b] =  
           {x:complex^N^M | !i j. (1 <= i /\ i <= dimindex(:M)) /\
                          (1 <= j /\ j <= dimindex(:N))
                         ==> Re(a$i$j) <= Re(x$i$j) /\ Re(x$i$j) <= Re(b$i$j) /\
                        Im(a$i$j) <= Im(x$i$j) /\ Im(x$i$j) <= Im(b$i$j)}))`,
  REWRITE_TAC[open_rmatrix_interval; closed_rmatrix_interval;open_cmatrix_interval; closed_cmatrix_interval; HD; FST; SND]);;
  
(* properties of real matrix entries*)

let IN_MATRIX_INTERVAL = prove
 (`(!x:real^N^M.
        x IN matrix_interval (a,b) <=>
                !i j. (1 <= i /\ i <= dimindex(:M)) /\
                          (1 <= j /\ j <= dimindex(:N))
                        ==> a$i$j < x$i$j /\ x$i$j < b$i$j) /\
   (!x:real^N^M.
        x IN matrix_interval [a,b] <=>
                !i j. (1 <= i /\ i <= dimindex(:M)) /\
                          (1 <= j /\ j <= dimindex(:N))
                         ==> a$i$j <= x$i$j /\ x$i$j <= b$i$j)`,
  REWRITE_TAC[matrix_interval; IN_ELIM_THM]);;
  
let MATRIX_INTERVAL_OPEN_SUBSET_CLOSED = prove
 (`!a b:real^N^M. matrix_interval(a,b) SUBSET matrix_interval[a,b]`,
  REWRITE_TAC[SUBSET; IN_MATRIX_INTERVAL] THEN MESON_TAC[REAL_LT_IMP_LE]);;
  
let MATRIX_INTERVAL_EQ_EMPTY = prove
 (`((matrix_interval [a:real^N^M,b] = {}) <=>
    ?i j. (1 <= i /\ i <= dimindex(:M)) /\ (1 <= j /\ j <= dimindex(:N))
           /\ b$i$j < a$i$j) /\
   ((matrix_interval (a:real^N^M,b) = {}) <=>
    ?i j. (1 <= i /\ i <= dimindex(:M)) /\ (1 <= j /\ j <= dimindex(:N))
           /\ b$i$j <= a$i$j)`,
  REWRITE_TAC[EXTENSION; IN_MATRIX_INTERVAL; NOT_IN_EMPTY] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; GSYM CONJ_ASSOC] THEN
  CONJ_TAC THEN EQ_TAC THENL
   [MESON_TAC[REAL_LE_REFL; REAL_NOT_LE];
    MESON_TAC[REAL_LE_TRANS; REAL_NOT_LE];
    ALL_TAC;
    MESON_TAC[REAL_LT_TRANS; REAL_NOT_LT]] THEN
  SUBGOAL_THEN `!a b. ?c. a < b ==> a < c /\ c < b`
  (MP_TAC o REWRITE_RULE[SKOLEM_THM]) THENL
   [MESON_TAC[REAL_LT_BETWEEN]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `mid:real->real->real`) THEN
  DISCH_THEN(MP_TAC o SPEC
   `(lambda i j. mid ((a:real^N^M)$i$j) ((b:real^N^M)$i$j)):real^N^M`) THEN
  STRIP_TAC THEN POP_ASSUM MP_TAC THEN 
  ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN STRIP_TAC THEN 
  MAP_EVERY EXISTS_TAC [`i:num`;`j:num`] THEN ASM_SIMP_TAC [] THEN 
  FIRST_X_ASSUM (MP_TAC o SPECL [`(a:real^N^M)$i$j`;`(b:real^N^M)$i$j`]) THEN 
  ASM_MESON_TAC[CONTRAPOS_THM; REAL_NOT_LT]);;
  
let MATRIX_INTERVAL_NE_EMPTY = prove
  (`(~(matrix_interval [a:real^N^M,b] = {}) <=>
    !i j. (1 <= i /\ i <= dimindex(:M)) /\ (1 <= j /\ j <= dimindex(:N)) 
         ==> a$i$j <= b$i$j) /\
   (~(matrix_interval (a:real^N^M,b) = {}) <=>
    !i j. (1 <= i /\ i <= dimindex(:M)) /\ (1 <= j /\ j <= dimindex(:N)) 
         ==> a$i$j < b$i$j)`,
  REWRITE_TAC[MATRIX_INTERVAL_EQ_EMPTY] THEN MESON_TAC[REAL_NOT_LE]);; 
 
(* ------------------------------------------------------------------------- *)
(* Open and closed balls and spheres in matrix space                         *)
(* ------------------------------------------------------------------------- *)

make_overloadable "matrix_ball" `:A->B`;;

overload_interface("matrix_ball",`real_matrix_ball:(real^N^M#real)->(real^N^M->bool)`);;

overload_interface("matrix_ball",`complex_matrix_ball:(complex^N^M#real)->(complex^N^M->bool)`);; 

let real_matrix_ball = new_definition
  `!x:real^N^M. real_matrix_ball(x,e) = { y | matrix_dist(x,y) < e}`;;
  
let complex_matrix_ball = new_definition
  `!x:complex^N^M. complex_matrix_ball(x,e) = { y | matrix_dist(x,y) < e}`;;
  
let matrix_ball = prove
    (`(!x:real^N^M. real_matrix_ball(x,e) = { y | matrix_dist(x,y) < e}) /\
    (!x:complex^N^M. complex_matrix_ball(x,e) = { y | matrix_dist(x,y) < e})`,
    SIMP_TAC[real_matrix_ball;complex_matrix_ball]);;
    
(* properties of real matrix entries*)
  
let IN_MATRIX_BALL = prove
 (`!x:real^N^M y e. y IN matrix_ball(x,e) <=> matrix_dist(x,y) < e`,
  REWRITE_TAC[matrix_ball; IN_ELIM_THM]);;
  
let MBALL_MATRIX_SPACE = prove
 (`!x:real^N^M r. mball matrix_space_metric (x,r) = matrix_ball(x,r)`,
  REWRITE_TAC[EXTENSION; IN_MBALL; IN_MATRIX_BALL; 
              MATRIX_SPACE_METRIC; IN_UNIV]);;
        
make_overloadable "matrix_cball" `:A->B`;;

overload_interface("matrix_cball",`real_matrix_cball:(real^N^M#real)->(real^N^M->bool)`);;

overload_interface("matrix_cball",`complex_matrix_cball:(complex^N^M#real)->(complex^N^M->bool)`);; 

let real_matrix_cball = new_definition
  `!x:real^N^M. real_matrix_cball(x,e) = { y | matrix_dist(x,y) <= e}`;;
  
let complex_matrix_cball = new_definition
  `!x:complex^N^M. complex_matrix_cball(x,e) = { y | matrix_dist(x,y) <= e}`;;
  
let matrix_cball = prove
    (`(!x:real^N^M. real_matrix_cball(x,e) = { y | matrix_dist(x,y) <= e}) /\
    (!x:complex^N^M. complex_matrix_cball(x,e) = { y | matrix_dist(x,y) <= e})`,
    SIMP_TAC[real_matrix_cball;complex_matrix_cball]);;
    
(* properties of real matrix entries*)
  
let IN_MATRIX_CBALL = prove
 (`!x:real^N^M y e. y IN matrix_cball(x,e) <=> matrix_dist(x,y) <= e`,
  REWRITE_TAC[matrix_cball; IN_ELIM_THM]);;
  
let MCBALL_MATRIX_SPACE = prove
 (`!x:real^N^M r. mcball matrix_space_metric (x,r) = matrix_cball(x,r)`,
  REWRITE_TAC[EXTENSION; IN_MCBALL; IN_MATRIX_CBALL; 
              MATRIX_SPACE_METRIC; IN_UNIV]);;
              
make_overloadable "matrix_sphere" `:A->B`;;

overload_interface("matrix_sphere",`real_matrix_sphere:(real^N^M#real)->(real^N^M->bool)`);;

overload_interface("matrix_sphere",`complex_matrix_sphere:(complex^N^M#real)->(complex^N^M->bool)`);; 

let real_matrix_sphere = new_definition
  `!x:real^N^M. real_matrix_sphere(x,e) = { y | matrix_dist(x,y) = e}`;;
  
let complex_matrix_sphere = new_definition
  `!x:complex^N^M. complex_matrix_sphere(x,e) = { y | matrix_dist(x,y) = e}`;;
  
let matrix_sphere = prove
    (`(!x:real^N^M. real_matrix_sphere(x,e) = { y | matrix_dist(x,y) = e}) /\
    (!x:complex^N^M. complex_matrix_sphere(x,e) = { y | matrix_dist(x,y) = e})`,
    SIMP_TAC[real_matrix_sphere;complex_matrix_sphere]);;              
              
(* properties of real matrix entries*)
  
let IN_MATRIX_SPHERE = prove
 (`!x:real^N^M y e. y IN matrix_sphere(x,e) <=> matrix_dist(x,y) = e`,
  REWRITE_TAC[matrix_sphere; IN_ELIM_THM]);;
  
let OPEN_MATRIX_BALL = prove
 (`!x:real^N^M e. matrix_open(matrix_ball(x,e))`,
  REWRITE_TAC[matrix_open; matrix_ball; IN_ELIM_THM] THEN 
  ONCE_REWRITE_TAC[MATRIX_DIST_SYM] THEN
  MESON_TAC[REAL_SUB_LT; REAL_LT_SUB_LADD; REAL_ADD_SYM; REAL_LET_TRANS;
            MATRIX_DIST_TRIANGLE_ALT]);;

let CENTRE_IN_MATRIX_BALL = prove
 (`!x:real^N^M e. x IN matrix_ball(x,e) <=> &0 < e`,
  MESON_TAC[IN_MATRIX_BALL; MATRIX_DIST_REFL]);;
  
let CENTRE_IN_MATRIX_CBALL = prove
 (`!x:real^N^M e. x IN matrix_cball(x,e) <=> &0 <= e`,
  MESON_TAC[IN_MATRIX_CBALL; MATRIX_DIST_REFL]);;
  
let MATRIX_OPEN_CONTAINS_BALL = prove
 (`!s:real^N^M->bool. matrix_open s <=> !x. x IN s ==> ?e. &0 < e /\ matrix_ball(x,e) SUBSET s`,
  REWRITE_TAC[matrix_open; SUBSET; IN_MATRIX_BALL] THEN 
  REWRITE_TAC[MATRIX_DIST_SYM]);;
  
let MATRIX_OPEN_BALL = prove
 (`!x:real^N^M e. matrix_open(matrix_ball(x,e))`,
  REWRITE_TAC[matrix_open; matrix_ball; IN_ELIM_THM] THEN 
  ONCE_REWRITE_TAC[MATRIX_DIST_SYM] THEN
  MESON_TAC[REAL_SUB_LT; REAL_LT_SUB_LADD; REAL_ADD_SYM; REAL_LET_TRANS;
            MATRIX_DIST_TRIANGLE_ALT]);;
            
let MATRIX_BALL_SUBSET_CBALL = prove
 (`!x:real^N^M e. matrix_ball(x,e) SUBSET matrix_cball(x,e)`,
  REWRITE_TAC[IN_MATRIX_BALL; IN_MATRIX_CBALL; SUBSET] THEN REAL_ARITH_TAC);;
  
let MATRIX_OPEN_CONTAINS_CBALL = prove
 (`!s:real^N^M->bool. matrix_open s <=> 
            !x. x IN s ==> ?e. &0 < e /\ matrix_cball(x,e) SUBSET s`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_OPEN_CONTAINS_BALL] THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SUBSET_TRANS; MATRIX_BALL_SUBSET_CBALL]] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[SUBSET; IN_MATRIX_BALL; IN_MATRIX_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  SUBGOAL_THEN `e / &2 < e` (fun th -> ASM_MESON_TAC[th; REAL_LET_TRANS]) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;
  
let matrix_open_in = prove
 (`!u s:real^N^M->bool.
        open_in (subtopology matrix_space u) s <=>
          s SUBSET u /\
          !x. x IN s ==> ?e. &0 < e /\
                             !x'. x' IN u /\ matrix_dist(x',x) < e ==> x' IN s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; GSYM MATRIX_OPEN_IN] THEN EQ_TAC THENL
   [REWRITE_TAC[matrix_open] THEN ASM SET_TAC[INTER_SUBSET; IN_INTER];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `d:real^N^M->real`) THEN
  EXISTS_TAC `UNIONS {b | ?x:real^N^M. (b = matrix_ball(x,d x)) /\ x IN s}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MATRIX_OPEN_UNIONS THEN
    ASM_SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; MATRIX_OPEN_BALL];
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_MESON_TAC[SUBSET; MATRIX_DIST_REFL; MATRIX_DIST_SYM; IN_MATRIX_BALL]]);;
  
(* ------------------------------------------------------------------------- *)
(* The definition and properties of the limit of matrix series               *)
(* ------------------------------------------------------------------------- *)
  
make_overloadable "->->" `:A->B->C->bool`;;

overload_interface ("->->",` rmatrixtendsto:(A->real^N^M)->real^N^M->(A)net->bool`);;

overload_interface ("->->",` cmatrixtendsto:(A->complex^N^M)->complex^N^M->(A)net->bool`);;

parse_as_infix("->->",(12,"right"));;

let rmatrixtendsto = new_definition
    `((f:A->real^N^M) ->-> l) net <=> !e. &0 < e ==> 
            eventually (\x. matrix_dist(f(x),l) < e) net`;;

let cmatrixtendsto = new_definition
  `((f:A->complex^N^M) ->-> l) net <=> !e. &0 < e ==> 
            eventually (\x. matrix_dist(f(x),l) < e) net`;;

let matrixtendsto = prove
    (`(!f l net. ((f:A->real^N^M) ->-> l) net <=> !e. &0 < e ==> 
            eventually (\x. matrix_dist(f(x),l) < e) net) /\
    (!f l net. ((f:A->complex^N^M) ->-> l) net <=> !e. &0 < e ==> 
            eventually (\x. matrix_dist(f(x),l) < e) net)`,
    SIMP_TAC[rmatrixtendsto;cmatrixtendsto]);;
  
make_overloadable "matrix_lim" `:A->B->C`;;

overload_interface ("matrix_lim",` rmatrix_lim:(A)net->(A->real^N^M)->real^N^M`);;

overload_interface ("matrix_lim",` cmatrix_lim:(A)net->(A->complex^N^M)->complex^N^M`);;
  
let rmatrix_lim = new_definition  
    `! (f:A->real^N^M) net. rmatrix_lim net f = (@l. (f ->-> l) net)`;;
    
let cmatrix_lim = new_definition  
    `! (f:A->complex^N^M) net. cmatrix_lim net f = (@l. (f ->-> l) net)`;;
    
let matrix_lim = prove  
    (`(!(f:A->real^N^M) net. rmatrix_lim net f = (@l. (f ->-> l) net)) /\ (!(f:A->complex^N^M) net. cmatrix_lim net f = (@l. (f ->-> l) net))`,
    SIMP_TAC[rmatrix_lim;cmatrix_lim]);;

(* properties of real matrix entries*)
    
let LIMIT_MATRIX_SPACE = prove
    (`!f:A->real^N^M x net. limit matrix_space f x net <=> (f ->-> x) net`,
    REWRITE_TAC[LIMIT_METRIC; GSYM MTOPOLOGY_MATRIX_SPACE_METRIC] THEN
    REWRITE_TAC[MATRIX_SPACE_METRIC; IN_UNIV; matrixtendsto]);;
  
let MATRIX_LIM_UNIQUE = prove
    (`!net:(A)net f:A->real^N^M l:real^N^M l'.
      ~(trivial_limit net) /\ (f ->-> l) net /\ (f ->-> l') net ==> (l = l')`,
    REWRITE_TAC[GSYM LIMIT_MATRIX_SPACE; GSYM MTOPOLOGY_MATRIX_SPACE_METRIC] THEN
    REWRITE_TAC[LIMIT_METRIC_UNIQUE]);;
  
let MATRIX_LIM_SEQUENTIALLY = prove
    (`!s l:real^N^M. (s ->-> l) sequentially <=>
            !e. &0 < e ==> ?N. !n. N <= n ==> matrix_dist(s(n),l) < e`,
    REWRITE_TAC[matrixtendsto; EVENTUALLY_SEQUENTIALLY] THEN MESON_TAC[]);;

let MATRIX_LIMIT_COMPONENTWISE_REAL = prove
    (`!net (f:A->real^N^M) l.
        limit matrix_space f l net <=>
        !i j. (1 <= i /\ i <= dimindex(:M)) /\ (1 <= j /\ j <= dimindex(:N))
            ==> limit euclideanreal (\x. f x$i$j) (l$i$j) net`,
    let lem = prove
    (`!P. (!x y z. P x y z) <=> (!z x y. P x y z)`, METIS_TAC[]) in
    REPEAT GEN_TAC THEN
    REWRITE_TAC[GSYM MTOPOLOGY_MATRIX_SPACE_METRIC;
                GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
    REWRITE_TAC[LIMIT_METRIC; MATRIX_SPACE_METRIC; REAL_EUCLIDEAN_METRIC] THEN
    REWRITE_TAC[IN_UNIV; GSYM IN_NUMSEG] THEN
    ONCE_REWRITE_TAC[MATRIX_DIST_SYM] THEN
    EQ_TAC THENL
    [REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_SIMP_TAC[] THEN
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
     MESON_TAC[MATRIX_SUB_COMPONENT; matrix_dist; 
               REAL_LET_TRANS; COMPONENT_LE_FNORM];
     REWRITE_TAC [GSYM RIGHT_FORALL_IMP_THM] THEN 
     X_GEN_TAC `e:real` THEN 
     ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`] THEN 
     STRIP_TAC THEN ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`] THEN 
     REWRITE_TAC [IMP_CONJ] THEN ONCE_REWRITE_TAC [lem] THEN
     REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN 
     SIMP_TAC[FORALL_EVENTUALLY; FINITE_NUMSEG; NUMSEG_EMPTY;
              NOT_LT; DIMINDEX_GE_1] THEN
     DISCH_THEN (MP_TAC o SPEC `e / (&(dimindex(:M)) * &(dimindex(:N)))`) THEN
     ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; 
                  REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1] THEN
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN 
     X_GEN_TAC `x:A` THEN SIMP_TAC[GSYM MATRIX_SUB_COMPONENT; matrix_dist] THEN 
     DISCH_TAC THEN W(MP_TAC o PART_MATCH lhand FNORM_LE_L1 o lhand o snd) THEN
     MATCH_MP_TAC(REAL_ARITH `s < e ==> n <= s ==> n < e`) THEN
     MATCH_MP_TAC SUM_SUM_BOUND_LT_GEN THEN
     ASM_SIMP_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1;
                  CARD_NUMSEG_1; GSYM IN_NUMSEG]]);;
                 
let MATRIX_VECTOR_SUB_COMPONENT = prove
    (`!A B:real^N^M i. (A - B)$i = A$i - B$i`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
    CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN 
    ASM_SIMP_TAC[matrix_sub; vector_sub; LAMBDA_BETA]);;
                 
let MATRIX_LIMIT_COMPONENTWISE_VECTOR = prove
    (`!net (f:A->real^N^M) l.
        limit matrix_space f l net <=>
        !i. 1 <= i /\ i <= dimindex(:M)
            ==> limit euclidean (\x. f x$i) (l$i) net`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[GSYM MTOPOLOGY_EUCLIDEAN_METRIC;
                GSYM MTOPOLOGY_MATRIX_SPACE_METRIC] THEN
    REWRITE_TAC[LIMIT_METRIC; EUCLIDEAN_METRIC; MATRIX_SPACE_METRIC] THEN
    REWRITE_TAC[IN_UNIV; RIGHT_IMP_FORALL_THM; GSYM IN_NUMSEG] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
    SIMP_TAC[FORALL_EVENTUALLY; FINITE_NUMSEG; NUMSEG_EMPTY;
             NOT_LT; DIMINDEX_GE_1] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL
    [FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN ASM_SIMP_TAC [] THEN
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
     X_GEN_TAC `x:A` THEN SIMP_TAC[matrix_dist; dist] THEN 
     SIMP_TAC [GSYM MATRIX_VECTOR_SUB_COMPONENT] THEN 
     METIS_TAC [VECTOR_COMPONENT_LE_FNORM; REAL_LET_TRANS];
     FIRST_X_ASSUM (MP_TAC o SPEC `e / (&(dimindex(:M)) * &(dimindex(:N)))`) THEN 
     ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; 
                  REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1] THEN 
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN BETA_TAC THEN
     REPEAT STRIP_TAC THEN SIMP_TAC [matrix_dist] THEN 
     W(MP_TAC o PART_MATCH lhand FNORM_LE_L1 o lhand o snd) THEN
     MATCH_MP_TAC(REAL_ARITH `s < e ==> n <= s ==> n < e`) THEN
     MATCH_MP_TAC SUM_SUM_BOUND_LT_GEN THEN
     ASM_SIMP_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1;
                  CARD_NUMSEG_1; GSYM IN_NUMSEG] THEN 
     REPEAT STRIP_TAC THEN 
     FIRST_X_ASSUM (MP_TAC o SPEC `k:num`) THEN 
     ASM_SIMP_TAC [dist; GSYM MATRIX_VECTOR_SUB_COMPONENT] THEN
     METIS_TAC [COMPONENT_LE_NORM; REAL_LET_TRANS]]);;
     
let MATRIX_CONTINUOUS_MAP_COMPONENTWISE_VECTOR = prove
 (`!top (f:A->real^N^M).
        continuous_map (top,matrix_space) f <=>
        !i. 1 <= i /\ i <= dimindex(:M)
            ==> continuous_map (top,euclidean) (\x. f x$i)`,
  REWRITE_TAC[CONTINUOUS_MAP_ATPOINTOF; MATRIX_LIMIT_COMPONENTWISE_VECTOR] THEN
  MESON_TAC[]);;
                         
let MATRIX_LIM_COMPONENTWISE_REAL = prove
    (`!net f:A->real^N^M l.
        (f ->-> l) net <=>
        !i j. (1 <= i /\ i <= dimindex(:M)) /\ (1 <= j /\ j <= dimindex(:N))
            ==> limit euclideanreal (\x. f x$i$j) (l$i$j) net`,
    REWRITE_TAC[GSYM LIMIT_MATRIX_SPACE; MATRIX_LIMIT_COMPONENTWISE_REAL]);;
    
let LIMIT_EQ_LIFT2 = prove
 (`!(net:A net) f l.
        limit euclideanreal f l net <=>
        limit matrix_space (lift_lift o f) (lift_lift l) net`,
  REWRITE_TAC[GSYM MTOPOLOGY_MATRIX_SPACE_METRIC;
              GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[LIMIT_METRIC; MATRIX_SPACE_METRIC;
              REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN
  REWRITE_TAC[o_THM; MATRIX_DIST_LIFT2; REAL_ABS_SUB]);;

let LIMIT_EQ_DROP2 = prove
 (`!(net:A net) f l.
        limit matrix_space f l net <=>
        limit euclideanreal (drop_drop o f) (drop_drop l) net`,
  REWRITE_TAC[LIMIT_EQ_LIFT2; o_DEF; LIFT2_DROP; ETA_AX]);;
  
let MATRIX_LIM_COMPONENTWISE_LIFT2 = prove
 (`!net f:A->real^N^M.
        (f ->-> l) net <=>
        !i j. (1 <= i /\ i <= dimindex(:M)) /\ (1 <= j /\ j <= dimindex(:N))
            ==> ((\x. lift_lift((f x)$i$j)) ->-> lift_lift(l$i$j)) net`,
  REWRITE_TAC[GSYM LIMIT_MATRIX_SPACE; LIMIT_EQ_DROP2; o_DEF; LIFT2_DROP] THEN
  REWRITE_TAC[LIMIT_MATRIX_SPACE; GSYM MATRIX_LIM_COMPONENTWISE_REAL]);;

let MATRIX_LIM_COMPONENTWISE_VECTOR = prove
    (`!net f:A->real^N^M l.
        (f ->-> l) net <=>
        !i. 1 <= i /\ i <= dimindex(:M)
            ==> limit euclidean (\x. f x$i) (l$i) net`,
    REWRITE_TAC[GSYM LIMIT_MATRIX_SPACE; MATRIX_LIMIT_COMPONENTWISE_VECTOR]);;

let MATRIX_LIM_CONST = prove
    (`!net A:real^N^M. ((\x:A. A) ->-> A) net`,
    SIMP_TAC[matrixtendsto; MATRIX_DIST_REFL; EVENTUALLY_TRUE]);;
  
let MATRIX_LIM_CMUL = prove
    (`!net:(A)net f:A->real^N^M l c. (f ->-> l) net ==> ((\x. c %% f x) ->-> c %% l) net`,
    REWRITE_TAC[MATRIX_LIM_COMPONENTWISE_REAL; MATRIX_CMUL_COMPONENT] THEN
    SIMP_TAC[LIMIT_REAL_LMUL]);;
  
let MATRIX_LIM_CMUL1 = prove
 (`!net:(A)net f l:real^N^M c d.
        ((lift_lift o c) ->-> lift_lift d) net /\ (f ->-> l) net
        ==> ((\x. c(x) %% f(x)) ->-> (d %% l)) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lift_lift; o_DEF] THEN 
  SIMP_TAC[MATRIX_LIM_COMPONENTWISE_REAL; MATRIX_CMUL_COMPONENT;
           LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LIMIT_REAL_MUL THEN 
  FIRST_X_ASSUM (MP_TAC o SPECL [`i:num`;`j:num`]) THEN
  ASM_SIMP_TAC [] THEN 
  FIRST_X_ASSUM (MP_TAC o SPECL [`1`;`1`]) THEN
  ASM_SIMP_TAC [ARITH; DIMINDEX_1; ETA_AX]);;
  
let MATRIX_LIM_CMUL_EQ = prove
 (`!net:(A)net f:A->real^N^M l c.
        ~(c = &0) ==> (((\x. c %% f x) ->-> c %% l) net <=> (f ->-> l) net)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[MATRIX_LIM_CMUL] THEN
  DISCH_THEN(MP_TAC o SPEC `inv c:real` o MATCH_MP MATRIX_LIM_CMUL) THEN
  ASM_SIMP_TAC[MATRIX_CMUL_ASSOC; REAL_MUL_LINV; MATRIX_CMUL_LID; ETA_AX]);;  
  
let MATRIX_LIM_NEG = prove
    (`!net:(A)net f:A->real^N^M l. (f ->-> l) net ==> ((\x. --(f x)) ->-> --l) net`,
    REWRITE_TAC[MATRIX_LIM_COMPONENTWISE_REAL; MATRIX_NEG_COMPONENT] THEN
    SIMP_TAC[LIMIT_REAL_NEG]);;
    
let MATRIX_LIM_NEG_EQ = prove
 (`!net:(A)net f:A->real^N^M l. ((\x. --(f x)) ->-> --l) net <=> (f ->-> l) net`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MATRIX_LIM_NEG) THEN
  REWRITE_TAC[MATRIX_NEG_NEG; ETA_AX]);;
  
let MATRIX_LIM_ADD = prove
    (`!net:(A)net f:A->real^N^M g:A->real^N^M l m.
        (f ->-> l) net /\ (g ->-> m) net ==> ((\x. f(x) + g(x)) ->-> l + m) net`,
    REWRITE_TAC[MATRIX_LIM_COMPONENTWISE_REAL; MATRIX_ADD_COMPONENT] THEN
    SIMP_TAC[LIMIT_REAL_ADD]);;
    
let MATRIX_LIM_ABS = prove
 (`!net:(A)net f:A->real^N^M l.
     (f ->-> l) net ==>
     ((\x. lambda i j. (abs(f(x)$i$j))) ->-> (lambda i j. abs(l$i$j)):real^N^M) net`,
  SIMP_TAC[MATRIX_LIM_COMPONENTWISE_REAL; LAMBDA_BETA] THEN
  SIMP_TAC[LIMIT_REAL_ABS]);;
  
let MATRIX_LIM_SUB = prove
    (`!net:(A)net f:A->real^N^M g l m.
        (f ->-> l) net /\ (g ->-> m) net ==> ((\x. f(x) - g(x)) ->-> l - m) net`,
    REWRITE_TAC[real_sub; MATRIX_SUB] THEN ASM_SIMP_TAC[MATRIX_LIM_ADD; MATRIX_LIM_NEG]);;

let MATRIX_SUB_SUB = CMATRIX_ARITH `!A B:real^N^M.(A - B) - A = --B`;;
    
let MATRIX_LIM_TRANSFORM = prove
 (`!net:(A)net f:A->real^N^M g l.
     ((\x. f x - g x) ->-> mat 0) net /\ (f ->-> l) net ==> (g ->-> l) net`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MATRIX_LIM_SUB) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MATRIX_LIM_NEG) THEN SIMP_TAC[MATRIX_SUB_SUB;MATRIX_SUB_LZERO;MATRIX_NEG_NEG] THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN BINOP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  SIMP_TAC[CART_EQ;LAMBDA_BETA]);;

let MATRIX_LIM_EVENTUALLY = prove
 (`!net:(A)net f:A->real^N^M l. eventually (\x. f x = l) net ==> (f ->-> l) net`,
  SIMP_TAC[matrixtendsto] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        EVENTUALLY_MONO)) THEN
  ASM_SIMP_TAC[MATRIX_DIST_REFL]);;
  
let MATRIX_LIM_TRANSFORM_EVENTUALLY = prove
 (`!net:(A)net f:A->real^N^M g l.
        eventually (\x. f x = g x) net /\ (f ->-> l) net ==> (g ->-> l) net`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MATRIX_SUB_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP MATRIX_LIM_EVENTUALLY) MP_TAC) THEN
  MESON_TAC[MATRIX_LIM_TRANSFORM]);;
  
let MATRIX_LIM_FNORM_UBOUND = prove
 (`!net:(A)net f (l:real^N^M) b.
      ~(trivial_limit net) /\
      (f ->-> l) net /\
      eventually (\x. fnorm(f x) <= b) net
      ==> fnorm(l) <= b`,
  let th1 = CMATRIX_ARITH `!x:real^N^M y. x = (x - y) + y` in
  let th2 = SPECL [`l:real^N^M`; `f(x:A):real^N^M`] th1 in
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISJ_CASES_TAC(REAL_ARITH `fnorm(l:real^N^M) <= b \/ b < fnorm l`) THEN
  ASM_REWRITE_TAC[matrixtendsto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `fnorm(l:real^N^M) - b`) MP_TAC) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT; IMP_IMP; GSYM EVENTUALLY_AND] THEN
  DISCH_THEN(MP_TAC o MATCH_MP EVENTUALLY_HAPPENS) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `b < fnorm(l:real^N^M)` THEN
  REWRITE_TAC [matrix_dist] THEN ONCE_REWRITE_TAC [FNORM_SUB_SYM] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[th2] THEN 
  W(MP_TAC o PART_MATCH lhand FNORM_TRIANGLE o lhand o snd) THEN
  REWRITE_TAC[GSYM th2] THEN ASM_ARITH_TAC);;
  
let MATRIX_LIM_TRIVIAL = prove
 (`!net (f:A->real^N^M) l. trivial_limit net ==> (f ->-> l) net`,
  SIMP_TAC[GSYM LIMIT_MATRIX_SPACE; LIMIT_TRIVIAL; 
           TOPSPACE_MATRIX_SPACE; IN_UNIV]);;
           
let MATRIX_LIM_MMUL = prove
 (`!net:(A)net c d v:real^N^M.
        ((lift_lift o c) ->-> lift_lift d) net 
        ==> ((\x. c(x) %% v) ->-> d %% v) net`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_LIM_CMUL1 THEN 
  ASM_REWRITE_TAC[MATRIX_LIM_CONST]);;
  
let MATRIX_LIM_NULL = prove
 (`!net f l:real^N^M. (f ->-> l) net <=> ((\x. f(x) - l) ->-> mat 0) net`,
  REWRITE_TAC[matrixtendsto; matrix_dist; MATRIX_SUB_RZERO]);;    

(* ------------------------------------------------------------------------- *)
(* limit point of matrix space                                               *)
(* ------------------------------------------------------------------------- *)

make_overloadable "matrix_limit_point_of" `:A->B->C`;;

overload_interface ("matrix_limit_point_of",` rmatrix_limit_point_of:real^N^M->(real^N^M->bool)->bool`);;

overload_interface ("matrix_limit_point_of",` cmatrix_limit_point_of:complex^N^M->(complex^N^M->bool)->bool`);;

parse_as_infix ("matrix_limit_point_of",(12,"right"));;

let rmatrix_limit_point_of = new_definition
 `!x:real^N^M. x matrix_limit_point_of s <=>
        !t. x IN t /\ matrix_open t ==> ?y. ~(y = x) /\ y IN s /\ y IN t`;;
        
let cmatrix_limit_point_of = new_definition
 `!x:complex^N^M. x matrix_limit_point_of s <=>
        !t. x IN t /\ matrix_open t ==> ?y. ~(y = x) /\ y IN s /\ y IN t`;;
        
let matrix_limit_point_of = prove
    (`(!x:real^N^M s. x matrix_limit_point_of s <=>
        !t. x IN t /\ matrix_open t ==> ?y. ~(y = x) /\ y IN s /\ y IN t) /\
    (!x:complex^N^M s. x matrix_limit_point_of s <=>
        !t. x IN t /\ matrix_open t ==> ?y. ~(y = x) /\ y IN s /\ y IN t)`,
    SIMP_TAC[rmatrix_limit_point_of;cmatrix_limit_point_of]);;
    
(* properties of real matrix entries*)
        
let MATRIX_LIMPT_APPROACHABLE = prove
 (`!x:real^N^M s. x matrix_limit_point_of s <=>
                !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ matrix_dist(x',x) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_limit_point_of] THEN
  MESON_TAC[matrix_open; MATRIX_DIST_SYM; OPEN_MATRIX_BALL; 
            CENTRE_IN_MATRIX_BALL; IN_MATRIX_BALL]);;

let [MATRIX_LIMPT_SEQUENTIAL; MATRIX_LIMPT_SEQUENTIAL_INJ; 
     MATRIX_LIMPT_SEQUENTIAL_DECREASING] =
  (CONJUNCTS o prove)
  (`(!x:real^N^M s.
        x matrix_limit_point_of s <=>
        ?f. (!n. f(n) IN (s DELETE x)) /\ (f ->-> x) sequentially) /\
    (!x:real^N^M s.
        x matrix_limit_point_of s <=>
        ?f. (!n. f(n) IN (s DELETE x)) /\
            (!m n. f m = f n <=> m = n) /\
            (f ->-> x) sequentially) /\
    (!x:real^N^M s.
        x matrix_limit_point_of s <=>
        ?f. (!n. f(n) IN (s DELETE x)) /\
            (!m n. m < n ==> matrix_dist(f n,x) < matrix_dist(f m,x)) /\
            (f ->-> x) sequentially)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT
   `(s ==> r) /\ (r ==> q) /\ (q ==> p) /\ (p ==> s)
    ==> (p <=> q) /\ (p <=> r) /\ (p <=> s)`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:num->real^N^M` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WLOG_LT THEN ASM_MESON_TAC[REAL_LT_REFL];
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    REWRITE_TAC[MATRIX_LIMPT_APPROACHABLE; MATRIX_LIM_SEQUENTIALLY; IN_DELETE] THEN
    MESON_TAC[LE_REFL];
    REWRITE_TAC[MATRIX_LIMPT_APPROACHABLE] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?f:num->real^N^M.
        (!n. (f n) IN s /\ ~(f n = x) /\ matrix_dist(f n,x) < inv(&n + &1)) /\
       (!n. matrix_dist(f(SUC n),x) < matrix_dist(f n,x))`
    MP_TAC THENL
     [MATCH_MP_TAC DEPENDENT_CHOICE THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `z:real^N^M`] THEN
      STRIP_TAC THEN REWRITE_TAC[GSYM CONJ_ASSOC; GSYM REAL_LT_MIN] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_INV_EQ; GSYM MATRIX_DIST_NZ] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num->real^N^M` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        REWRITE_TAC[MATRIX_LIM_SEQUENTIALLY] THEN MATCH_MP_TAC FORALL_POS_MONO_1 THEN
        CONJ_TAC THENL [MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
        X_GEN_TAC `N:num` THEN EXISTS_TAC `N:num` THEN
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        TRANS_TAC REAL_LTE_TRANS `inv(&n + &1)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN
        ASM_ARITH_TAC]]]);;

let MATRIX_SPACE_DERIVED_SET_OF_IFF_LIMIT_POINT_OF = prove
  (`!s. matrix_space derived_set_of s = 
                          {x:real^N^M | x matrix_limit_point_of s}`,
   GEN_TAC THEN
   REWRITE_TAC[GSYM MTOPOLOGY_MATRIX_SPACE_METRIC; METRIC_DERIVED_SET_OF;
               MATRIX_SPACE_METRIC; IN_UNIV; matrix_limit_point_of; EXTENSION;
               IN_ELIM_THM; MBALL_MATRIX_SPACE] THEN
   GEN_TAC THEN EQ_TAC THENL
   [INTRO_TAC "hp; !t; x t" THEN HYP_TAC "t" (REWRITE_RULE[matrix_open]) THEN
    HYP_TAC "t: @r. r t" (C MATCH_MP (ASSUME `x:real^N^M IN t`)) THEN
    HYP_TAC "hp: @y. neq y matrix_dist" (C MATCH_MP (ASSUME `&0 < r`)) THEN
    EXISTS_TAC `y:real^N^M` THEN HYP REWRITE_TAC "neq y" [] THEN
    REMOVE_THEN "t" MATCH_MP_TAC THEN REMOVE_THEN "matrix_dist" MP_TAC THEN
    REWRITE_TAC[IN_MATRIX_BALL; MATRIX_DIST_SYM];
    INTRO_TAC "hp; !r; r" THEN REMOVE_THEN "hp" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_MATRIX_BALL; OPEN_MATRIX_BALL]]);;

let MATRIX_LIMIT_POINT_IN_DERIVED_SET = prove
 (`!s x:real^N^M. x matrix_limit_point_of s <=> 
                  x IN matrix_space derived_set_of s`,
  REWRITE_TAC[MATRIX_SPACE_DERIVED_SET_OF_IFF_LIMIT_POINT_OF; IN_ELIM_THM]);;
  
let MATRIX_CLOSED_LIMPT = prove
 (`!s:real^N^M->bool. matrix_closed s <=> !x. x matrix_limit_point_of s ==> x IN s`,
  REWRITE_TAC[matrix_closed] THEN ONCE_REWRITE_TAC[MATRIX_OPEN_SUBOPEN] THEN
  REWRITE_TAC[matrix_limit_point_of; IN_DIFF; IN_UNIV; SUBSET] THEN MESON_TAC[]);;

(*
let MATRIX_CLOSED_SEQUENTIAL_LIMITS = prove
 (`!s:real^M^N->bool. matrix_closed s <=>
       !x l. (!n. x(n) IN s) /\ (x ->-> l) sequentially ==> l IN s`,
  MESON_TAC[MATRIX_CLOSURE_SEQUENTIAL; MATRIX_CLOSURE_CLOSED;
            MATRIX_CLOSED_LIMPT; MATRIX_LIMPT_SEQUENTIAL; IN_DELETE]);;
  
let MATRIX_CLOSED_CBALL = prove
 (`!x:real^N^M e. matrix_closed(matrix_cball(x,e))`,
  REWRITE_TAC[MATRIX_CLOSED_SEQUENTIAL_LIMITS; IN_MATRIX_CBALL; matrix_dist] THEN
  GEN_TAC THEN GEN_TAC THEN X_GEN_TAC `s:num->real^N^M` THEN
  X_GEN_TAC `y:real^N^M` THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` MATRIX_LIM_FNORM_UBOUND) THEN
  EXISTS_TAC `\n. x - (s:num->real^N^M) n` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  ASM_SIMP_TAC[MATRIX_LIM_SUB; MATRIX_LIM_CONST; SEQUENTIALLY] THEN 
  MESON_TAC[GE_REFL]);;
*)

(* ------------------------------------------------------------------------- *)
(* Interior of a matrix set.                                                 *)
(* ------------------------------------------------------------------------- *)

make_overloadable "matrix_interior" `:A->A`;;

overload_interface ("matrix_interior",` rmatrix_interior:(real^N^M->bool)->(real^N^M->bool)`);;

overload_interface ("matrix_interior",` cmatrix_interior:(complex^N^M->bool)->(complex^N^M->bool)`);;

let rmatrix_interior = new_definition
  `rmatrix_interior (s:real^N^M->bool) = {x | ?t. matrix_open t /\ x IN t /\ t SUBSET s}`;;
  
let cmatrix_interior = new_definition
  `cmatrix_interior (s:complex^N^M->bool) = {x | ?t. matrix_open t /\ x IN t /\ t SUBSET s}`;;
  
let matrix_interior = prove
  (`(!s. rmatrix_interior (s:real^N^M->bool) = {x | ?t. matrix_open t /\ x IN t /\ t SUBSET s}) /\
  (!s. cmatrix_interior (s:complex^N^M->bool) = {x | ?t. matrix_open t /\ x IN t /\ t SUBSET s})`,
  SIMP_TAC[rmatrix_interior;cmatrix_interior]);;
  
let MATRIX_SPACE_INTERIOR_OF = prove
 (`!s:real^N^M->bool. matrix_space interior_of s = matrix_interior s`,
  REWRITE_TAC[interior_of; matrix_interior; MATRIX_OPEN_IN]);;
  
let MATRIX_INTERIOR_EQ = prove
 (`!s:real^N^M->bool. (matrix_interior s = s) <=> matrix_open s`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; matrix_interior; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [MATRIX_OPEN_SUBOPEN] THEN MESON_TAC[SUBSET]);;
  
let MATRIX_OPEN_INTERIOR = prove
 (`!s:real^N^M->bool. matrix_open(matrix_interior s)`,
  GEN_TAC THEN REWRITE_TAC[matrix_interior] THEN 
  GEN_REWRITE_TAC I [MATRIX_OPEN_SUBOPEN] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;
  
let MATRIX_INTERIOR_OPEN = prove
 (`!s:real^N^M->bool. matrix_open s ==> (matrix_interior s = s)`,
  MESON_TAC[MATRIX_INTERIOR_EQ]);;
  
let MATRIX_INTERIOR_EMPTY = prove
 (`matrix_interior ({}:real^N^M->bool) = {}`,
  SIMP_TAC[MATRIX_INTERIOR_OPEN;MATRIX_OPEN_EMPTY]);;
  
let MATRIX_INTERIOR_SUBSET = prove
 (`!s:real^N^M->bool. (matrix_interior s) SUBSET s`,
  REWRITE_TAC[SUBSET; matrix_interior; IN_ELIM_THM] THEN MESON_TAC[]);;
  
let MATRIX_INTERIOR_MAXIMAL = prove
 (`!s t:real^N^M->bool. t SUBSET s /\ matrix_open t ==> t SUBSET (matrix_interior s)`,
  REWRITE_TAC[matrix_interior; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;
  
let MATRIX_INTERIOR_UNIQUE = prove
 (`!s t:real^N^M->bool. t SUBSET s /\ matrix_open t /\ 
         (!t'. t' SUBSET s /\ matrix_open t' ==> t' SUBSET t)
         ==> (matrix_interior s = t)`,
  MESON_TAC[SUBSET_ANTISYM; MATRIX_INTERIOR_MAXIMAL; MATRIX_INTERIOR_SUBSET;
            MATRIX_OPEN_INTERIOR]);;
            
let IN_MATRIX_INTERIOR = prove
 (`!x s:real^N^M->bool. x IN matrix_interior s <=> ?e. &0 < e /\ matrix_ball(x,e) SUBSET s`,
  REWRITE_TAC[matrix_interior; IN_ELIM_THM] THEN
  MESON_TAC[MATRIX_OPEN_CONTAINS_BALL; SUBSET_TRANS; 
            CENTRE_IN_MATRIX_BALL; MATRIX_OPEN_BALL]);;
  
let MATRIX_INTERIOR_CBALL = prove
 (`!x:real^N^M e. matrix_interior(matrix_cball(x,e)) = matrix_ball(x,e)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 <= e` THENL
   [ALL_TAC;
    SUBGOAL_THEN `matrix_cball(x:real^N^M,e) = {} /\ 
                  matrix_ball(x:real^N^M,e) = {}`
     (fun th -> REWRITE_TAC[th; MATRIX_INTERIOR_EMPTY]) THEN
    REWRITE_TAC[IN_MATRIX_BALL; IN_MATRIX_CBALL; EXTENSION; NOT_IN_EMPTY] THEN
    CONJ_TAC THEN X_GEN_TAC `y:real^N^M` THEN
    MP_TAC(ISPECL [`x:real^N^M`; `y:real^N^M`] MATRIX_DIST_POS_LE) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC MATRIX_INTERIOR_UNIQUE THEN
  REWRITE_TAC[MATRIX_BALL_SUBSET_CBALL; MATRIX_OPEN_BALL] THEN
  X_GEN_TAC `t:real^N^M->bool` THEN
  SIMP_TAC[SUBSET; IN_MATRIX_CBALL; IN_MATRIX_BALL; 
           REAL_LT_LE] THEN STRIP_TAC THEN
  X_GEN_TAC `z:real^N^M` THEN DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N^M` o GEN_REWRITE_RULE I [matrix_open]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `z:real^N^M = x` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `k:real` o MATCH_MP REAL_DOWN) THEN
    SUBGOAL_THEN `?w:real^N^M. matrix_dist(w,x) = k` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MATRIX_CHOOSE_DIST; MATRIX_DIST_SYM; REAL_LT_IMP_LE];
      ASM_MESON_TAC[REAL_NOT_LE; MATRIX_DIST_REFL; MATRIX_DIST_SYM]];
    RULE_ASSUM_TAC(REWRITE_RULE[MATRIX_DIST_NZ]) THEN
    DISCH_THEN(MP_TAC o SPEC 
    `z + ((d / &2) / matrix_dist(z,x)) %% (z - x:real^N^M)`) THEN
    REWRITE_TAC[matrix_dist; MATRIX_ADD_SUB; FNORM_MUL; REAL_ABS_DIV;
                REAL_ABS_FNORM; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; GSYM matrix_dist; REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    ASM_REWRITE_TAC[REAL_ARITH `abs d < d * &2 <=> &0 < d`] THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[matrix_dist] THEN
    REWRITE_TAC[CMATRIX_ARITH 
                `(x:real^N^M) - (z + k %% (z - x)) = (&1 + k) %% (x - z)`] THEN
    REWRITE_TAC[REAL_NOT_LE; FNORM_MUL] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[FNORM_SUB_SYM] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ; GSYM matrix_dist] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &1 < abs(&1 + x)`) THEN
    ONCE_REWRITE_TAC[MATRIX_DIST_SYM] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH]]);;

(* ------------------------------------------------------------------------- *)
(* Closure of a set in matrix space                                                        *)
(* ------------------------------------------------------------------------- *)

make_overloadable "matrix_closure" `:A->A`;;

overload_interface ("matrix_closure",` rmatrix_closure:(real^N^M->bool)->(real^N^M->bool)`);;

overload_interface ("matrix_closure",` cmatrix_closure:(complex^N^M->bool)->(complex^N^M->bool)`);;

let rmatrix_closure = new_definition
  `rmatrix_closure s = s UNION {x:real^N^M | x matrix_limit_point_of s}`;;
  
let cmatrix_closure = new_definition
  `cmatrix_closure s = s UNION {x:complex^N^M | x matrix_limit_point_of s}`;;
  
let matrix_closure = prove
    (`(!s. rmatrix_closure s = s UNION {x:real^N^M | x matrix_limit_point_of s}) /\
    (!s. cmatrix_closure s = s UNION {x:complex^N^M | x matrix_limit_point_of s})`,
    SIMP_TAC[rmatrix_closure;cmatrix_closure]);;
  
let MATRIX_SPACE_CLOSURE_OF = prove
  (`!s:real^N^M->bool. matrix_space closure_of s = matrix_closure s`,
   GEN_TAC THEN
   REWRITE_TAC[matrix_closure; CLOSURE_OF; TOPSPACE_MATRIX_SPACE; INTER_UNIV;
               MATRIX_SPACE_DERIVED_SET_OF_IFF_LIMIT_POINT_OF]);;
  
let MATRIX_CLOSURE_INTERIOR = prove
 (`!s:real^N^M->bool. matrix_closure s = UNIV DIFF (matrix_interior (UNIV DIFF s))`,
  REWRITE_TAC[EXTENSION; matrix_closure; IN_UNION; IN_DIFF; IN_UNIV; matrix_interior;
              IN_ELIM_THM; matrix_limit_point_of; SUBSET] THEN
  MESON_TAC[]);;
  
let MATRIX_CLOSED_CLOSURE = prove
 (`!s:real^N^M->bool. matrix_closed(matrix_closure s)`,
  REWRITE_TAC[matrix_closed; MATRIX_CLOSURE_INTERIOR; 
              COMPL_COMPL; MATRIX_OPEN_INTERIOR]);;
  
let MATRIX_CLOSURE_SEQUENTIAL = prove
 (`!s l:real^N^M.
     l IN matrix_closure(s) <=> ?x. (!n. x(n) IN s) /\ (x ->-> l) sequentially`,
  REWRITE_TAC[matrix_closure; IN_UNION; MATRIX_LIMPT_SEQUENTIAL; 
              IN_ELIM_THM; IN_DELETE] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
    `((b ==> c) /\ (~a /\ c ==> b)) /\ (a ==> c) ==> (a \/ b <=> c)`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  EXISTS_TAC `\n:num. l:real^N^M` THEN
  ASM_REWRITE_TAC[MATRIX_LIM_CONST]);;
  
let MATRIX_CLOSURE_HULL = prove
 (`!s:real^N^M->bool. matrix_closure s = matrix_closed hull s`,
  GEN_TAC THEN MATCH_MP_TAC(GSYM HULL_UNIQUE) THEN
  REWRITE_TAC[MATRIX_CLOSED_CLOSURE; SUBSET] THEN
  REWRITE_TAC[matrix_closure; IN_UNION; IN_ELIM_THM; MATRIX_CLOSED_LIMPT] THEN
  MESON_TAC[matrix_limit_point_of]);;
  
let MATRIX_CLOSURE_EQ = prove
 (`!s:real^N^M->bool. (matrix_closure s = s) <=> matrix_closed s`,
  SIMP_TAC[MATRIX_CLOSURE_HULL; HULL_EQ; MATRIX_CLOSED_INTERS]);;
  
let MATRIX_CLOSURE_CLOSED = prove
 (`!s:real^N^M->bool. matrix_closed s ==> (matrix_closure s = s)`,
  MESON_TAC[MATRIX_CLOSURE_EQ]);;
  
let MATRIX_CLOSURE_EMPTY = prove
 (`matrix_closure {}:real^N^M->bool = {}`,
  SIMP_TAC[MATRIX_CLOSURE_CLOSED; MATRIX_CLOSED_EMPTY]);;
  
let MATRIX_CLOSURE_SUBSET = prove
 (`!s:real^N^M->bool. s SUBSET (matrix_closure s)`,
  REWRITE_TAC[MATRIX_CLOSURE_HULL; HULL_SUBSET]);;
  
let MATRIX_CLOSURE_MINIMAL = prove
 (`!s t:real^N^M->bool. s SUBSET t /\ matrix_closed t ==> (matrix_closure s) SUBSET t`,
  REWRITE_TAC[HULL_MINIMAL; MATRIX_CLOSURE_HULL]);;
  
let MATRIX_CLOSED_SEQUENTIAL_LIMITS = prove
 (`!s:real^M^N->bool. matrix_closed s <=>
       !x l. (!n. x(n) IN s) /\ (x ->-> l) sequentially ==> l IN s`,
  MESON_TAC[MATRIX_CLOSURE_SEQUENTIAL; MATRIX_CLOSURE_CLOSED;
            MATRIX_CLOSED_LIMPT; MATRIX_LIMPT_SEQUENTIAL; IN_DELETE]);;

(* ------------------------------------------------------------------------- *)
(* Useful nets in matrix space.                                              *)
(* ------------------------------------------------------------------------- *)

make_overloadable "matrix_at" `:A->B`;;

overload_interface ("matrix_at",` rmatrix_at:real^N^M->(real^N^M)net`);;

overload_interface ("matrix_at",` cmatrix_at:complex^N^M->(complex^N^M)net`);;

let rmatrix_at = new_definition
  `rmatrix_at (a:real^N^M) = atpointof matrix_space a`;;
  
let cmatrix_at = new_definition
  `cmatrix_at (a:complex^N^M) = atpointof matrix_space a`;;
  
let matrix_at = prove
    (`(!a. rmatrix_at a = atpointof matrix_space a) /\
    (!a. cmatrix_at a = atpointof matrix_space a)`,
    SIMP_TAC[rmatrix_at;cmatrix_at]);;
    
(* properties of real matrix entries*)
  
let MATRIX_NETLIMIT_AT = prove
 (`!a:real^N^M. netlimit(matrix_at a) = a`,
  REWRITE_TAC[matrix_at; NETLIMIT_ATPOINTOF]);;
  
let MATRIX_NETLIMIT_WITHIN = prove
 (`!a:real^N^M s. netlimit (matrix_at a within s) = a`,
  REWRITE_TAC[netlimit; NETLIMITS_WITHIN] THEN
   REWRITE_TAC[GSYM netlimit] THEN REWRITE_TAC[MATRIX_NETLIMIT_AT]);;
   
let MATRIX_EVENTUALLY_WITHIN = prove
 (`!s a:real^N^M p.
     eventually p (matrix_at a within s) <=>
        ?d. &0 < d /\ !x. x IN s /\ &0 < matrix_dist(x,a) 
             /\ matrix_dist(x,a) < d ==> p(x)`,
  REWRITE_TAC[matrix_at; EVENTUALLY_WITHIN_IMP; GSYM MTOPOLOGY_MATRIX_SPACE_METRIC] THEN
  REWRITE_TAC[EVENTUALLY_ATPOINTOF_METRIC] THEN
  REWRITE_TAC[MATRIX_SPACE_METRIC; IN_UNIV] THEN MESON_TAC[]);;
   
let MATRIX_LIM_WITHIN = prove
 (`!f:real^N^M->real^Q^P l a s.
      (f ->-> l) (matrix_at a within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x. x IN s /\ &0 < matrix_dist(x,a) 
                               /\ matrix_dist(x,a) < d
                    ==> matrix_dist(f(x),l) < e`,
  REWRITE_TAC[matrixtendsto; MATRIX_EVENTUALLY_WITHIN] THEN MESON_TAC[]);;
  
let MATRIX_WITHIN_UNIV = prove
 (`!x:real^N^M. matrix_at x within UNIV = matrix_at x`,
  REWRITE_TAC[NET_WITHIN_UNIV]);;
  
let MATRIX_EVENTUALLY_AT = prove
 (`!a:real^N^M p. eventually p (matrix_at a) <=>
    ?d. &0 < d /\ !x. &0 < matrix_dist(x,a) /\ matrix_dist(x,a) < d ==> p(x)`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  REWRITE_TAC[MATRIX_EVENTUALLY_WITHIN; IN_UNIV]);;
  
let MATRIX_LIM_AT = prove
 (`!f l:real^N^M a:real^Q^P.
      (f ->-> l) (matrix_at a) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\ !x. &0 < matrix_dist(x,a) /\ matrix_dist(x,a) < d
                    ==> matrix_dist(f(x),l) < e`,
  REWRITE_TAC[matrixtendsto; MATRIX_EVENTUALLY_AT] THEN MESON_TAC[]);;
  
let MATRIX_EVENTUALLY_AT_ZERO = prove
 (`!P:real^N^M->bool a:real^N^M.
        eventually P (matrix_at a) 
        <=> eventually (\x. P(a + x)) (matrix_at (mat 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MATRIX_EVENTUALLY_AT] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `&0 < d` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:real^N^M` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a + x:real^N^M`) THEN
    SIMP_TAC[matrix_dist; MATRIX_ADD_SUB; MATRIX_SUB_RZERO];
    FIRST_X_ASSUM(MP_TAC o SPEC `x - a:real^N^M`) THEN
    REWRITE_TAC[matrix_dist; MATRIX_SUB_RZERO; MATRIX_SUB_ADD2]]);;
  
let MATRIX_LIM_AT_WITHIN = prove
 (`!f:real^N^M->real^P^Q l a s. (f ->-> l)(matrix_at a) ==> (f ->-> l)(matrix_at a within s)`,
  REWRITE_TAC[MATRIX_LIM_AT; MATRIX_LIM_WITHIN] THEN MESON_TAC[]);;
  
let MATRIX_LIM_AT_ZERO = prove
 (`!f:real^M^N->real^Q^P l a.
        (f ->-> l) (matrix_at a) <=> ((\x. f(a + x)) ->-> l) (matrix_at(mat 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrixtendsto] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MATRIX_EVENTUALLY_AT_ZERO] THEN
  REWRITE_TAC[]);;
  
let MATRIX_EVENTUALLY_WITHIN = prove
 (`!s a:real^M^N p.
     eventually p (matrix_at a within s) <=>
        ?d. &0 < d /\ !x. x IN s /\ &0 < matrix_dist(x,a) /\ 
              matrix_dist(x,a) < d ==> p(x)`,
  REWRITE_TAC[matrix_at; EVENTUALLY_WITHIN_IMP; 
              GSYM MTOPOLOGY_MATRIX_SPACE_METRIC] THEN
  REWRITE_TAC[EVENTUALLY_ATPOINTOF_METRIC] THEN
  REWRITE_TAC[MATRIX_SPACE_METRIC; IN_UNIV] THEN MESON_TAC[]);;
  
(*
let IN_MATRIX_INTERIOR_EVENTUALLY = prove
 (`!s a:real^N^M. a IN matrix_interior s <=>
                  a IN s /\ eventually (\x. x IN s) (matrix_at a)`,
  REWRITE_TAC[IN_MATRIX_INTERIOR; MATRIX_EVENTUALLY_AT; SUBSET; 
              IN_MATRIX_BALL; GSYM MATRIX_DIST_NZ] THEN
  MESON_TAC[MATRIX_DIST_SYM; MATRIX_DIST_REFL]);;
    
let MATRIX_EVENTUALLY_WITHIN_INTERIOR = prove
 (`!p s x:real^N^M.
        x IN matrix_interior s
        ==> (eventually p (matrix_at x within s) <=> eventually p (matrix_at x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MATRIX_INTERIOR_EVENTUALLY] THEN
  MATCH_MP_TAC(TAUT
   `(p /\ q ==> r) /\ (p /\ r ==> q) ==> p' /\ p ==> (q <=> r)`) THEN
  REWRITE_TAC[GSYM EVENTUALLY_AND; EVENTUALLY_WITHIN_IMP] THEN
  CONJ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  SIMP_TAC[]);;
    
let MATRIX_EVENTUALLY_WITHIN_OPEN = prove
 (`!f l a:real^M^N s.
        a IN s /\ matrix_open s
        ==> (eventually P (matrix_at a within s) <=> eventually P (matrix_at a))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MATRIX_EVENTUALLY_WITHIN_INTERIOR THEN
  ASM_MESON_TAC[MATRIX_INTERIOR_OPEN]);;
  
let MATRIX_EVENTUALLY_WITHIN_OPEN_IN = prove
 (`!P a s t:real^M^N->bool.
         a IN t /\ open_in (subtopology matrix_space s) t ==> 
  (eventually P (matrix_at a within t) <=> eventually P (matrix_at a within s))`,
  REWRITE_TAC[MATRIX_OPEN_IN_OPEN] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[EVENTUALLY_WITHIN_IMP] THEN ONCE_REWRITE_TAC[SET_RULE
   `x IN s INTER t ==> P <=> x IN t ==> x IN s ==> P`] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM EVENTUALLY_WITHIN_IMP] THEN
  MATCH_MP_TAC MATRIX_EVENTUALLY_WITHIN_OPEN THEN ASM SET_TAC[]);;

let MATRIX_LIM_WITHIN_OPEN = prove
 (`!f l a:real^M^N s.
     a IN s /\ matrix_open s ==> ((f ->-> l) (matrix_at a within s) 
        <=> (f ->-> l) (matrix_at a))`,
  SIMP_TAC[matrixtendsto; MATRIX_EVENTUALLY_WITHIN_OPEN]);;

let MATRIX_LIM_WITHIN_OPEN_IN = prove
 (`!f:real^M^N->real^Q^P l a s t.
        a IN t /\ open_in (subtopology matrix_space s) t ==> 
    ((f ->-> l) (matrix_at a within t) <=> (f ->-> l) (matrix_at a within s))`,
  REWRITE_TAC[matrixtendsto] THEN 
  MESON_TAC[MATRIX_EVENTUALLY_WITHIN_OPEN_IN]);;
*)

(* ------------------------------------------------------------------------- *)
(* Compactness of the matrix space 
       (the definition is the one based on convegent subsequences).          *)
(* ------------------------------------------------------------------------- *)

make_overloadable "matrix_compact" `:A->bool`;;

overload_interface ("matrix_compact",` rmatrix_compact:(real^N^M->bool)->bool`);;

overload_interface ("matrix_compact",` cmatrix_compact:(complex^N^M->bool)->bool`);;
  
let rmatrix_compact = new_definition
  `rmatrix_compact s <=>
        !f:num->real^N^M.
            (!n. f(n) IN s)
            ==> ?l r. l IN s /\ (!m n:num. m < n ==> r(m) < r(n)) /\
                      ((f o r) ->-> l) sequentially`;;
                      
let cmatrix_compact = new_definition
  `cmatrix_compact s <=>
        !f:num->complex^N^M.
            (!n. f(n) IN s)
            ==> ?l r. l IN s /\ (!m n:num. m < n ==> r(m) < r(n)) /\
                      ((f o r) ->-> l) sequentially`;;

let matrix_compact = prove
    (`(!s. rmatrix_compact s <=>
        !f:num->real^N^M.
            (!n. f(n) IN s)
            ==> ?l r. l IN s /\ (!m n:num. m < n ==> r(m) < r(n)) /\
                      ((f o r) ->-> l) sequentially) /\
    (!s. cmatrix_compact s <=>
        !f:num->complex^N^M.
            (!n. f(n) IN s)
            ==> ?l r. l IN s /\ (!m n:num. m < n ==> r(m) < r(n)) /\
                      ((f o r) ->-> l) sequentially)`,
    SIMP_TAC[rmatrix_compact;cmatrix_compact]);;

(* properties of real matrix entries*)
                                            
let MATRIX_COMPACT_EMPTY = prove
 (`matrix_compact ({}:real^N^M->bool)`,
  REWRITE_TAC[matrix_compact; NOT_IN_EMPTY]);;
                      
let COMPACT_IN_MATRIX_SPACE = prove
 (`!s:real^N^M->bool. compact_in matrix_space s <=> matrix_compact s`,
  REWRITE_TAC[matrix_compact; GSYM LIMIT_MATRIX_SPACE] THEN
  REWRITE_TAC[GSYM MTOPOLOGY_MATRIX_SPACE_METRIC; COMPACT_IN_SEQUENTIALLY] THEN
  REWRITE_TAC[matrix_compact; MATRIX_SPACE_METRIC; SUBSET_UNIV]);;
  
let COMPACT_MATRIX_INTERVAL = prove
 (`!a b:real^N^M. matrix_compact(matrix_interval[a,b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM COMPACT_IN_MATRIX_SPACE] THEN
  SUBGOAL_THEN
    `matrix_interval[a:real^N^M,b] = IMAGE (\x. lambda i. x i)
(cartesian_product (1..dimindex(:M)) (\i. interval [a$i,b$i]))`    
 SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!g. (!x. x IN s ==> f x IN t) /\ (!y. y IN t ==> g y IN s /\ f(g y) = y)
          ==> t = IMAGE f s`) THEN
    EXISTS_TAC `\(x:real^N^M) i. if i IN 1..dimindex(:M) then x$i else ARB` THEN
    REWRITE_TAC[cartesian_product; IN_ELIM_THM; EXTENSIONAL] THEN
    SIMP_TAC[IN_MATRIX_INTERVAL; LAMBDA_BETA; IN_INTERVAL;
             IN_NUMSEG; CART_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `product_topology (1..dimindex(:M)) 
                         (\i. (euclidean:(real^N)topology))` THEN
    SIMP_TAC[COMPACT_IN_CARTESIAN_PRODUCT;
             COMPACT_IN_EUCLIDEAN;COMPACT_INTERVAL] THEN
    SIMP_TAC [MATRIX_CONTINUOUS_MAP_COMPONENTWISE_VECTOR] THEN
    SIMP_TAC [CART_EQ; LAMBDA_BETA] THEN
    SIMP_TAC [IN_NUMSEG; TOPSPACE_EUCLIDEAN; CONTINUOUS_MAP_PRODUCT_PROJECTION]);;

let MATRIX_COMPACT_IMP_CLOSED = prove
 (`!s:real^N^M->bool. matrix_compact s ==> matrix_closed s`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_CLOSED_IN; GSYM COMPACT_IN_MATRIX_SPACE] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] COMPACT_IN_IMP_CLOSED_IN) THEN
  REWRITE_TAC[GSYM MTOPOLOGY_MATRIX_SPACE_METRIC] THEN
  REWRITE_TAC[HAUSDORFF_SPACE_MTOPOLOGY]);;
    
(* ------------------------------------------------------------------------- *)
(* matrix space boundedness.                                                              *)
(* ------------------------------------------------------------------------- *)

make_overloadable "matrix_bounded" `:A->bool`;;

overload_interface ("matrix_bounded",` rmatrix_bounded:(real^N^M->bool)->bool`);;

overload_interface ("matrix_bounded",` cmatrix_bounded:(complex^N^M->bool)->bool`);;

let rmatrix_bounded = new_definition
  `rmatrix_bounded s <=> ?a. !x:real^N^M. x IN s ==> fnorm(x) <= a`;;
  
let cmatrix_bounded = new_definition
  `cmatrix_bounded s <=> ?a. !x:complex^N^M. x IN s ==> fnorm(x) <= a`;;
  
let matrix_bounded = prove
    (`(!s. rmatrix_bounded s <=> ?a. !x:real^N^M. x IN s ==> fnorm(x) <= a) /\
    (!s. cmatrix_bounded s <=> ?a. !x:complex^N^M. x IN s ==> fnorm(x) <= a) `,
    SIMP_TAC[rmatrix_bounded;cmatrix_bounded]);;
    
(* properties of real matrix entries*)
  
let MATRIX_BOUNDED_EMPTY = prove
 (`matrix_bounded ({}:real^N^M->bool)`,
  REWRITE_TAC[matrix_bounded; NOT_IN_EMPTY]);;
  
let MBOUNDED_MATRIX_SPACE = prove
 (`!s:real^N^M->bool. mbounded matrix_space_metric s <=> matrix_bounded s`,
  let th1 = CMATRIX_ARITH `!x:real^N^M y. x = (x - y) + y` in
  let th2 = SPECL [`x:real^N^M`; `c:real^N^M`] th1 in
  let lem1 = REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS in
  let lem = ONCE_REWRITE_RULE 
           [TAUT `p ==> q ==> r <=> q ==> p ==> r`] lem1 in
  GEN_TAC THEN REWRITE_TAC[mbounded; matrix_bounded; MCBALL_MATRIX_SPACE] THEN
  EQ_TAC THEN REWRITE_TAC[SUBSET; IN_MATRIX_CBALL; LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`c:real^N^M`; `b:real`] THEN DISCH_TAC THEN
    EXISTS_TAC `fnorm(c:real^N^M) + b`;
    X_GEN_TAC `b:real` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`mat 0:real^N^M`; `b:real`]] THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  SIMP_TAC[matrix_dist] THEN ONCE_REWRITE_TAC [FNORM_SUB_SYM] THENL
  [STRIP_TAC THEN ONCE_REWRITE_TAC [th2] THEN
   W(MP_TAC o PART_MATCH lhand FNORM_TRIANGLE o lhand o snd) THEN
   MATCH_MP_TAC lem THEN REWRITE_TAC [GSYM th2] THEN
   ASM_ARITH_TAC;
   ASM_SIMP_TAC[MATRIX_SUB_RZERO]]);;
   
let MATRIX_BOUNDED_CLOSURE = prove
 (`!s:real^N^M->bool. matrix_bounded s ==> matrix_bounded(matrix_closure s)`,
  REWRITE_TAC[matrix_bounded; MATRIX_CLOSURE_SEQUENTIAL] THEN
  GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `y:real^N^M` THEN
  DISCH_THEN(X_CHOOSE_TAC `x:num->real^N^M`) THEN
  MATCH_MP_TAC(ISPEC `sequentially` MATRIX_LIM_FNORM_UBOUND) THEN
  EXISTS_TAC `x:num->real^N^M` THEN
  ASM_SIMP_TAC[EVENTUALLY_TRUE; TRIVIAL_LIMIT_SEQUENTIALLY]);;

let MATRIX_BOUNDED_POS = prove
 (`!s:real^N^M->bool. matrix_bounded s <=> 
            ?b. &0 < b /\ !x. x IN s ==> fnorm(x) <= b`,
  REWRITE_TAC[matrix_bounded] THEN
  MESON_TAC[REAL_ARITH `&0 < &1 + abs(y) /\ (x <= y ==> x <= &1 + abs(y))`]);;
  
let MATRIX_BOUNDED_SUBSET = prove
 (`!s t:real^N^M->bool. matrix_bounded t /\ s SUBSET t ==> matrix_bounded s`,
  MESON_TAC[matrix_bounded; SUBSET]);;
  
let MATRIX_BOUNDED_INTER = prove
 (`!s t:real^N^M->bool. matrix_bounded s \/ matrix_bounded t 
          ==> matrix_bounded (s INTER t)`,
  MESON_TAC[MATRIX_BOUNDED_SUBSET; INTER_SUBSET]);;
  
let MATRIX_BOUNDED_CBALL = prove
 (`!x:real^N^M e. matrix_bounded(matrix_cball(x,e))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_bounded] THEN
  EXISTS_TAC `fnorm(x:real^N^M) + e` THEN 
  REWRITE_TAC[IN_MATRIX_CBALL; matrix_dist] THEN
  SIMP_TAC [FNORM_EQ_NORM_VECTORIZE] THEN 
  SIMP_TAC [VECTORIZE_SUB; GSYM FORALL_VECTORIZE] THEN 
  NORM_ARITH_TAC);;

let MATRIX_BOUNDED_SUBSET_OPEN_INTERVAL_SYMMETRIC = prove
 (`!s:real^N^M->bool. matrix_bounded s ==> ?a. s SUBSET matrix_interval(--a,a)`,
  REWRITE_TAC[MATRIX_BOUNDED_POS; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N^M->bool`; `B:real`] THEN STRIP_TAC THEN
  EXISTS_TAC `(lambda i j. B + &1):real^N^M` THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N^M` THEN DISCH_TAC THEN
  SIMP_TAC[IN_MATRIX_INTERVAL; LAMBDA_BETA; REAL_BOUNDS_LT; 
           MATRIX_NEG_COMPONENT] THEN
  ASM_MESON_TAC[COMPONENT_LE_FNORM;
                REAL_ARITH `x <= y ==> a <= x ==> a < y + &1`]);;
                
let MATRIX_BOUNDED_SUBSET_OPEN_INTERVAL = prove
 (`!s:real^N^M->bool. matrix_bounded s ==> ?a b. s SUBSET matrix_interval(a,b)`,
  MESON_TAC[MATRIX_BOUNDED_SUBSET_OPEN_INTERVAL_SYMMETRIC]);;
  
let MATRIX_BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC = prove
 (`!s:real^N^M->bool. matrix_bounded s ==> ?a. s SUBSET matrix_interval[--a,a]`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MATRIX_BOUNDED_SUBSET_OPEN_INTERVAL_SYMMETRIC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  SIMP_TAC[IN_MATRIX_BALL; IN_MATRIX_INTERVAL; SUBSET; REAL_LT_IMP_LE]);;
  
let MATRIX_BOUNDED_SUBSET_CLOSED_INTERVAL = prove
 (`!s:real^N^M->bool. matrix_bounded s ==> ?a b. s SUBSET matrix_interval[a,b]`,
  MESON_TAC[MATRIX_BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC]);;

let MATRIX_COMPACT_IMP_BOUNDED = prove
 (`!s:real^N^M->bool. matrix_compact s ==> matrix_bounded s`,
  REWRITE_TAC[GSYM COMPACT_IN_MATRIX_SPACE; GSYM MBOUNDED_MATRIX_SPACE] THEN
  REWRITE_TAC[GSYM MTOPOLOGY_MATRIX_SPACE_METRIC; COMPACT_IN_IMP_MBOUNDED]);;
  
let MATRIX_BOUNDED_CLOSED_IMP_COMPACT = prove
 (`!s:real^N^M->bool. matrix_bounded s /\ matrix_closed s ==> matrix_compact s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MATRIX_BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[GSYM COMPACT_IN_MATRIX_SPACE; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N^M`; `b:real^N^M`] THEN DISCH_TAC THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `matrix_interval[a:real^N^M,b]` THEN
  ASM_REWRITE_TAC[CLOSED_IN_MATRIX_SPACE; COMPACT_IN_MATRIX_SPACE] THEN
  REWRITE_TAC[COMPACT_MATRIX_INTERVAL]);;
  
let MATRIX_COMPACT_EQ_BOUNDED_CLOSED = prove
 (`!s:real^N^M->bool. matrix_compact s <=> matrix_bounded s /\ matrix_closed s`,
  MESON_TAC[MATRIX_BOUNDED_CLOSED_IMP_COMPACT; MATRIX_COMPACT_IMP_CLOSED;
            MATRIX_COMPACT_IMP_BOUNDED]);;
            
let MATRIX_BOUNDED_UNION = prove
 (`!s:real^N^M->bool t. matrix_bounded (s UNION t) <=> matrix_bounded s /\ matrix_bounded t`,
  REWRITE_TAC[matrix_bounded; IN_UNION] THEN MESON_TAC[REAL_LE_MAX]);;
  
let MATRIX_CLOSED_UNION = prove
 (`!s:real^N^M->bool t. matrix_closed s /\ matrix_closed t 
                        ==> matrix_closed(s UNION t)`,
  REWRITE_TAC[MATRIX_CLOSED_IN; CLOSED_IN_UNION]);;
            
let MATRIX_COMPACT_UNION = prove
 (`!s t:real^N^M->bool. matrix_compact s /\ matrix_compact t ==> matrix_compact (s UNION t)`,
  SIMP_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED; 
           MATRIX_BOUNDED_UNION; MATRIX_CLOSED_UNION]);;

let MATRIX_COMPACT_EQ_BOLZANO_WEIERSTRASS = prove
 (`!s:real^N^M->bool.
        matrix_compact s <=>
           !t. INFINITE t /\ t SUBSET s ==> 
               ?x. x IN s /\ x matrix_limit_point_of t`,
  REWRITE_TAC[GSYM COMPACT_IN_MATRIX_SPACE] THEN
  REWRITE_TAC[GSYM MTOPOLOGY_MATRIX_SPACE_METRIC] THEN
  REWRITE_TAC[COMPACT_IN_EQ_BOLZANO_WEIERSTRASS] THEN
  REWRITE_TAC[MATRIX_SPACE_METRIC; SUBSET_UNIV] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; 
              MTOPOLOGY_MATRIX_SPACE_METRIC] THEN
  REWRITE_TAC[GSYM MATRIX_LIMIT_POINT_IN_DERIVED_SET] THEN MESON_TAC[]);; 
           
let MATRIX_BOLZANO_WEIERSTRASS_IMP_CLOSED = prove
 (`!s:real^N^M->bool.
        (!t. INFINITE t /\ t SUBSET s ==> 
         ?x. x IN s /\ x matrix_limit_point_of t)
             ==> matrix_closed s`,
  REWRITE_TAC[GSYM MATRIX_COMPACT_EQ_BOLZANO_WEIERSTRASS; 
              MATRIX_COMPACT_IMP_CLOSED]);;
           
let MATRIX_FINITE_IMP_CLOSED = prove
 (`!s:real^N^M->bool. FINITE s ==> matrix_closed s`,
  MESON_TAC[MATRIX_BOLZANO_WEIERSTRASS_IMP_CLOSED; INFINITE; FINITE_SUBSET]);;
  
let MATRIX_FINITE_IMP_BOUNDED = prove
 (`!s:real^N^M->bool. FINITE s ==> matrix_bounded s`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[MATRIX_BOUNDED_EMPTY] THEN
  REWRITE_TAC[matrix_bounded; IN_INSERT] THEN 
  X_GEN_TAC `x:real^N^M` THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `fnorm(x:real^N^M) + abs B` THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[FNORM_POS_LE; REAL_ARITH
   `(y <= b /\ &0 <= x ==> y <= x + abs b) /\ x <= x + abs b`]);;
           
let MATRIX_FINITE_IMP_COMPACT = prove
 (`!s:real^N^M->bool. FINITE s ==> matrix_compact s`,
  SIMP_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED; 
           MATRIX_FINITE_IMP_CLOSED; MATRIX_FINITE_IMP_BOUNDED]);;
            
let MATRIX_COMPACT_SING = prove
 (`!a:real^N^M. matrix_compact {a}`,
  SIMP_TAC[MATRIX_FINITE_IMP_COMPACT; FINITE_RULES]);;
  
let MATRIX_COMPACT_INSERT = prove
 (`!a:real^N^M s. matrix_compact s ==> matrix_compact(a INSERT s)`,
  ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  SIMP_TAC[MATRIX_COMPACT_UNION; MATRIX_COMPACT_SING]);;
  
let MATRIX_COMPACT_INTER_CLOSED = prove
 (`!s t:real^N^M->bool. matrix_compact s /\ matrix_closed t ==> matrix_compact (s INTER t)`,
  SIMP_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED; MATRIX_CLOSED_INTER] THEN
  MESON_TAC[MATRIX_BOUNDED_SUBSET; INTER_SUBSET]);;
  
let MATRIX_CLOSED_INTER_COMPACT = prove
 (`!s t:real^N^M->bool. matrix_closed s /\ matrix_compact t ==> matrix_compact (s INTER t)`,
  MESON_TAC[MATRIX_COMPACT_INTER_CLOSED; INTER_COMM]);;
  
(*
let MATRIX_COMPACT_CBALL = prove
 (`!x:real^N^M->bool e. matrix_compact(matrix_cball(x,e))`,
  REWRITE_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED; 
              MATRIX_BOUNDED_CBALL; MATRIX_CLOSED_CBALL]);;
              
let MATRIX_COMPACT_FRONTIER_BOUNDED = prove
 (`!s:real^N^M->bool. matrix_bounded s ==> matrix_compact(matrix_frontier s)`,
  SIMP_TAC[matrix_frontier; MATRIX_COMPACT_EQ_BOUNDED_CLOSED;
           MATRIX_CLOSED_DIFF; MATRIX_OPEN_INTERIOR; 
           MATRIX_CLOSED_CLOSURE] THEN
  MESON_TAC[SUBSET_DIFF; MATRIX_BOUNDED_SUBSET; MATRIX_BOUNDED_CLOSURE]);;

let MATRIX_COMPACT_FRONTIER = prove
 (`!s. matrix_compact s ==> matrix_compact (matrix_frontier s)`,
  MESON_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED; 
            MATRIX_COMPACT_FRONTIER_BOUNDED]);;
*)

(* ------------------------------------------------------------------------- *)
(* matrix space completeness.                                                              *)
(* ------------------------------------------------------------------------- *)  
  
make_overloadable "matrix_cauchy" `:A->bool`;;

overload_interface ("matrix_cauchy",` rmatrix_cauchy:(num->real^N^M)->bool`);;

overload_interface ("matrix_cauchy",` cmatrix_cauchy:(num->complex^N^M)->bool`);;
  
let rmatrix_cauchy = new_definition
  `rmatrix_cauchy (s:num->real^N^M) <=>
     !e. &0 < e ==> ?N. !m n. m >= N /\ n >= N ==> matrix_dist(s m,s n) < e`;;
     
let cmatrix_cauchy = new_definition
  `cmatrix_cauchy (s:num->complex^N^M) <=>
     !e. &0 < e ==> ?N. !m n. m >= N /\ n >= N ==> matrix_dist(s m,s n) < e`;;
     
let matrix_cauchy = prove
  (`(!s. rmatrix_cauchy (s:num->real^N^M) <=>
     !e. &0 < e ==> ?N. !m n. m >= N /\ n >= N ==> matrix_dist(s m,s n) < e) /\
    (!s. cmatrix_cauchy (s:num->complex^N^M) <=>
     !e. &0 < e ==> ?N. !m n. m >= N /\ n >= N ==> matrix_dist(s m,s n) < e)`,
    SIMP_TAC[rmatrix_cauchy;cmatrix_cauchy]);;
     
make_overloadable "matrix_complete" `:A->bool`;;

overload_interface ("matrix_complete",` rmatrix_complete:(real^N^M->bool)->bool`);;

overload_interface ("matrix_complete",` cmatrix_complete:(complex^N^M->bool)->bool`);;
     
let rmatrix_complete = new_definition
  `rmatrix_complete s <=>
     !f:num->real^N^M. (!n. f n IN s) /\ matrix_cauchy f
                      ==> ?l. l IN s /\ (f ->-> l) sequentially`;;
                
let cmatrix_complete = new_definition
  `cmatrix_complete s <=>
     !f:num->complex^N^M. (!n. f n IN s) /\ matrix_cauchy f
                      ==> ?l. l IN s /\ (f ->-> l) sequentially`;;
                      
let matrix_complete = prove
    (`(!s. rmatrix_complete s <=>
     !f:num->real^N^M. (!n. f n IN s) /\ matrix_cauchy f
                      ==> ?l. l IN s /\ (f ->-> l) sequentially) /\
    (!s. cmatrix_complete s <=>
     !f:num->complex^N^M. (!n. f n IN s) /\ matrix_cauchy f
                      ==> ?l. l IN s /\ (f ->-> l) sequentially)`,
    SIMP_TAC[rmatrix_complete;cmatrix_complete]);;
     
let CAUCHY_IN_MATRIX_SPACE = prove
 (`!s:num->real^N^M. cauchy_in matrix_space_metric s <=> matrix_cauchy s`,
  REWRITE_TAC[matrix_cauchy; cauchy_in; MATRIX_SPACE_METRIC; IN_UNIV; GE]);;
  
let MATRIX_CAUCHY = prove
 (`!s:num->real^N^M.
      matrix_cauchy s <=> !e. &0 < e ==> ?N. !n. n >= N 
            ==> matrix_dist(s n,s N) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_cauchy; GE] THEN EQ_TAC THENL
   [MESON_TAC[LE_REFL]; DISCH_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MESON_TAC[MATRIX_DIST_TRIANGLE_HALF_L]);;
     
let MATRIX_CONVERGENT_IMP_CAUCHY = prove
 (`!s:num->real^N^M l. (s ->-> l) sequentially ==> matrix_cauchy s`,
  REWRITE_TAC[GSYM LIMIT_MATRIX_SPACE; GSYM CAUCHY_IN_MATRIX_SPACE] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MTOPOLOGY_MATRIX_SPACE_METRIC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONVERGENT_IMP_CAUCHY_IN) THEN
  REWRITE_TAC[MATRIX_SPACE_METRIC; IN_UNIV]);;

let MATRIX_CAUCHY_IMP_BOUNDED = prove
 (`!s:num->real^N^M. matrix_cauchy s ==> matrix_bounded {y | ?n. y = s n}`,
  GEN_TAC THEN REWRITE_TAC[GSYM CAUCHY_IN_MATRIX_SPACE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CAUCHY_IN_IMP_MBOUNDED) THEN
  REWRITE_TAC[MBOUNDED_MATRIX_SPACE] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN SET_TAC[]);;
  
let MATRIX_CAUCHY_CONVERGENT_SUBSEQUENCE = prove
 (`!x:num->real^N^M r.
        matrix_cauchy x /\ (!m n. m < n ==> r m < r n) /\ ((x o r) ->-> l) sequentially
        ==> (x ->-> l) sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] MATRIX_LIM_ADD)) THEN
  DISCH_THEN(MP_TAC o SPEC `\n. (x:num->real^N^M)(n) - x(r n)`) THEN
  DISCH_THEN(MP_TAC o SPEC `mat 0: real^N^M`) THEN ASM_REWRITE_TAC[o_THM] THEN
  REWRITE_TAC[MATRIX_ADD_RID; MATRIX_SUB_ADD2; ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [matrix_cauchy]) THEN
  REWRITE_TAC[GE; MATRIX_LIM_SEQUENTIALLY; matrix_dist; MATRIX_SUB_RZERO] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MONOTONE_BIGGER) THEN
  ASM_MESON_TAC[LE_TRANS]);;

let MATRIX_SPACE_COMPACT_IMP_COMPLETE = prove
 (`!s:real^N^M->bool. matrix_compact s ==> matrix_complete s`,
  GEN_TAC THEN REWRITE_TAC[matrix_complete; matrix_compact] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `f:num->real^N^M` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MATRIX_CAUCHY_CONVERGENT_SUBSEQUENCE THEN
  ASM_MESON_TAC[]);;
                                              
let MATRIX_COMPLETE_UNIV = prove
 (`matrix_complete(:real^N^M)`,
  REWRITE_TAC[matrix_complete; IN_UNIV] THEN X_GEN_TAC `x:num->real^N^M` THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP MATRIX_CAUCHY_IMP_BOUNDED) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP MATRIX_BOUNDED_CLOSURE) THEN
  MP_TAC(ISPEC `matrix_closure {y:real^N^M | ?n:num. y = x n}`
               MATRIX_SPACE_COMPACT_IMP_COMPLETE) THEN
  ASM_SIMP_TAC[MATRIX_BOUNDED_CLOSED_IMP_COMPACT; 
               MATRIX_CLOSED_CLOSURE; matrix_complete] THEN
  DISCH_THEN(MP_TAC o SPEC `x:num->real^N^M`) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ASM_REWRITE_TAC[matrix_closure; IN_ELIM_THM; IN_UNION] THEN MESON_TAC[]);;
  
let MATRIX_COMPLETE_EQ_CLOSED = prove
 (`!s:real^N^M->bool. matrix_complete s <=> matrix_closed s`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[matrix_complete; MATRIX_CLOSED_LIMPT; MATRIX_LIMPT_SEQUENTIAL] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN GEN_TAC THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
    MESON_TAC[MATRIX_CONVERGENT_IMP_CAUCHY; IN_DELETE; MATRIX_LIM_UNIQUE;
              TRIVIAL_LIMIT_SEQUENTIALLY];
    REWRITE_TAC[matrix_complete; MATRIX_CLOSED_SEQUENTIAL_LIMITS] THEN 
    DISCH_TAC THEN
    X_GEN_TAC `f:num->real^N^M` THEN STRIP_TAC THEN
    MP_TAC(REWRITE_RULE[matrix_complete] MATRIX_COMPLETE_UNIV) THEN
    DISCH_THEN(MP_TAC o SPEC `f:num->real^N^M`) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN ASM_MESON_TAC[]]);;

let MATRIX_CONVERGENT_EQ_CAUCHY = prove
 (`!s:num->real^N^M. (?l. (s ->-> l) sequentially) <=> matrix_cauchy s`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM; MATRIX_CONVERGENT_IMP_CAUCHY];
    REWRITE_TAC[REWRITE_RULE[matrix_complete; IN_UNIV] MATRIX_COMPLETE_UNIV]]);;

(* ------------------------------------------------------------------------- *)
(* Define continuity over a net to take in restrictions of the set.          *)
(* ------------------------------------------------------------------------- *)

make_overloadable "matrix_continuous" `:A->B->bool`;;

overload_interface ("matrix_continuous",` rmatrix_continuous:(real^N^M->real^P^Q)->(real^N^M)net->bool`);;

overload_interface ("matrix_continuous",` cmatrix_continuous:(complex^N^M->complex^P^Q)->(complex^N^M)net->bool`);;

parse_as_infix ("matrix_continuous",(12,"right"));;

let rmatrix_continuous = new_definition
  `(f:real^N^M->real^P^Q) matrix_continuous net <=> (f ->-> f(netlimit net)) net`;;
  
let cmatrix_continuous = new_definition
  `(f:complex^N^M->complex^P^Q) matrix_continuous net <=> (f ->-> f(netlimit net)) net`;;
  
let matrix_continuous = prove
    (`(!f net. (f:real^N^M->real^P^Q) matrix_continuous net <=> (f ->-> f(netlimit net)) net) /\
    (!f net. (f:complex^N^M->complex^P^Q) matrix_continuous net <=> (f ->-> f(netlimit net)) net)`,
    SIMP_TAC[rmatrix_continuous;cmatrix_continuous]);;
    
(* properties of real matrix entries*)

let MATRIX_CONTINUOUS_WITHIN = prove
 (`!f x:real^N^M s:real^N^M->bool. f matrix_continuous (matrix_at x within s) <=> 
              (f ->-> f(x)) (matrix_at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_continuous] THEN
  ASM_CASES_TAC `trivial_limit(matrix_at (x:real^N^M) within s)` THEN
  ASM_SIMP_TAC[MATRIX_LIM_TRIVIAL; MATRIX_NETLIMIT_WITHIN]);;
  
let MATRIX_CONTINUOUS_CONST = prove
 (`!net c:real^N^M. (\x. c) matrix_continuous net`,
  REWRITE_TAC[matrix_continuous; MATRIX_LIM_CONST]);;

let MATRIX_CONTINUOUS_CMUL = prove
 (`!f c net. f matrix_continuous net ==> (\x. c %% f(x)) matrix_continuous net`,
  REWRITE_TAC[matrix_continuous; MATRIX_LIM_CMUL]);;

let MATRIX_CONTINUOUS_NEG = prove
 (`!f:real^N^M->real^P^Q net. f matrix_continuous net ==> 
         (\x. --(f x)) matrix_continuous net`,
  REWRITE_TAC[matrix_continuous; MATRIX_LIM_NEG]);;

let MATRIX_CONTINUOUS_ADD = prove
 (`!f:real^N^M->real^P^Q g net. f matrix_continuous net /\ g matrix_continuous net
           ==> (\x. f(x) + g(x)) matrix_continuous net`,
  REWRITE_TAC[matrix_continuous; MATRIX_LIM_ADD]);;

let MATRIX_CONTINUOUS_SUB = prove
 (`!f:real^N^M->real^P^Q g net. f matrix_continuous net /\ g matrix_continuous net
           ==> (\x. f(x) - g(x)) matrix_continuous net`,
  REWRITE_TAC[matrix_continuous; MATRIX_LIM_SUB]);;
    
(* ------------------------------------------------------------------------- *)
(* For setwise continuity, just start from the epsilon-delta definitions.    *)
(* A version in matrix space                                                 *)
(* ------------------------------------------------------------------------- *)

make_overloadable "matrix_continuous_on" `:A->B->bool`;;

overload_interface ("matrix_continuous_on",`rmatrix_continuous_on:(real^N^M->real^P^Q)->(real^N^M->bool)->bool`);;

overload_interface ("matrix_continuous_on",`cmatrix_continuous_on:(complex^N^M->complex^P^Q)->(complex^N^M->bool)->bool`);;

parse_as_infix ("matrix_continuous_on",(12,"right"));;

let rmatrix_continuous_on = new_definition
  `!f:real^N^M->real^P^Q s:real^N^M->bool. f matrix_continuous_on s <=>
        !x. x IN s ==> !e. &0 < e
                           ==> ?d. &0 < d /\
                                   !x'. x' IN s /\ matrix_dist(x',x) < d
                                        ==> matrix_dist(f(x'),f(x)) < e`;;
                                        
let cmatrix_continuous_on = new_definition
  `!f:complex^N^M->complex^N^M s:complex^N^M->bool. (f matrix_continuous_on s) <=>
        !x. x IN s ==> !e. &0 < e
                           ==> ?d. &0 < d /\
                                   !x'. x' IN s /\ matrix_dist(x',x) < d
                                        ==> matrix_dist(f(x'),f(x)) < e`;;
                    
let matrix_continuous_on = prove
    (`(!f:real^N^M->real^P^Q s. f matrix_continuous_on s <=>
        (!x. x IN s ==> !e. &0 < e
                           ==> ?d. &0 < d /\
                                   !x'. x' IN s /\ matrix_dist(x',x) < d
                                        ==> matrix_dist(f(x'),f(x)) < e)) /\
    (!f:complex^N^M->complex^N^M s. f matrix_continuous_on s <=>
        (!x. x IN s ==> !e. &0 < e
                           ==> ?d. &0 < d /\
                                   !x'. x' IN s /\ matrix_dist(x',x) < d
                                        ==> matrix_dist(f(x'),f(x)) < e))`,
    SIMP_TAC[rmatrix_continuous_on;cmatrix_continuous_on]);;

make_overloadable "matrix_uniformly_continuous_on" `:A->B->bool`;;

overload_interface ("matrix_uniformly_continuous_on",` rmatrix_uniformly_continuous_on:(real^N^M->real^P^Q)->(real^N^M->bool)->bool`);;

overload_interface ("matrix_uniformly_continuous_on",` cmatrix_uniformly_continuous_on:(complex^N^M->complex^P^Q)->(complex^N^M->bool)->bool`);;
    
parse_as_infix ("matrix_uniformly_continuous_on",(12,"right"));;    
    
let rmatrix_uniformly_continuous_on = new_definition
  `(f:real^N^M->real^P^Q) matrix_uniformly_continuous_on (s:real^N^M->bool) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x x'. x IN s /\ x' IN s /\ matrix_dist(x',x) < d
                           ==> matrix_dist(f(x'),f(x)) < e`;;
                           
let cmatrix_uniformly_continuous_on = new_definition
  `(f:complex^N^M->complex^P^Q) matrix_uniformly_continuous_on (s:complex^N^M->bool) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x x'. x IN s /\ x' IN s /\ matrix_dist(x',x) < d
                           ==> matrix_dist(f(x'),f(x)) < e`;;
                           
let matrix_uniformly_continuous_on = prove
    (`(!f:real^N^M->real^P^Q s. f matrix_uniformly_continuous_on s <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x x'. x IN s /\ x' IN s /\ matrix_dist(x',x) < d
                           ==> matrix_dist(f(x'),f(x)) < e) /\
    (!f:complex^N^M->complex^P^Q s. f matrix_uniformly_continuous_on s <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x x'. x IN s /\ x' IN s /\ matrix_dist(x',x) < d
                           ==> matrix_dist(f(x'),f(x)) < e)`,
    SIMP_TAC[rmatrix_uniformly_continuous_on;cmatrix_uniformly_continuous_on]);;
    
(* properties of real matrix entries*)
    
let matrix_continuous_within = prove
 (`(!f:real^N^M->real^P^Q s. f matrix_continuous (matrix_at x within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
     !x'. x' IN s /\ matrix_dist(x',x) < d ==> matrix_dist(f(x'),f(x)) < e)`,
  REWRITE_TAC[MATRIX_CONTINUOUS_WITHIN; MATRIX_LIM_WITHIN] THEN
  REWRITE_TAC[GSYM MATRIX_DIST_NZ] THEN MESON_TAC[MATRIX_DIST_REFL]);;
    
let matrix_continuous_at = prove
 (`!f:real^N^M->real^P^Q x. f matrix_continuous (matrix_at x) <=>
        !e. &0 < e ==> ?d. &0 < d /\
                !x'. matrix_dist(x',x) < d ==> matrix_dist(f(x'),f(x)) < e`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  REWRITE_TAC[matrix_continuous_within; IN_UNIV]);;
  
let MATRIX_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN = prove
 (`!f:real^N^M->real^P^Q s. f matrix_continuous_on s <=> !x. x IN s ==> 
         f matrix_continuous (matrix_at x within s)`,
  REWRITE_TAC[matrix_continuous_on; matrix_continuous_within]);;
  
let CONTINUOUS_MAP_MATRIX_SPACE = prove
 (`!f:real^N^M->real^Q^P s.
     continuous_map (subtopology matrix_space s,matrix_space) f <=>
     f matrix_continuous_on s`,
  REWRITE_TAC[GSYM  MTOPOLOGY_MATRIX_SPACE_METRIC;
              GSYM MTOPOLOGY_SUBMETRIC] THEN
  REWRITE_TAC[METRIC_CONTINUOUS_MAP; matrix_continuous_on] THEN
  REWRITE_TAC[SUBMETRIC; MATRIX_SPACE_METRIC; IN_UNIV; IN_INTER] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MATRIX_DIST_SYM] THEN
  MESON_TAC[]);;
  
let MATRIX_CONTINUOUS_WITHIN = prove
 (`!f x:real^M^N. f matrix_continuous (matrix_at x within s) 
                <=> (f ->-> f(x)) (matrix_at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_continuous] THEN
  ASM_CASES_TAC `trivial_limit(matrix_at (x:real^M^N) within s)` THEN
  ASM_SIMP_TAC[MATRIX_LIM_TRIVIAL; MATRIX_NETLIMIT_WITHIN]);;
  
let MATRIX_CONTINUOUS_AT = prove
 (`!f (x:real^N^M). f matrix_continuous (matrix_at x) 
                   <=> (f ->-> f(x)) (matrix_at x)`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  REWRITE_TAC[MATRIX_CONTINUOUS_WITHIN; IN_UNIV]);;
  
let MATRIX_CONTINUOUS_ON = prove
 (`!f (s:real^N^M->bool).
        f matrix_continuous_on s <=> 
        !x. x IN s ==> (f ->-> f(x)) (matrix_at x within s)`,
  REWRITE_TAC[MATRIX_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; 
              MATRIX_CONTINUOUS_WITHIN]);;
              
let MATRIX_CONTINUOUS_AT_WITHIN = prove
 (`!f:real^M^N->real^Q^P x s.
        f matrix_continuous (matrix_at x) ==>
        f matrix_continuous (matrix_at x within s)`,
  SIMP_TAC[MATRIX_LIM_AT_WITHIN; MATRIX_CONTINUOUS_AT; 
           MATRIX_CONTINUOUS_WITHIN]);;

(* ------------------------------------------------------------------------- *)
(* Same thing for setwise continuity.                                        *)
(* ------------------------------------------------------------------------- *)

let MATRIX_CONTINUOUS_ON_CONST = prove
 (`!s:real^N^M->bool c. (\x. c) matrix_continuous_on s`,
  SIMP_TAC[MATRIX_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; 
           MATRIX_CONTINUOUS_CONST]);;

let MATRIX_CONTINUOUS_ON_CMUL = prove
 (`!f:real^N^M->real^P^Q c s. f matrix_continuous_on s ==> 
                    (\x. c %% f(x)) matrix_continuous_on s`,
  SIMP_TAC[MATRIX_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; 
           MATRIX_CONTINUOUS_CMUL]);;

let MATRIX_CONTINUOUS_ON_NEG = prove
 (`!f:real^N^M->real^P^Q s. f matrix_continuous_on s
         ==> (\x. --(f x)) matrix_continuous_on s`,
  SIMP_TAC[MATRIX_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; MATRIX_CONTINUOUS_NEG]);;

let MATRIX_CONTINUOUS_ON_ADD = prove
 (`!f:real^N^M->real^P^Q g s. f matrix_continuous_on s /\ g matrix_continuous_on s
           ==> (\x. f(x) + g(x)) matrix_continuous_on s`,
  SIMP_TAC[MATRIX_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; MATRIX_CONTINUOUS_ADD]);;

let MATRIX_CONTINUOUS_ON_SUB = prove
 (`!f:real^N^M->real^P^Q g s. f matrix_continuous_on s /\ g matrix_continuous_on s
           ==> (\x. f(x) - g(x)) matrix_continuous_on s`,
  SIMP_TAC[MATRIX_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; MATRIX_CONTINUOUS_SUB]);;
  
let MATRIX_CONTINUOUS_ON_ID = prove
 (`!s:real^N^M->bool. (\x. x) matrix_continuous_on s`,
  REWRITE_TAC[matrix_continuous_on] THEN MESON_TAC[]);;
  
let MATRIX_COMPACT_CONTINUOUS_IMAGE = prove
 (`!f:real^N^M->real^Q^P s.
        f matrix_continuous_on s /\ matrix_compact s 
        ==> matrix_compact(IMAGE f s)`,
  REWRITE_TAC[GSYM COMPACT_IN_MATRIX_SPACE; 
              GSYM CONTINUOUS_MAP_MATRIX_SPACE] THEN
  MESON_TAC[IMAGE_COMPACT_IN; COMPACT_IN_ABSOLUTE]);;
  
let MATRIX_CONTINUOUS_ON_OPEN_GEN = prove
 (`!f:real^N^M->real^Q^P s t.
    IMAGE f s SUBSET t
    ==> (f matrix_continuous_on s <=>
         !u. open_in (subtopology matrix_space t) u
             ==> open_in (subtopology matrix_space s) {x | x IN s /\ f x IN u})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[matrix_continuous_on] THEN EQ_TAC THENL
   [REWRITE_TAC[matrix_open_in; SUBSET; IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `u:real^Q^P->bool` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MATRIX_DIST_REFL]; ALL_TAC] THEN
    X_GEN_TAC `x:real^N^M` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^N^M->real^Q^P) x`) THEN ASM SET_TAC[];
    DISCH_TAC THEN X_GEN_TAC `x:real^N^M` THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o
      SPEC `matrix_ball((f:real^N^M->real^Q^P) x,e) INTER t`) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[MATRIX_OPEN_IN_OPEN; INTER_COMM; MATRIX_OPEN_BALL];
      ALL_TAC] THEN
    REWRITE_TAC[matrix_open_in; SUBSET; IN_INTER; IN_ELIM_THM; 
                IN_MATRIX_BALL; IN_IMAGE] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N^M`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_MESON_TAC[MATRIX_DIST_REFL; MATRIX_DIST_SYM]]);;
  
let MATRIX_CONTINUOUS_ON_CLOSED_GEN = prove
 (`!f:real^N^M->real^Q^P s t.
    IMAGE f s SUBSET t
    ==> (f matrix_continuous_on s <=>
         !u. closed_in (subtopology matrix_space t) u
             ==> closed_in (subtopology matrix_space s)
                           {x | x IN s /\ f x IN u})`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th ->
    ONCE_REWRITE_TAC[MATCH_MP MATRIX_CONTINUOUS_ON_OPEN_GEN th]) THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `u:real^Q^P->bool` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t DIFF u:real^Q^P->bool`) THENL
   [REWRITE_TAC[closed_in]; REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ]] THEN
  REWRITE_TAC[TOPSPACE_MATRIX_SPACE_SUBTOPOLOGY] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[SUBSET_RESTRICT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]);;
  
let MATRIX_CONTINUOUS_ON_CLOSED = prove
 (`!f:real^N^M->real^Q^P s.
      f matrix_continuous_on s <=>
        !t. closed_in (subtopology matrix_space (IMAGE f s)) t
            ==> closed_in (subtopology matrix_space s) {x | x IN s /\ f(x) IN t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_CONTINUOUS_ON_CLOSED_GEN THEN
  REWRITE_TAC[SUBSET_REFL]);;
  
let MATRIX_CONTINUOUS_CLOSED_PREIMAGE = prove
 (`!f:real^N^M->real^Q^P s t.
     f matrix_continuous_on s /\ matrix_closed s /\ matrix_closed t
     ==> matrix_closed {x | x IN s /\ f(x) IN t}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATRIX_CONTINUOUS_ON_CLOSED]) THEN
  REWRITE_TAC [MATRIX_CLOSED_IN_CLOSED] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (f:real^N^M->real^Q^P) s INTER t`) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `t:real^Q^P->bool` THEN ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    SUBGOAL_THEN `{x | x IN s /\ (f:real^N^M->real^Q^P) x IN t} =
                 s INTER t'` SUBST1_TAC THENL
    [ASM SET_TAC []; ASM_MESON_TAC [MATRIX_CLOSED_INTER]]]);;
    
(* ------------------------------------------------------------------------- *)
(* Identity function is continuous in every sense.                           *)
(* ------------------------------------------------------------------------- *)

let MATRIX_CONTINUOUS_WITHIN_ID = prove
 (`!a:real^N^M s. (\x. x) matrix_continuous (matrix_at a within s)`,
  REWRITE_TAC[matrix_continuous_within] THEN MESON_TAC[]);;

let MATRIX_CONTINUOUS_AT_ID = prove
 (`!a:real^N^M. (\x. x) matrix_continuous (matrix_at a)`,
  REWRITE_TAC[matrix_continuous_at] THEN MESON_TAC[]);;

let MATRIX_CONTINUOUS_ON_ID = prove
 (`!s:real^N^M->bool. (\x. x) matrix_continuous_on s`,
  REWRITE_TAC[matrix_continuous_on] THEN MESON_TAC[]);;

let UNIFORMLY_CONTINUOUS_ON_ID = prove
 (`!s:real^N^M->bool. (\x. x) matrix_uniformly_continuous_on s`,
  REWRITE_TAC[matrix_uniformly_continuous_on] THEN MESON_TAC[]);;
  
(* ------------------------------------------------------------------------- *)
(* Topological stuff lifted to R                                             *)
(* ------------------------------------------------------------------------- *)

let MATRIX_OPEN_LIFT2 = prove
 (`!s. matrix_open(IMAGE lift_lift s) <=>
        !x. x IN s ==> ?e. &0 < e /\ !x'. abs(x' - x) < e ==> x' IN s`,
  REWRITE_TAC[matrix_open; FORALL_LIFT2; 
              LIFT2_IN_IMAGE_LIFT2; MATRIX_DIST_LIFT2]);;

let MATRIX_LIMPT_APPROACHABLE_LIFT2 = prove
 (`!x s. (lift_lift x) matrix_limit_point_of (IMAGE lift_lift s) <=>
         !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ abs(x' - x) < e`,
  REWRITE_TAC[MATRIX_LIMPT_APPROACHABLE; EXISTS_LIFT2; LIFT2_IN_IMAGE_LIFT2;
              LIFT2_EQ; MATRIX_DIST_LIFT2]);;

let MATRIX_CLOSED_LIFT2 = prove
 (`!s. matrix_closed (IMAGE lift_lift s) <=>
        !x. (!e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ abs(x' - x) < e)
            ==> x IN s`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_CLOSED_LIMPT; MATRIX_LIMPT_APPROACHABLE] THEN
  ONCE_REWRITE_TAC[FORALL_LIFT2] THEN
  REWRITE_TAC[MATRIX_LIMPT_APPROACHABLE_LIFT2; LIFT2_EQ; MATRIX_DIST_LIFT2;
              EXISTS_LIFT2; LIFT2_IN_IMAGE_LIFT2]);;
              
let MATRIX_BOUNDED_LIFT2 = prove
 (`!s. matrix_bounded(IMAGE lift_lift s) <=>  ?a. !x. x IN s ==> abs(x) <= a`,
  REWRITE_TAC[matrix_bounded; FORALL_LIFT2; FNORM_LIFT2; LIFT2_IN_IMAGE_LIFT2]);;

let MATRIX_BOUNDED_HAS_SUP = prove
 (`!s. matrix_bounded(IMAGE lift_lift s) /\ ~(s = {})
       ==> (!x. x IN s ==> x <= sup s) /\
           (!b. (!x. x IN s ==> x <= b) ==> sup s <= b)`,
  REWRITE_TAC[MATRIX_BOUNDED_LIFT2; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[SUP; REAL_ARITH `abs(x) <= a ==> x <= a`]);;

let MATRIX_COMPACT_ATTAINS_SUP = prove
 (`!s. matrix_compact (IMAGE lift_lift s) /\ ~(s = {})
       ==> ?x. x IN s /\ !y. y IN s ==> y <= x`,
  REWRITE_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `s:real->bool` MATRIX_BOUNDED_HAS_SUP) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC `sup s` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MATRIX_CLOSED_LIFT2; REAL_ARITH `s <= s - e <=> ~(&0 < e)`;
                REAL_ARITH `x <= s /\ ~(x <= s - e) ==> abs(x - s) < e`]);;
  
let MATRIX_CONTINUOUS_ATTAINS_SUP = prove
 (`!f:real^N^M->real s.
        matrix_compact s /\ ~(s = {}) /\ (lift_lift o f) matrix_continuous_on s
        ==> ?x. x IN s /\ !y. y IN s ==> f(y) <= f(x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `IMAGE (f:real^N^M->real) s` MATRIX_COMPACT_ATTAINS_SUP) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; MATRIX_COMPACT_CONTINUOUS_IMAGE; 
               IMAGE_EQ_EMPTY] THEN
  MESON_TAC[IN_IMAGE]);;
  
let MATRIX_BOUNDED_HAS_INF = prove
 (`!s. matrix_bounded(IMAGE lift_lift s) /\ ~(s = {})
       ==> (!x. x IN s ==> inf s <= x) /\
           (!b. (!x. x IN s ==> b <= x) ==> b <= inf s)`,
  REWRITE_TAC[MATRIX_BOUNDED_LIFT2; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[INF; REAL_ARITH `abs(x) <= a ==> --a <= x`]);;
  
let MATRIX_COMPACT_ATTAINS_INF = prove
 (`!s. matrix_compact (IMAGE lift_lift s) /\ ~(s = {})
       ==> ?x. x IN s /\ !y. y IN s ==> x <= y`,
  REWRITE_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `s:real->bool` MATRIX_BOUNDED_HAS_INF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC `inf s` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MATRIX_CLOSED_LIFT2; REAL_ARITH `s + e <= s <=> ~(&0 < e)`;
                REAL_ARITH `s <= x /\ ~(s + e <= x) ==> abs(x - s) < e`]);;
  
let MATRIX_CONTINUOUS_ATTAINS_INF = prove
 (`!f:real^N^M->real s.
        matrix_compact s /\ ~(s = {}) /\ (lift_lift o f) matrix_continuous_on s
        ==> ?x. x IN s /\ !y. y IN s ==> f(x) <= f(y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `IMAGE (f:real^N^M->real) s` MATRIX_COMPACT_ATTAINS_INF) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; MATRIX_COMPACT_CONTINUOUS_IMAGE; 
               IMAGE_EQ_EMPTY] THEN
  MESON_TAC[IN_IMAGE]);;
  
let MATRIX_CONTINUOUS_WITHIN_SEQUENTIALLY = prove
 (`!f s a:real^N^M.
        f matrix_continuous (matrix_at a within s) <=>
                !x. (!n. x(n) IN s) /\ (x ->-> a) sequentially
                     ==> ((f o x) ->-> f(a)) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_continuous_within] THEN EQ_TAC THENL
   [REWRITE_TAC[MATRIX_LIM_SEQUENTIALLY; o_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&1 / (&n + &1)`) THEN
  SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; REAL_OF_NUM_LE; REAL_POS; ARITH;
       REAL_ARITH `&0 <= n ==> &0 < n + &1`; NOT_FORALL_THM; SKOLEM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[NOT_IMP; FORALL_AND_THM] THEN
  X_GEN_TAC `y:num->real^N^M` THEN 
  REWRITE_TAC[MATRIX_LIM_SEQUENTIALLY; o_THM] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[LE_REFL]] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FORALL_POS_MONO_1 THEN
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `&1 / (&m + &1)` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_INV2; real_div; REAL_ARITH `&0 <= x ==> &0 < x + &1`;
               REAL_POS; REAL_MUL_LID; REAL_LE_RADD; REAL_OF_NUM_LE]);;
  
let MATRIX_CONTINUOUS_AT_SEQUENTIALLY = prove
 (`!f a:real^N^M.
        f matrix_continuous (matrix_at a) <=>
              !x. (x ->-> a) sequentially
                  ==> ((f o x) ->-> f(a)) sequentially`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  REWRITE_TAC[MATRIX_CONTINUOUS_WITHIN_SEQUENTIALLY; IN_UNIV]);;
    
(* ------------------------------------------------------------------------- *)
(* The definition and properties of the infinite sum of matrix serie         *)
(* ------------------------------------------------------------------------- *)  

make_overloadable "msums" `:A->B->C->bool`;;

overload_interface ("msums",` rmsums:(num->real^N^M)->real^N^M->(num->bool)->bool`);;

overload_interface ("msums",` cmsums:(num->complex^N^M)->complex^N^M->(num->bool)->bool`);;

parse_as_infix("msums",(12,"right"));;

let rmsums = new_definition
    `(f msums (l:real^N^M)) s = ((\n. msum(s INTER (0..n)) f) ->-> l) sequentially`;;
 
let cmsums = new_definition
    `(f msums (l:complex^N^M)) s = ((\n. msum(s INTER (0..n)) f) ->-> l) sequentially`;;
    
let msums = prove
    (`(!f l s. (f msums (l:real^N^M)) s = ((\n. msum(s INTER (0..n)) f) ->-> l) sequentially) /\
    (!f l s. (f msums (l:complex^N^M)) s = ((\n. msum(s INTER (0..n)) f) ->-> l) sequentially)`,
    SIMP_TAC[rmsums;cmsums]);;
    
make_overloadable "infmsum" `:A->B->C`;;

overload_interface ("infmsum",` rinfmsum:(num->bool)->(num->real^N^M)->real^N^M`);;

overload_interface ("infmsum",` cinfmsum:(num->bool)->(num->complex^N^M)->complex^N^M`);;

let rinfmsum = new_definition
    `rinfmsum s (f:num->real^N^M) = @l. (f msums l) s`;;
    
let cinfmsum = new_definition
    `cinfmsum s (f:num->complex^N^M) = @l. (f msums l) s`;;
    
let infmsum = prove
    (`(!s f. rinfmsum s (f:num->real^N^M) = @l. (f msums l) s) /\
    (!s f. cinfmsum s (f:num->complex^N^M) = @l. (f msums l) s)`,
    SIMP_TAC[rinfmsum;cinfmsum]);;
    
make_overloadable "msummable" `:A->B->bool`;;

overload_interface ("msummable",` rmsummable:(num->bool)->(num->real^N^M)->bool`);;

overload_interface ("msummable",` cmsummable:(num->bool)->(num->complex^N^M)->bool`);;

let rmsummable = new_definition
    `rmsummable s (f:num->real^N^M) = ?l. (f msums l) s`;;
    
let cmsummable = new_definition
    `cmsummable s (f:num->complex^N^M) = ?l. (f msums l) s`;;
    
let msummable = prove
    (`(!s f. rmsummable s (f:num->real^N^M) = ?l. (f msums l) s) /\
    (!s f. cmsummable s (f:num->complex^N^M) = ?l. (f msums l) s)`,
    SIMP_TAC[rmsummable;cmsummable]);;

(* properties of real matrix entries*)    
    
let MSUMS_SUMMABLE = prove
    (`!f:num->real^N^M l s. (f msums l) s ==> msummable s f`,
    REWRITE_TAC[msummable] THEN METIS_TAC[]);;
  
let MSUMS_INFSUM = prove
    (`!f:num->real^N^M s. (f msums (infmsum s f)) s <=> msummable s f`,
    REWRITE_TAC[infmsum; msummable] THEN METIS_TAC[]);;
  
let MSUMS_LIM = prove
    (`!f:num->real^N^M s.
      (f msums matrix_lim sequentially (\n. msum (s INTER (0..n)) f)) s
      <=> msummable s f`,
    GEN_TAC THEN GEN_TAC THEN EQ_TAC THENL [MESON_TAC[msummable];
    REWRITE_TAC[msummable; msums] THEN STRIP_TAC THEN REWRITE_TAC[matrix_lim] THEN
    ASM_MESON_TAC[]]);;
    
let MSERIES_FROM = prove
    (`!f:num->real^N^M l k. 
        (f msums l) (from k) = ((\n. msum(k..n) f) ->-> l) sequentially`,
    REPEAT GEN_TAC THEN REWRITE_TAC[msums] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; numseg; from; IN_ELIM_THM; IN_INTER] THEN ARITH_TAC);;
  
let MSERIES_UNIQUE = prove
    (`!f:num->real^N^M l l' s. (f msums l) s /\ (f msums l') s ==> (l = l')`,
    REWRITE_TAC[msums] THEN 
    MESON_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; MATRIX_LIM_UNIQUE]);;
  
let INFMSUM_UNIQUE = prove
    (`!f:num->real^N^M l s. (f msums l) s ==> infmsum s f = l`,
    MESON_TAC[MSERIES_UNIQUE; MSUMS_INFSUM; msummable]);;
                
let MSERIES_FINITE = prove
    (`!f:num->real^N^M s. FINITE s ==> (f msums (msum s f)) s`,
    REPEAT GEN_TAC THEN REWRITE_TAC[num_FINITE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[msums; MATRIX_LIM_SEQUENTIALLY] THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `n:num` THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s INTER (0..m) = s`
    (fun th -> ASM_REWRITE_TAC[th; MATRIX_DIST_REFL]) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_NUMSEG; LE_0] THEN
    ASM_MESON_TAC[LE_TRANS]);;
    
let MSERIES_0 = prove
 (`!s. ((\n:num. mat 0) msums (mat 0)) s`,
  REWRITE_TAC[msums; MSUM_0; MATRIX_LIM_CONST]);;
  
let MSERIES_ADD = prove
    (`!A:num->real^N^M A0 B B0 s.
     (A msums A0) s /\ (B msums B0) s ==> ((\n. A n + B n) msums (A0 + B0)) s`,
    SIMP_TAC[msums; FINITE_INTER_NUMSEG; MSUM_ADD; MATRIX_LIM_ADD]);;

let MSERIES_SUB = prove
    (`!A:num->real^N^M A0 B B0 s.
     (A msums A0) s /\ (B msums B0) s ==> ((\n. A n - B n) msums (A0 - B0)) s`,
    SIMP_TAC[msums; FINITE_INTER_NUMSEG; MSUM_SUB; MATRIX_LIM_SUB]);;

let MSERIES_CMUL = prove
    (`!A:num->real^N^M A0 c s. (A msums A0) s ==> ((\n. c %% A n) msums (c %% A0)) s`,
    SIMP_TAC[msums; FINITE_INTER_NUMSEG; MSUM_LMUL; MATRIX_LIM_CMUL]);;
  
let MSERIES_NEG = prove
    (`!A:num->real^N^M A0 s. (A msums A0) s ==> ((\n. --(A n)) msums (--A0)) s`,
    SIMP_TAC[msums; FINITE_INTER_NUMSEG; MSUM_NEG; MATRIX_LIM_NEG]);;
    
let MSERIES_TRIVIAL = prove
    (`!f:num->real^N^M. (f msums mat 0) {}`,
    REWRITE_TAC[msums; INTER_EMPTY; MSUM_CLAUSES; MATRIX_LIM_CONST]);;
   
let MSUMS_REINDEX = prove
    (`!k a l:real^N^M n.
   ((\x. a(x + k)) msums l) (from n) <=> (a msums l) (from(n + k))`,
    REPEAT GEN_TAC THEN REWRITE_TAC[msums; FROM_INTER_NUMSEG] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MSUM_OFFSET] THEN
    REWRITE_TAC[MATRIX_LIM_SEQUENTIALLY] THEN
    ASM_MESON_TAC[ARITH_RULE `N + k:num <= n ==> n = (n - k) + k /\ N <= n - k`;
                ARITH_RULE `N + k:num <= n ==> N <= n + k`]);;
   
let MSERIES_EVEN = prove
    (`!f l:real^N^M n.
        (f msums l) (from n) <=>
        ((\i. if EVEN i then f(i DIV 2) else mat 0) msums l) (from (2 * n))`,
    let lemma = prove
    (`msum(2 * m..n) (\i. if EVEN i then f i else mat 0):real^N^M =
        msum(m..n DIV 2) (\i. f(2 * i))`,
    TRANS_TAC EQ_TRANS
     `msum (2 * m..2 * (n DIV 2) + 1)
           (\i. if EVEN i then f i else mat 0):real^N^M` THEN
    CONJ_TAC THENL
    [ALL_TAC;
     REWRITE_TAC[MSUM_PAIR] THEN
     REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN; MATRIX_ADD_RID]] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MSUM_EQ_SUPERSET THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; SUBSET_NUMSEG] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `p = 2 * n DIV 2 + 1` SUBST1_TAC
    THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN]) in
    REPEAT GEN_TAC THEN REWRITE_TAC[MSERIES_FROM; lemma] THEN
    REWRITE_TAC[ARITH_RULE `(2 * i) DIV 2 = i`; ETA_AX] THEN
    REWRITE_TAC[matrixtendsto] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `e:real` THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    ABBREV_TAC `P m <=> matrix_dist(msum (n..m) f:real^N^M,l) < e` THEN
    POP_ASSUM(K ALL_TAC) THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    EXISTS_TAC `2 * N` THEN ASM_SIMP_TAC[GSYM LE_RDIV_EQ; ARITH_EQ] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `2 * n`) THEN
    REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;
  
let MSERIES_ODD = prove
    (`!f l:real^N^M n.
        (f msums l) (from n) <=>
        ((\i. if ODD i then f(i DIV 2) else mat 0) msums l) (from (2 * n + 1))`,
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [MSERIES_EVEN] THEN
    REWRITE_TAC[GSYM MSUMS_REINDEX] THEN
    REWRITE_TAC[ODD_ADD; ARITH_ODD; NOT_ODD] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
    SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[ARITH_RULE `(2 * m + 1) DIV 2 = m`] THEN
    REWRITE_TAC[ARITH_RULE `(2 * m) DIV 2 = m`]);;

(* ------------------------------------------------------------------------- *)
(* Cauchy criterion for matrix series.                                              *)
(* ------------------------------------------------------------------------- *)

let MATRIX_SEQUENCE_CAUCHY_WLOG = prove
 (`!P s:num->real^N^M. (!m n:num. P m /\ P n ==> matrix_dist(s m,s n) < e) <=>
         (!m n. P m /\ P n /\ m <= n ==> matrix_dist(s m,s n) < e)`,
  MESON_TAC[MATRIX_DIST_SYM; LE_CASES]);;
  
let MSUM_DIFF_LEMMA = prove
 (`!f:num->real^N^M k m n.
        m <= n
        ==> msum(k INTER (0..n)) f - msum(k INTER (0..m)) f =
            msum(k INTER (m+1..n)) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real^N^M`; `k INTER (0..n)`; `k INTER (0..m)`]
    MSUM_DIFF) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_INTER; FINITE_NUMSEG] THEN MATCH_MP_TAC
     (SET_RULE `s SUBSET t ==> (u INTER s SUBSET u INTER t)`) THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG] THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[SET_RULE
     `(k INTER s) DIFF (k INTER t) = k INTER (s DIFF t)`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_DIFF; IN_NUMSEG] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC]);;
    
let FNORM_MSUM_TRIVIAL_LEMMA = prove
 (`!f:num->real^N^M s e. &0 < e ==> (P ==> fnorm(msum(s INTER (m..n)) f) < e <=>
                   P ==> n < m \/ fnorm(msum(s INTER (m..n)) f) < e)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n:num < m` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [GSYM NUMSEG_EMPTY]) THEN
  ASM_REWRITE_TAC[MSUM_CLAUSES; FNORM_0; INTER_EMPTY]);;

let MSERIES_CAUCHY = prove
 (`!f:num->real^N^M s. (?l. (f msums l) s) =
         !e. &0 < e
             ==> ?N. !m n. m >= N
                           ==> fnorm(msum(s INTER (m..n)) f) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[msums; MATRIX_CONVERGENT_EQ_CAUCHY; matrix_cauchy] THEN
  REWRITE_TAC[MATRIX_SEQUENCE_CAUCHY_WLOG] THEN ONCE_REWRITE_TAC[MATRIX_DIST_SYM] THEN
  SIMP_TAC[matrix_dist; MSUM_DIFF_LEMMA; FNORM_MSUM_TRIVIAL_LEMMA] THEN
  REWRITE_TAC[GE; TAUT `a ==> b \/ c <=> a /\ ~b ==> c`] THEN
  REWRITE_TAC[NOT_LT; ARITH_RULE
   `(N <= m /\ N <= n /\ m <= n) /\ m + 1 <= n <=>
    N + 1 <= m + 1 /\ m + 1 <= n`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THENL
   [EXISTS_TAC `N + 1`; EXISTS_TAC `N:num`] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `N + 1 <= m + 1 ==> N <= m + 1`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m - 1`; `n:num`]) THEN
  SUBGOAL_THEN `m - 1 + 1 = m` SUBST_ALL_TAC THENL
   [ALL_TAC; ANTS_TAC THEN SIMP_TAC[]] THEN
  ASM_ARITH_TAC);;
    
let MSUMMABLE_CAUCHY = prove
 (`!f:num->real^N^M s. msummable s f <=>
         !e. &0 < e
             ==> ?N. !m n. m >= N ==> fnorm(msum(s INTER (m..n)) f) < e`,
  REWRITE_TAC[msummable; GSYM MSERIES_CAUCHY]);;
  
(* ------------------------------------------------------------------------- *)
(* Comparison test for matrix series                                         *)
(* ------------------------------------------------------------------------- *)    

let MSERIES_COMPARISON = prove
 (`!f g s. (?l. ((lift_lift o g) msums l) s) /\
           (?N. !n. n >= N /\ n IN s ==> fnorm(f n) <= g n)
           ==> ?l:real^N^M. (f msums l) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MSERIES_CAUCHY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `N1:num`)) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N1 + N2:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `fnorm (msum (s INTER (m .. n)) (lift_lift o g))` THEN 
  CONJ_TAC THENL
   [SIMP_TAC[GSYM LIFT2_SUM; FINITE_INTER_NUMSEG; FNORM_LIFT2] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs(a)`) THEN
    MATCH_MP_TAC MSUM_FNORM_LE THEN
    REWRITE_TAC[FINITE_INTER_NUMSEG; IN_INTER; IN_NUMSEG] THEN
    ASM_MESON_TAC[ARITH_RULE `m >= N1 + N2:num /\ m <= x ==> x >= N1`];
    ASM_MESON_TAC[ARITH_RULE `m >= N1 + N2:num ==> m >= N2`]]);;    
    
(* ------------------------------------------------------------------------- *)
(* Ratio test of matrix series                                              *)
(* ------------------------------------------------------------------------- *)
 
let MSERIES_RATIO = prove
 (`!c a s N.
      c < &1 /\
      (!n. n >= N ==> fnorm(a(SUC n)) <= c * fnorm(a(n)))
      ==> ?l:real^N^M. (a msums l) s`,
  REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MSERIES_COMPARISON THEN
  DISJ_CASES_TAC(REAL_ARITH `c <= &0 \/ &0 < c`) THENL
   [EXISTS_TAC `\n:num. &0` THEN REWRITE_TAC[o_DEF; LIFT2_NUM] THEN
    CONJ_TAC THENL [MESON_TAC[MSERIES_0]; ALL_TAC] THEN
    EXISTS_TAC `N + 1` THEN REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN 
    EXISTS_TAC `c * fnorm(a(n - 1):real^N^M)` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `N + 1 <= n ==> SUC(n - 1) = n /\ N <= n - 1`];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= --c * x ==> c * x <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[FNORM_POS_LE] THEN
    UNDISCH_TAC `c <= &0` THEN REAL_ARITH_TAC;
    ASSUME_TAC(MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < c`))] THEN
  EXISTS_TAC `\n. fnorm(a(N):real^N^M) * c pow (n - N)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `N:num` THEN
    SIMP_TAC[GE; LE_EXISTS; IMP_CONJ; ADD_SUB2; LEFT_IMP_EXISTS_THM] THEN
    SUBGOAL_THEN `!d:num. fnorm(a(N + d):real^N^M) <= fnorm(a N) * c pow d`
     (fun th -> MESON_TAC[th]) THEN INDUCT_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; real_pow; REAL_MUL_RID; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * fnorm((a:num->real^N^M) (N + d))` THEN
    ASM_SIMP_TAC[LE_ADD] THEN ASM_MESON_TAC[REAL_LE_LMUL; REAL_MUL_AC]] THEN
  GEN_REWRITE_TAC I [MSERIES_CAUCHY] THEN X_GEN_TAC `e:real` THEN
  SIMP_TAC[GSYM LIFT2_SUM; FINITE_INTER; FNORM_LIFT2; FINITE_NUMSEG] THEN
  DISCH_TAC THEN SIMP_TAC[SUM_LMUL; FINITE_INTER; FINITE_NUMSEG] THEN
  ASM_CASES_TAC `(a:num->real^N^M) N = mat 0:real^N^M` THENL
   [ASM_REWRITE_TAC[FNORM_0; REAL_MUL_LZERO; REAL_ABS_NUM]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `((&1 - c) * e) / fnorm((a:num->real^N^M) N)`]
               REAL_ARCH_POW_INV) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_SUB_LT; FNORM_POS_LT; GE] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN EXISTS_TAC `N + M:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs(fnorm((a:num->real^N^M) N) *
                  sum(m..n) (\i. c pow (i - N)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= abs y`) THEN
    ASM_SIMP_TAC[SUM_POS_LE; FINITE_INTER_NUMSEG; REAL_POW_LE] THEN
    MATCH_MP_TAC SUM_SUBSET THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
    REWRITE_TAC[FINITE_INTER_NUMSEG; FINITE_NUMSEG] THEN
    REWRITE_TAC[IN_INTER; IN_DIFF] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_FNORM] THEN
  DISJ_CASES_TAC(ARITH_RULE `n:num < m \/ m <= n`) THENL
   [ASM_SIMP_TAC[SUM_TRIV_NUMSEG; REAL_ABS_NUM; REAL_MUL_RZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `m = 0 + m /\ n = (n - m) + m` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `m:num <= n` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET] THEN UNDISCH_TAC `N + M:num <= m` THEN
  SIMP_TAC[LE_EXISTS] THEN DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[ARITH_RULE `(i + (N + M) + d) - N:num = (M + d) + i`] THEN
  ONCE_REWRITE_TAC[REAL_POW_ADD] THEN REWRITE_TAC[SUM_LMUL; SUM_GP] THEN
  ASM_SIMP_TAC[LT; REAL_LT_IMP_NE] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; FNORM_POS_LT; REAL_ABS_MUL] THEN
  REWRITE_TAC[REAL_ABS_POW] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ABS_DIV; REAL_POW_LT; REAL_ARITH
   `&0 < c /\ c < &1 ==> &0 < abs c /\ &0 < abs(&1 - c)`; REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 < x /\ x <= &1 /\ &1 <= e ==> abs(c pow 0 - x) < e`) THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_POW_1_LE; REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[REAL_ARITH `c < &1 ==> x * abs(&1 - c) = (&1 - c) * x`] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_POW_ADD; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_ARITH
   `!a:real b:real c:real d:real e:real. 
     (((a * b) * c) * d) * e = (e * ((a * b) * c)) * d`] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_MUL_LID;
               REAL_ARITH `&0 < c ==> abs c = c`] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `xm < e ==> &0 <= (d - &1) * e ==> xm <= d * e`)) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_SUB_LE; GSYM REAL_POW_INV] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN
    MATCH_MP_TAC REAL_INV_1_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_MUL; REAL_LT_DIV; FNORM_POS_LT]]);;

(* ------------------------------------------------------------------------- *)
(* linear function R^M^N ->-> R^P^Q in matrix space                           *)
(* ------------------------------------------------------------------------- *)      

let mlinear = new_definition
  `mlinear (f:real^M^N->real^P^Q) <=>
        (!x y. f(x + y) = f(x) + f(y)) /\
        (!c x. f(c %% x) = c %% f(x))`;;
        
let MLINEAR_COMPOSE_CMUL = prove
 (`!f:real^M^N->real^P^Q c. mlinear f ==> mlinear (\x. c %% f(x))`,
  SIMP_TAC[mlinear] THEN REPEAT STRIP_TAC THEN CMATRIX_ARITH_TAC);;

let MLINEAR_COMPOSE_NEG = prove
 (`!f:real^M^N->real^P^Q. mlinear f ==> mlinear (\x. --(f(x)))`,
  SIMP_TAC[mlinear] THEN REPEAT STRIP_TAC THEN CMATRIX_ARITH_TAC);;

let MLINEAR_COMPOSE_NEG_EQ = prove
 (`!f:real^M^N->real^P^Q. mlinear(\x. --(f x)) <=> mlinear f`,
  MATCH_MP_TAC(MESON[]
   `(!x. P x ==> P(f x)) /\ (!x. f(f x) = x)
    ==> (!x. P(f x) <=> P x)`) THEN
  REWRITE_TAC[MLINEAR_COMPOSE_NEG; MATRIX_NEG_NEG; ETA_AX]);;

let MLINEAR_COMPOSE_ADD = prove
 (`!f g:real^M^N->real^P^Q. mlinear f /\ mlinear g ==> mlinear (\x. f(x) + g(x))`,
  SIMP_TAC[mlinear] THEN REPEAT STRIP_TAC THEN CMATRIX_ARITH_TAC);;

let MLINEAR_COMPOSE_SUB = prove
 (`!f g:real^M^N->real^P^Q. mlinear f /\ mlinear g ==> mlinear (\x. f(x) - g(x))`,
  SIMP_TAC[mlinear] THEN REPEAT STRIP_TAC THEN CMATRIX_ARITH_TAC);;
  
let MLINEAR_COMPOSE_RMUL = prove
 (`!f A:real^N^M. mlinear f ==> mlinear (\x. f(x) ** A)`,
 SIMP_TAC[mlinear] THEN REPEAT STRIP_TAC THEN 
 SIMP_TAC[MATRIX_ADD_RDISTRIB; MATRIX_ADD_LDISTRIB;
          MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;
          
let MLINEAR_COMPOSE_LMUL = prove
 (`!f A:real^N^M. mlinear f ==> mlinear (\x. A ** f(x))`,
 SIMP_TAC[mlinear] THEN REPEAT STRIP_TAC THEN 
 SIMP_TAC[MATRIX_ADD_RDISTRIB; MATRIX_ADD_LDISTRIB;
          MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

let MLINEAR_COMPOSE = prove
 (`!f g:real^M^N->real^P^Q. mlinear f /\ mlinear g ==> mlinear (g o f)`,
  SIMP_TAC[mlinear; o_THM]);;

let MLINEAR_ID = prove
 (`mlinear (\x. x)`,
  REWRITE_TAC[mlinear]);;

let MLINEAR_I = prove
 (`mlinear I`,
  REWRITE_TAC[I_DEF; MLINEAR_ID]);;

let MLINEAR_ZERO = prove
 (`mlinear (\x. mat 0)`,
  REWRITE_TAC[mlinear] THEN CONJ_TAC THEN CMATRIX_ARITH_TAC);;

let MLINEAR_NEGATION = prove
 (`mlinear(--)`,
  REWRITE_TAC[mlinear] THEN CMATRIX_ARITH_TAC);;
  
let MLINEAR_DROP2_CMUL = prove
(`!A:real^N^M x: real^1^1. mlinear (\x. drop_drop x %% A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [mlinear] THEN 
  SIMP_TAC [DROP2_ADD; DROP2_CMUL] THEN 
  SIMP_TAC [MATRIX_CMUL_ADD_RDISTRIB; MATRIX_CMUL_ASSOC]);;

let MLINEAR_COMPOSE_MSUM = prove
 (`!f:real^M^N->real^P^Q->real^K^R s. FINITE s /\ (!a. a IN s ==> mlinear(f a))
         ==> mlinear(\x. msum s (\a. f a x))`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MSUM_CLAUSES; MLINEAR_ZERO] THEN
  ASM_SIMP_TAC[ETA_AX; IN_INSERT; MLINEAR_COMPOSE_ADD]);;

let MLINEAR_MMUL_COMPONENT = prove
 (`!f:real^M^N->real^P^Q v i j.
     mlinear f /\ 1 <= i /\ i <= dimindex(:Q) /\ 1 <= j /\ j <= dimindex(:P)
     ==> mlinear (\x. f(x)$i$j %% v)`,
  SIMP_TAC[mlinear; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN CMATRIX_ARITH_TAC);;

let MLINEAR_0 = prove
 (`!f:real^M^N->real^P^Q. mlinear f ==> (f(mat 0) = mat 0)`,
  MESON_TAC[MATRIX_CMUL_LZERO; mlinear]);;

let MLINEAR_CMUL = prove
 (`!f:real^M^N->real^P^Q c x. mlinear f ==> (f(c %% x) = c %% f(x))`,
  SIMP_TAC[mlinear]);;

let MLINEAR_NEG = prove
 (`!f:real^M^N->real^P^Q x. mlinear f ==> (f(--x) = --(f x))`,
  ONCE_REWRITE_TAC[MATRIX_NEG_MINUS1] THEN SIMP_TAC[MLINEAR_CMUL]);;

let MLINEAR_ADD = prove
 (`!f:real^M^N->real^P^Q x y. mlinear f ==> (f(x + y) = f(x) + f(y))`,
  SIMP_TAC[mlinear]);;

let MLINEAR_SUB = prove
 (`!f:real^M^N->real^P^Q x y. mlinear f ==> (f(x - y) = f(x) - f(y))`,
  SIMP_TAC[MATRIX_SUB; MLINEAR_ADD; MLINEAR_NEG]);;

let MLINEAR_MSUM = prove
 (`!f:real^M^N->real^P^Q g s. mlinear f /\ FINITE s ==> (f(msum s g) = msum s (f o g))`,
  GEN_TAC THEN GEN_TAC THEN SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MSUM_CLAUSES] THEN FIRST_ASSUM(fun th ->
    SIMP_TAC[MATCH_MP MLINEAR_0 th; MATCH_MP MLINEAR_ADD th; o_THM]));;
    
(*let MLINEAR_MSUM1 = prove
 (`!f g s t. mlinear f /\ FINITE s /\ FINITE t ==> 
     (f(msum t (\y. (msum s (\x. g x y)))) = 
      msum t (\y. (msum s (\x. f o g (x,y))))))`,
  GEN_TAC THEN GEN_TAC THEN SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MSUM_CLAUSES] THEN FIRST_ASSUM(fun th ->
    SIMP_TAC[MATCH_MP MLINEAR_0 th; MATCH_MP MLINEAR_ADD th; o_THM]));;*)
    
let LINEAR_MSUM_MUL = prove
 (`!f:real^M^N->real^P^Q s c v.
        mlinear f /\ FINITE s
        ==> f(msum s (\i. c i %% v i)) = msum s (\i. c(i) %% f(v i))`,
  SIMP_TAC[MLINEAR_MSUM; o_DEF; MLINEAR_CMUL]);;

let MLINEAR_INJECTIVE_0 = prove
 (`!f:real^M^N->real^P^Q. mlinear f
       ==> ((!x y. (f(x) = f(y)) ==> (x = y)) <=>
            (!x. (f(x) = mat 0) ==> (x = mat 0)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM MATRIX_SUB_EQ] THEN
  ASM_SIMP_TAC[GSYM MLINEAR_SUB] THEN MESON_TAC[MATRIX_SUB_RZERO]);;

let MBASIS_EXPANSION = prove
    (`!x:real^N^M. msum(1..dimindex(:N)) 
            (\j. msum(1..dimindex(:M)) (\i. x$i$j %% ((lambda a b. if a = i /\ b = j then &1 else &0):real^N^M))) = x`,
    SIMP_TAC[CART_EQ; MSUM_COMPONENT; 
           MATRIX_CMUL_COMPONENT; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[REAL_MUL_RZERO;REAL_MUL_RID] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  SIMP_TAC[GSYM (SIMP_RULE [SUM_DELTA] SUM_SUM_DELTA);GSYM IN_SING] THEN
  ASM_SIMP_TAC[IN_SING;SUM_DELTA;SUM_SUM_DELTA;IN_NUMSEG]);;  
  
let MLINEAR_BOUNDED = prove
 (`!f:real^M^N->real^P^Q. mlinear f ==> ?B. !x. fnorm(f x) <= B * fnorm(x)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC
   `sum (1..dimindex(:M)) (\j. 
   sum (1..dimindex(:N)) (\i. fnorm((f:real^M^N->real^P^Q)(lambda a b. if a = i /\ b = j then &1 else &0))))` THEN
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) 
                   [GSYM MBASIS_EXPANSION] THEN
  ASM_SIMP_TAC[MLINEAR_MSUM; FINITE_NUMSEG] THEN
  SIMP_TAC [o_DEF] THEN ASM_SIMP_TAC[MLINEAR_MSUM; FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  SIMP_TAC [o_DEF] THEN 
  MATCH_MP_TAC MSUM_FNORM_LE1 THEN
  SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  ASM_SIMP_TAC[FNORM_MUL; MLINEAR_CMUL] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL; FNORM_POS_LE; COMPONENT_LE_FNORM]);;

let MLINEAR_BOUNDED_POS = prove
 (`!f:real^M^N->real^P^Q. mlinear f ==> 
      ?B. &0 < B /\ !x. fnorm(f x) <= B * fnorm(x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B:real` o MATCH_MP MLINEAR_BOUNDED) THEN
  EXISTS_TAC `abs(B) + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[FNORM_POS_LE] THEN
  REAL_ARITH_TAC);;

let SYMMETRIC_MLINEAR_IMAGE = prove
 (`!f:real^M^N->real^P^Q s. (!x. x IN s ==> --x IN s) /\ mlinear f
          ==> !x. x IN (IMAGE f s) ==> --x IN (IMAGE f s)`,
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  SIMP_TAC[GSYM MLINEAR_NEG] THEN SET_TAC[]);;
  
let MLINEAR_COMPONENTWISE = prove
 (`!f:real^N^M->real^Q^P.
        mlinear f <=>
        !i j. (1 <= i /\ i <= dimindex(:P)) /\ (1 <= j /\ j <= dimindex(:Q))
        ==> mlinear(\x. lift_lift(f(x)$i$j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlinear] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CART_EQ] THEN 
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CART_EQ] THEN 
  SIMP_TAC[GSYM LIFT2_CMUL; GSYM LIFT2_ADD; LIFT2_EQ] THEN
  SIMP_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
  [FIRST_X_ASSUM (MP_TAC o SPECL [`x:real^N^M`;`y:real^N^M`;`i:num`]) THEN 
   ASM_SIMP_TAC [];
   FIRST_X_ASSUM (MP_TAC o SPECL [`c:real`;`x:real^N^M`;`i:num`]) THEN 
   ASM_SIMP_TAC [];
   FIRST_X_ASSUM (MP_TAC o SPECL [`i:num`;`i':num`]) THEN 
   ASM_SIMP_TAC [];
   FIRST_X_ASSUM (MP_TAC o SPECL [`i:num`;`i':num`]) THEN 
   ASM_SIMP_TAC []]);;
   
(*
let MLINEAR_LIFT2_MIP = prove
 (`!a. mlinear(\x. lift_lift(a mip x))`,
  REWRITE_TAC[mlinear; MIP_RMUL; MIP_RADD; LIFT2_ADD; LIFT2_CMUL]);;
*)

(* ------------------------------------------------------------------------- *)
(* Bilinear functions.                                                       *)
(* ------------------------------------------------------------------------- *)

let bimlinear = new_definition
  `bimlinear f <=> (!x. mlinear(\y. f x y)) /\ (!y. mlinear(\x. f x y))`;;
  
let BIMLINEAR_MUL = prove
  (` bimlinear ( matrix_mul :real^N^M->real^P^N->real^P^M)`,
  SIMP_TAC [bimlinear; mlinear] THEN REPEAT STRIP_TAC THEN 
  CMATRIX_ARITH_TAC);;

let BIMLINEAR_SWAP = prove
 (`!op:real^N^M->real^Q^P->real^S^R.
        bimlinear(\x y. op y x) <=> bimlinear op`,
  REWRITE_TAC[bimlinear; ETA_AX] THEN MESON_TAC[]);;

let BIMLINEAR_LADD = prove
 (`!h:real^N^M->real^Q^P->real^S^R x y z. bimlinear h ==> h (x + y) z = (h x z) + (h y z)`,
  SIMP_TAC[bimlinear; mlinear]);;

let BIMLINEAR_RADD = prove
 (`!h:real^N^M->real^Q^P->real^S^R x y z. bimlinear h ==> h x (y + z) = (h x y) + (h x z)`,
  SIMP_TAC[bimlinear; mlinear]);;

let BIMLINEAR_LCMUL = prove
 (`!h:real^N^M->real^Q^P->real^S^R c x y. bimlinear h ==> h (c %% x) y = c %% (h x y)`,
  SIMP_TAC[bimlinear; mlinear]);;

let BIMLINEAR_RCMUL = prove
 (`!h:real^N^M->real^Q^P->real^S^R c x y. bimlinear h ==> h x (c %% y) = c %% (h x y)`,
  SIMP_TAC[bimlinear; mlinear]);;

let BIMLINEAR_LNEG = prove
 (`!h:real^N^M->real^Q^P->real^S^R x y. bimlinear h ==> h (--x) y = --(h x y)`,
  ONCE_REWRITE_TAC[MATRIX_NEG_MINUS1] THEN SIMP_TAC[BIMLINEAR_LCMUL]);;

let BIMLINEAR_RNEG = prove
 (`!h:real^N^M->real^Q^P->real^S^R x y. bimlinear h ==> h x (--y) = --(h x y)`,
  ONCE_REWRITE_TAC[MATRIX_NEG_MINUS1] THEN SIMP_TAC[BIMLINEAR_RCMUL]);;

let BIMLINEAR_LZERO = prove
 (`!h:real^N^M->real^Q^P->real^S^R x. bimlinear h ==> h (mat 0) x = mat 0`,
  ONCE_REWRITE_TAC[CMATRIX_ARITH `(x:real^N^M) = mat 0 <=> x + x = x`] THEN
  SIMP_TAC[GSYM BIMLINEAR_LADD; MATRIX_ADD_LID]);;

let BIMLINEAR_RZERO = prove
 (`!h:real^N^M->real^Q^P->real^S^R x. bimlinear h ==> h x (mat 0) = mat 0`,
  ONCE_REWRITE_TAC[CMATRIX_ARITH `(x:real^N^M) = mat 0 <=> x + x = x`] THEN
  SIMP_TAC[GSYM BIMLINEAR_RADD; MATRIX_ADD_LID]);;

let BIMLINEAR_LSUB = prove
 (`!h:real^N^M->real^Q^P->real^S^R x y z. bimlinear h ==> h (x - y) z = (h x z) - (h y z)`,
  SIMP_TAC[MATRIX_SUB; BIMLINEAR_LNEG; BIMLINEAR_LADD]);;

let BIMLINEAR_RSUB = prove
 (`!h:real^N^M->real^Q^P->real^S^R x y z. bimlinear h ==> h x (y - z) = (h x y) - (h x z)`,
  SIMP_TAC[MATRIX_SUB; BIMLINEAR_RNEG; BIMLINEAR_RADD]);;

let BIMLINEAR_LSUM = prove
 (`!bop:real^N^M->real^Q^P->real^S^R f s:A->bool y.
        bimlinear bop /\ FINITE s
        ==> bop(msum s f) y = msum s (\i. bop (f i) y)`,
  REWRITE_TAC[bimlinear] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `y:real^Q^P`) THEN
  DISCH_THEN(MP_TAC o
   ISPECL [`f:A->real^N^M`; `s:A->bool`] o
   MATCH_MP (REWRITE_RULE[IMP_CONJ] MLINEAR_MSUM)) THEN
  ASM_REWRITE_TAC[o_DEF]);;

let BIMLINEAR_RSUM = prove
 (`!bop:real^N^M->real^Q^P->real^S^R f s:A->bool x.
        bimlinear bop /\ FINITE s
        ==> bop x (msum s f) = msum s (\i. bop x (f i))`,
  REWRITE_TAC[bimlinear] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^N^M`) THEN
  DISCH_THEN(MP_TAC o
   ISPECL [`f:A->real^Q^P`; `s:A->bool`] o
   MATCH_MP (REWRITE_RULE[IMP_CONJ] MLINEAR_MSUM)) THEN
  ASM_REWRITE_TAC[o_DEF]);;
  
let BIMLINEAR_MSUM = prove
 (`!h:real^N^M->real^Q^P->real^S^R s:A->bool t: B->bool.
       bimlinear h /\ FINITE s /\ FINITE t
       ==> h (msum s f) (msum t g) = msum s (\i. msum t (\j. h (f i) (g j)))`,
  SIMP_TAC[TAUT `a /\ b /\ c ==> d <=> c ==> a ==> b ==> d`] THEN
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MSUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[BIMLINEAR_RZERO; MSUM_0] THEN
  ASM_SIMP_TAC[BIMLINEAR_RADD; MSUM_ADD] THEN
  SIMP_TAC[CMATRIX_ARITH `!B:real^N^M. A + B = C + B <=> A = C`] THEN
  ASM_SIMP_TAC[BIMLINEAR_LSUM]);;
    
let BIMLINEAR_MSUM_MSUM = prove
(`!h:real^N^M->real^Q^P->real^S^R s1:A->bool t1: B->bool s2:C->bool t2: D->bool. 
  bimlinear h /\ FINITE s1 /\ FINITE t1 /\ FINITE s2 /\ FINITE t2 
  ==> h (msum s1 (\y1. 
         msum t1 (\x1. f x1 y1)))
        (msum s2 (\y2. 
         msum t2 (\x2. g x2 y2))) = 
      msum s1 (\y1. 
      msum t1 (\x1. 
      msum s2 (\y2. 
      msum t2 (\x2.
                    h (f x1 y1) (g x2 y2)))))`,
    SIMP_TAC[TAUT 
     `a /\ b /\ c /\ d /\ e ==> f <=> e ==> a ==> b ==> c==> d ==> f`] THEN 
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN 
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC[MSUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[BIMLINEAR_RZERO; MSUM_0] THEN
    ASM_SIMP_TAC[BIMLINEAR_RADD; MSUM_ADD] THEN
    SIMP_TAC[CMATRIX_ARITH `!B:real^N^M. A + B = C + B <=> A = C`] THEN
    ASM_SIMP_TAC[BIMLINEAR_LSUM] THEN POP_ASSUM MP_TAC THEN 
    SPEC_TAC (`s2:C->bool`,`s2:C->bool`) THEN 
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC[MSUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[BIMLINEAR_RZERO; MSUM_0] THEN
    ASM_SIMP_TAC[BIMLINEAR_RADD; MSUM_ADD] THEN
    SIMP_TAC[CMATRIX_ARITH `!B:real^N^M. A + B = C + B <=> A = C`] THEN
    ASM_SIMP_TAC[BIMLINEAR_LSUM]);;
       
(*let MSUM_FNORM_LE3 = prove
 (`!s1 s2 s3 s4 f:A->B->real^N^M g t1:C->D->A t2:E->F->B.
        FINITE (s1) /\ FINITE (s2) /\ FINITE (s3) /\ FINITE (s4) /\
        (!x1 y1 x2 y2. x1 IN s1 /\ y1 IN s2 /\ x2 IN s3 /\ y2 IN s4
        ==> fnorm(f (t1 x1 y1) (t2 x2 y2)) <= g (t1 x1 y1) (t2 x2 y2))
        ==> fnorm(msum s2 (\y1. msum s4 (\y2. msum s1 (\x1. msum s3 (\x2. f (t1 x1 y1) (t2 x2 y2)))))) 
             <= sum s2 (\y1. sum s4 (\y2. sum s1 (\x1. sum s3 (\x2. g (t1 x1 y1) (t2 x2 y2)))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s2 (\y1:D. sum s4 (\y2:F. sum s1 (\x1:C. sum s3 (\x2:E.fnorm (f (t1 x1 y1) (t2 x2 y2):real^N^M) ))))` THEN
  ASM_SIMP_TAC [SUM_SUM_LE;MSUM_FNORM3]);;  *)
    
let BIMLINEAR_BOUNDED = prove
 (`!h:real^N^M->real^Q^P->real^S^R.
        bimlinear h ==> ?B. !x y. fnorm(h x y) <= B * fnorm(x) * fnorm(y)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC 
   `sum (1..dimindex(:N)) (\j1. 
    sum (1..dimindex(:Q)) (\j2.
    sum (1..dimindex(:M)) (\i1. 
    sum (1..dimindex(:P)) (\i2.
    fnorm((h:real^N^M->real^Q^P->real^S^R) ((lambda a b. if a = i1 /\ b = j1 then &1 else &0):real^N^M) ((lambda a b. if a = i2 /\ b = j2 then &1 else &0):real^Q^P))))))` THEN 
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC
   (LAND_CONV o RAND_CONV o BINOP_CONV) [GSYM MBASIS_EXPANSION] THEN
   ASM_SIMP_TAC[BIMLINEAR_MSUM; FINITE_NUMSEG] THEN
   ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN 
   MATCH_MP_TAC MSUM_FNORM_LE3 THEN 
   SIMP_TAC [FINITE_NUMSEG; IN_NUMSEG] THEN 
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC [BIMLINEAR_RCMUL;BIMLINEAR_LCMUL] THEN 
   SIMP_TAC [FNORM_MUL] THEN REWRITE_TAC [REAL_MUL_ASSOC] THEN 
   ASM_MESON_TAC [REAL_LE_MUL; REAL_LE_MUL2; FNORM_POS_LE; REAL_ABS_POS; 
                  COMPONENT_LE_FNORM;REAL_LE_REFL]);;
     
let BIMLINEAR_BOUNDED_POS = prove
 (`!h:real^N^M->real^Q^P->real^S^R. bimlinear h
       ==> ?B. &0 < B /\ !x y. fnorm(h x y) <= B * fnorm(x) * fnorm(y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B:real` o MATCH_MP BIMLINEAR_BOUNDED) THEN
  EXISTS_TAC `abs(B) + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_RMUL THEN
         SIMP_TAC[FNORM_POS_LE; REAL_LE_MUL]) THEN
  REAL_ARITH_TAC);;
  
(* ------------------------------------------------------------------------- *)
(* Convexity of matrix set                                                   *)
(* ------------------------------------------------------------------------- *)

let matrix_convex = new_definition
  `matrix_convex (s:real^N^M->bool) <=>
        !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
                  ==> (u %% x + v %% y) IN s`;;
                  
let MATRIX_CONVEX_UNIV = prove
 (`matrix_convex(UNIV:real^N^M->bool)`,
  REWRITE_TAC[matrix_convex; IN_UNIV]);;
  
let MATRIX_CONVEX_INTERS = prove
 (`(!s:real^N^M->bool. s IN f ==> matrix_convex s) ==> matrix_convex(INTERS f)`,
  REWRITE_TAC[matrix_convex; IN_INTERS] THEN MESON_TAC[]);;
  
let MATRIX_CONVEX_EMPTY = prove
 (`matrix_convex {}`,
  REWRITE_TAC[matrix_convex; NOT_IN_EMPTY]);;
  
let MATRIX_CONVEX_SING = prove
 (`!a:real^N^M. matrix_convex {a}`,
  SIMP_TAC[matrix_convex; IN_SING; 
           GSYM MATRIX_CMUL_ADD_RDISTRIB; MATRIX_CMUL_LID]);;
  
let MATRIX_CONVEX_ALT = prove
 (`matrix_convex s <=> !x y u. x IN s /\ y IN s /\ &0 <= u /\ u <= &1
                        ==> ((&1 - u) %% x + u %% y) IN s`,
  REWRITE_TAC[matrix_convex] THEN
  MESON_TAC[REAL_ARITH `&0 <= u /\ &0 <= v /\ (u + v = &1)
                        ==> v <= &1 /\ (u = &1 - v)`;
            REAL_ARITH `u <= &1 ==> &0 <= &1 - u /\ ((&1 - u) + u = &1)`]);;
            
let IN_MATRIX_CONVEX_SET = prove
 (`!s:real^N^M->bool a b u.
        matrix_convex s /\ a IN s /\ b IN s /\ &0 <= u /\ u <= &1
        ==> ((&1 - u) %% a + u %% b) IN s`,
  MESON_TAC[MATRIX_CONVEX_ALT]);;
  
(* ------------------------------------------------------------------------- *)
(* Line segments, with open/closed overloading of (a,b) and [a,b].           *)
(* ------------------------------------------------------------------------- *)

let matrix_closed_segment = define
 `matrix_closed_segment[a,b] = {(&1 - u) %% a + u %% b | &0 <= u /\ u <= &1}`;;
 
let matrix_open_segment = new_definition
 `matrix_open_segment(a,b) = matrix_closed_segment[a,b] DIFF {a,b}`;;
 
let MATRIX_OPEN_SEGMENT_ALT = prove
 (`!a b:real^N^M.
        ~(a = b)
        ==> matrix_open_segment(a,b) = 
             {(&1 - u) %% a + u %% b | &0 < u /\ u < &1}`,
  let lem1 = prove
    (`!a b u. (&1 - u) %% a + u %% b = a <=> u %% (b - a) = mat 0`,
    REPEAT STRIP_TAC THEN
    SIMP_TAC [MAT_0_COMPONENT; CART_EQ; MATRIX_CMUL_COMPONENT;
              MATRIX_SUB_COMPONENT; MATRIX_ADD_COMPONENT;
              LAMBDA_BETA]
    THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[] THEN
    DISCH_THEN (MP_TAC o SPEC `i':num`) THEN ASM_ARITH_TAC) in
  let lem2 = prove
    (`!a b u. (&1 - u) %% a + u %% b = b <=> (&1 - u) %% (b - a) = mat 0`,
    REPEAT STRIP_TAC THEN
    SIMP_TAC [MAT_0_COMPONENT; CART_EQ; MATRIX_CMUL_COMPONENT;
              MATRIX_SUB_COMPONENT; MATRIX_ADD_COMPONENT;
              LAMBDA_BETA]
    THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[] THEN
    DISCH_THEN (MP_TAC o SPEC `i':num`) THEN ASM_ARITH_TAC) in      
  REPEAT STRIP_TAC THEN REWRITE_TAC[matrix_open_segment; 
                                    matrix_closed_segment] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N^M` THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `u:real` THEN ASM_CASES_TAC `x:real^N^M = (&1 - u) %% a + u %% b` THEN
  ASM_REWRITE_TAC[REAL_LE_LT; lem1; lem2;
    MATRIX_CMUL_EQ_0; REAL_SUB_0; MATRIX_SUB_EQ] THEN
  REAL_ARITH_TAC);;
  
make_overloadable "matrix_segment" `:A`;;

overload_interface("matrix_segment",`matrix_open_segment`);;
overload_interface("matrix_segment",`matrix_closed_segment`);;

let matrix_segment = prove
 (`(matrix_segment[a,b] = {(&1 - u) %% a + u %% b | &0 <= u /\ u <= &1}) /\
   (matrix_segment(a,b) = matrix_segment[a,b] DIFF {a,b})`,
  REWRITE_TAC[matrix_open_segment; matrix_closed_segment]);;
  
let matrix_midpoint = new_definition
 `!a:real^N^M b. matrix_midpoint(a,b) = inv(&2) %% (a + b)`;;
 
let MATRIX_SEGMENT_REFL = prove
 (`(!a. matrix_segment[a,a] = {a}) /\
   (!a. matrix_segment(a,a) = {})`,
  REWRITE_TAC[matrix_segment; MIP_ARITH `(&1 - u) %% a + u %% a = a`] THEN
  SET_TAC[REAL_POS]);;
  
let IN_MATRIX_SEGMENT = prove
 (`!a b x:real^N^M.
        (x IN matrix_segment[a,b] <=>
         ?u. &0 <= u /\ u <= &1 /\ x = (&1 - u) %% a + u %% b) /\
        (x IN matrix_segment(a,b) <=>
         ~(a = b) /\ ?u. &0 < u /\ u < &1 /\ x = (&1 - u) %% a + u %% b)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[matrix_segment; IN_ELIM_THM; CONJ_ASSOC]; ALL_TAC] THEN
  ASM_CASES_TAC `a:real^N^M = b` THEN
  ASM_REWRITE_TAC[MATRIX_SEGMENT_REFL; NOT_IN_EMPTY] THEN
  ASM_SIMP_TAC[MATRIX_OPEN_SEGMENT_ALT; IN_ELIM_THM; CONJ_ASSOC]);;
  
let MATRIX_MIDPOINT_IN_SEGMENT = prove
 (`(!a b:real^N^M. matrix_midpoint(a,b) IN matrix_segment[a,b]) /\
   (!a b:real^N^M. matrix_midpoint(a,b) IN matrix_segment(a,b) <=> ~(a = b))`,
  REWRITE_TAC[IN_MATRIX_SEGMENT] THEN REPEAT STRIP_TAC THENL
   [ALL_TAC; ASM_CASES_TAC `a:real^N^M = b` THEN ASM_REWRITE_TAC[]] THEN
  EXISTS_TAC `&1 / &2` THEN REWRITE_TAC[matrix_midpoint] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN CMATRIX_ARITH_TAC);;
    
let BETWEEN_IN_MATRIX_SEGMENT = prove
 (`!x a b:real^N^M. matrix_between x (a,b) <=> x IN matrix_segment[a,b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_between] THEN
  ASM_CASES_TAC `a:real^N^M = b` THEN
  ASM_REWRITE_TAC[MATRIX_SEGMENT_REFL; IN_SING] THENL 
  [REWRITE_TAC [MATRIX_DIST_REFL] THEN 
   SIMP_TAC [MATRIX_DIST_SYM; MATRIX_DIST_EQ_0;
   REAL_ARITH `(a = b) ==> (&0 = a + b <=> b = &0)`]; ALL_TAC] THEN
  REWRITE_TAC[matrix_segment; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(ASSUME_TAC o SYM) THEN
    EXISTS_TAC `matrix_dist(a:real^N^M,x) / matrix_dist(a,b)` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; 
                 MATRIX_DIST_POS_LT] THEN
    ASM_SIMP_TAC [REAL_MUL_LZERO; MATRIX_DIST_POS_LE; REAL_MUL_LID] THEN
    CONJ_TAC; ALL_TAC] THENL 
    [MP_TAC (SPECL [`x:real^N^M`;`b:real^N^M`] MATRIX_DIST_POS_LE) THEN
    ASM_ARITH_TAC; ALL_TAC; ALL_TAC] THENL 
    [MATCH_MP_TAC MATRIX_CMUL_LCANCEL_IMP THEN
     EXISTS_TAC `matrix_dist(a:real^N^M,b)` THEN
     ASM_SIMP_TAC[MATRIX_CMUL_ASSOC; MATRIX_CMUL_ADD_LDISTRIB; 
                  REAL_SUB_LDISTRIB; REAL_DIV_LMUL; 
                  REAL_MUL_RID;MATRIX_DIST_EQ_0] THEN
     FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATRIX_DIST_TRIANGLE_EQ] o SYM) THEN
     FIRST_ASSUM(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[matrix_dist; REAL_ADD_SUB] THEN
     SIMP_TAC [CART_EQ; MATRIX_CMUL_COMPONENT;
              MATRIX_SUB_COMPONENT; MATRIX_ADD_COMPONENT;
              LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[] THEN
     DISCH_THEN (MP_TAC o SPEC `i':num`) THEN ASM_ARITH_TAC;
     STRIP_TAC THEN ASM_REWRITE_TAC[matrix_dist] THEN
     REWRITE_TAC[MIP_ARITH `a - ((&1 - u) %% a + u %% b) = u %% (a - b)`;
                MIP_ARITH `((&1 - u) %% a + u %% b) - b = (&1 - u) %% (a - b)`;
                FNORM_MUL; GSYM REAL_ADD_LDISTRIB] THEN
     REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD]);;

let IN_MATRIX_INTERVAL_1 = prove
 (`!a b x:real^1^1.
        (x IN matrix_interval[a,b] <=> 
        drop_drop a <= drop_drop x /\ drop_drop x <= drop_drop b) /\
        (x IN matrix_interval(a,b) <=> 
        drop_drop a < drop_drop x /\ drop_drop x < drop_drop b)`,
  REWRITE_TAC[IN_MATRIX_INTERVAL; drop_drop; 
              DIMINDEX_1; LE_ANTISYM] THEN MESON_TAC[]);;
              
let MATRIX_INTERVAL_EQ_EMPTY_1 = prove
 (`!a b:real^1^1.
        (matrix_interval[a,b] = {} <=> drop_drop b < drop_drop a) /\
        (matrix_interval(a,b) = {} <=> drop_drop b <= drop_drop a)`,
  SIMP_TAC[MATRIX_INTERVAL_EQ_EMPTY; drop_drop; DIMINDEX_1; LE_ANTISYM] THEN
  MESON_TAC[]);;
  
let MATRIX_SEGMENT_1 = prove
 (`(!a b. matrix_segment[a,b] =
          if drop_drop a <= drop_drop b 
          then matrix_interval[a,b] 
          else matrix_interval[b,a]) /\
   (!a b. matrix_segment(a,b) =
          if drop_drop a <= drop_drop b 
          then matrix_interval(a,b) 
          else matrix_interval(b,a))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[matrix_open_segment] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY;
              EXTENSION; GSYM BETWEEN_IN_MATRIX_SEGMENT; 
              matrix_between; IN_MATRIX_INTERVAL_1] THEN
  REWRITE_TAC[GSYM DROP2_EQ; MATRIX_DIST_REAL; GSYM drop_drop] THEN 
  ASM_REAL_ARITH_TAC);;
  
let MATRIX_SEGMENT_OPEN_SUBSET_CLOSED = prove
 (`!a b:real^N^M. matrix_segment(a,b) SUBSET matrix_segment[a,b]`,
  REWRITE_TAC[CONJUNCT2(SPEC_ALL matrix_segment)] THEN SET_TAC[]);;
  
let MATRIX_SEGMENT_CONVEX_HULL = prove
 (`!a b. matrix_segment[a,b] = matrix_convex hull {a,b}`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[MATRIX_CONVEX_HULL_INSERT; MATRIX_CONVEX_HULL_SING; 
           NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[IN_SING; RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
  REWRITE_TAC[matrix_segment; EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[REAL_ARITH `u + v = &1 <=> u = &1 - v`] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> c /\ a /\ b /\ d`] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  REWRITE_TAC[REAL_LE_SUB_LADD; REAL_ADD_LID] THEN MESON_TAC[]);;
  
let MATRIX_BOUNDED_SEGMENT = prove
 (`(!a b:real^N^M. matrix_bounded(matrix_segment[a,b])) /\
   (!a b:real^N^M. matrix_bounded(matrix_segment(a,b)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(MESON[MATRIX_BOUNDED_SUBSET]
   `matrix_bounded s /\ t SUBSET s ==> matrix_bounded s /\ matrix_bounded t`) THEN
  REWRITE_TAC[MATRIX_SEGMENT_OPEN_SUBSET_CLOSED] THEN
  MATCH_MP_TAC MATRIX_COMPACT_IMP_BOUNDED THEN 
  REWRITE_TAC[MATRIX_SEGMENT_CONVEX_HULL] THEN
  MATCH_MP_TAC MATRIX_COMPACT_CONVEX_HULL THEN
  SIMP_TAC[MATRIX_COMPACT_INSERT; MATRIX_COMPACT_EMPTY]);;
  
let MATRIX_SEGMENT_IMAGE_INTERVAL = prove
 (`(!a b. matrix_segment[a,b] =
          IMAGE (\u. (&1 - drop_drop u) %% a + drop_drop u %% b)
                (matrix_interval[mat 0,mat 1])) /\
   (!a b. ~(a = b)
          ==> matrix_segment(a,b) =
                IMAGE (\u. (&1 - drop_drop u) %% a + drop_drop u %% b)
                (matrix_interval(mat 0,mat 1)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_MATRIX_INTERVAL_1; IN_MATRIX_SEGMENT] THEN
  ASM_REWRITE_TAC[GSYM EXISTS_DROP2; DROP2_MAT] THEN MESON_TAC[]);;
  
let MATRIX_OPEN_INTERVAL = prove
 (`!a:real^N^M b. matrix_open(matrix_interval (a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_open; matrix_interval; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i j. (1 <= i /\ i <= dimindex(:M)) /\
                      (1 <= j /\ j <= dimindex(:N))
                    ==> ?d. &0 < d /\
                            !x'. abs(x' - (x:real^N^M)$i$j) < d
                    ==> (a:real^N^M)$i$j < x' /\ x' < (b:real^N^M)$i$j`
  MP_TAC THENL [ASM_SIMP_TAC[OPEN_INTERVAL_LEMMA]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->num->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `inf (IMAGE (\(i,j). (d:num->num->real) i j) 
    {i,j | i IN 1..dimindex(:M) /\ j IN (1..dimindex(:N))})` THEN
  CONJ_TAC THEN TRY (X_GEN_TAC `A:real^N^M`) THEN 
  SIMP_TAC [GSYM CROSS] THEN 
  SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; FINITE_CROSS; FINITE_NUMSEG;
           IMAGE_EQ_EMPTY; NOT_INSERT_EMPTY; NUMSEG_EMPTY; CROSS_EQ_EMPTY;
           ARITH_RULE `n < 1 <=> (n = 0)`; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; matrix_dist] THENL
  [GEN_TAC THEN ONCE_REWRITE_TAC [GSYM PAIR] THEN 
   SIMP_TAC [IN_CROSS; IN_NUMSEG; FST; SND] THEN STRIP_TAC THEN 
   SUBST1_TAC (MESON [GSYM PAIR] `x':num#num = FST x', SND x'`) THEN 
   FIRST_X_ASSUM (MP_TAC o SPECL [`FST (x':num#num)`;`SND (x':num#num)`]) THEN
   ASM_SIMP_TAC []; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o ISPEC `(i:num,j:num)`) THEN 
   ASM_SIMP_TAC [IN_CROSS; IN_NUMSEG] THEN 
   ASM_MESON_TAC[COMPONENT_LE_FNORM; REAL_LET_TRANS; MATRIX_SUB_COMPONENT]);;
  
let MATRIX_CLOSED_INTERVAL = prove
 (`!a:real^N^M b. matrix_closed(matrix_interval [a,b])`,
  REWRITE_TAC[MATRIX_CLOSED_LIMPT; MATRIX_LIMPT_APPROACHABLE; 
              IN_MATRIX_INTERVAL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(a:real^N^M)$i$j - (x:real^N^M)$i$j`);
    FIRST_X_ASSUM(MP_TAC o SPEC `(x:real^N^M)$i$j - (b:real^N^M)$i$j`)] THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N^M` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[matrix_dist; REAL_NOT_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((z - x :real^N^M)$i$j)` THEN
  ASM_SIMP_TAC[COMPONENT_LE_FNORM] THEN
  ASM_SIMP_TAC[MATRIX_SUB_COMPONENT] THEN
  ASM_SIMP_TAC[REAL_ARITH `x < a /\ a <= z ==> a - x <= abs(z - x)`;
               REAL_ARITH `z <= b /\ b < x ==> x - b <= abs(z - x)`]);;
    
(* ------------------------------------------------------------------------- *)
(* Continuity of all kinds is preserved under composition.                   *)
(* ------------------------------------------------------------------------- *)

let MATRIX_CONTINUOUS_CLOSED_IN_PREIMAGE = prove
 (`!f s:real^N^M->bool t.
         f matrix_continuous_on s /\ matrix_closed t
         ==> closed_in (subtopology matrix_space s) {x | x IN s /\ f x IN t}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE
   `x IN s /\ f x IN t <=> x IN s /\ f x IN (t INTER IMAGE f s)`] THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[MATRIX_CONTINUOUS_ON_CLOSED]) THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC MATRIX_CLOSED_IN_CLOSED_INTER THEN
  ASM_REWRITE_TAC[]);; 

let MATRIX_CONTINUOUS_WITHIN_COMPOSE = prove
 (`!f g x s:real^N^M->bool. f matrix_continuous (matrix_at x within s) /\
             g matrix_continuous (matrix_at (f x) within IMAGE f s)
             ==> (g o f) matrix_continuous (matrix_at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_continuous_within; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;
  
let MATRIX_LIM_WITHIN_SUBSET = prove
 (`!f:real^N^M->real^P^Q l a s t.
    (f ->-> l) (matrix_at a within s) /\ t SUBSET s ==> 
    (f ->-> l) (matrix_at a within t)`,
  REWRITE_TAC[MATRIX_LIM_WITHIN; SUBSET] THEN MESON_TAC[]);;
  
let MATRIX_CONTINUOUS_WITHIN_SUBSET = prove
 (`!f s:real^N^M->bool t x. f matrix_continuous (matrix_at x within s) /\ t SUBSET s
             ==> f matrix_continuous (matrix_at x within t)`,
   REWRITE_TAC[MATRIX_CONTINUOUS_WITHIN] THEN 
   MESON_TAC[MATRIX_LIM_WITHIN_SUBSET]);;

let MATRIX_CONTINUOUS_AT_COMPOSE = prove
 (`!f g x:real^N^M. f matrix_continuous (matrix_at x) /\
           g matrix_continuous (matrix_at (f x))
           ==> (g o f) matrix_continuous (matrix_at x)`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  MESON_TAC[MATRIX_CONTINUOUS_WITHIN_COMPOSE; IN_IMAGE; 
            MATRIX_CONTINUOUS_WITHIN_SUBSET;
            SUBSET_UNIV; IN_UNIV]);;

let MATRIX_CONTINUOUS_ON_COMPOSE = prove
 (`!f g s:real^N^M->bool. f matrix_continuous_on s /\ g matrix_continuous_on (IMAGE f s)
           ==> (g o f) matrix_continuous_on s`,
  REWRITE_TAC[MATRIX_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  MESON_TAC[IN_IMAGE; MATRIX_CONTINUOUS_WITHIN_COMPOSE]);;
  
let MATRIX_CONTINUOUS_MMUL = prove
 (`!net c v. (lift_lift o c) matrix_continuous net ==> 
              (\x. c(x) %% v) matrix_continuous net`,
  REWRITE_TAC[matrix_continuous; MATRIX_LIM_MMUL; o_THM]);;
  
let MATRIX_CONTINUOUS_ON_MMUL = prove
 (`!s c v. (lift_lift o c) matrix_continuous_on s ==> 
           (\x. c(x) %% v) matrix_continuous_on s`,
  REWRITE_TAC[MATRIX_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  SIMP_TAC[MATRIX_CONTINUOUS_MMUL]);;
  
let MATRIX_CONTINUOUS_ON_SUBSET = prove
 (`!f s t:real^N^M->bool. f matrix_continuous_on s /\ t SUBSET s ==>
           f matrix_continuous_on t`,
  REWRITE_TAC[MATRIX_CONTINUOUS_ON] THEN 
  MESON_TAC[SUBSET; MATRIX_LIM_WITHIN_SUBSET]);;

let MLINEAR_LIM_0 = prove
 (`!f:real^N^M->real^Q^P. mlinear f ==> (f ->-> mat 0) (matrix_at (mat 0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_LIM_AT] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MLINEAR_BOUNDED_POS) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `e / B:real` THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN 
  REWRITE_TAC[matrix_dist; MATRIX_SUB_RZERO] THEN
  ASM_MESON_TAC[REAL_MUL_SYM; REAL_LET_TRANS; REAL_LT_RDIV_EQ]);;
  
let MLINEAR_CONTINUOUS_AT = prove
 (`!f:real^N^M->real^Q^P a. mlinear f ==> f matrix_continuous (matrix_at a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\x. (f:real^N^M->real^Q^P) (a + x) - f(a)` MLINEAR_LIM_0) THEN
  ANTS_TAC THENL
   [POP_ASSUM MP_TAC THEN SIMP_TAC[mlinear] THEN
    REPEAT STRIP_TAC THEN CMATRIX_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_LIM_NULL; MATRIX_CONTINUOUS_AT] THEN
  GEN_REWRITE_TAC RAND_CONV [MATRIX_LIM_AT_ZERO] THEN SIMP_TAC[]);;

let MLINEAR_CONTINUOUS_WITHIN = prove
 (`!f:real^N^M->real^Q^P s x. 
      mlinear f ==> f matrix_continuous (matrix_at x within s)`,
  SIMP_TAC[MATRIX_CONTINUOUS_AT_WITHIN; MLINEAR_CONTINUOUS_AT]);;

(**supplement to matrix lim**)

let MATRIX_LIM_LINEAR = prove
 (`!net:(A)net h f:A->real^N^M l.
        (f ->-> l) net /\ mlinear h ==> ((\x. h(f x)) ->-> h l) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrixtendsto] THEN
  STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o
    MATCH_MP MLINEAR_BOUNDED_POS) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / B :real`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; matrix_dist; GSYM MLINEAR_SUB; REAL_LT_RDIV_EQ] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_MUL_SYM]);;
  
let MATRIX_LIM_WITHIN_ID = prove
 (`!a s:real^N^M->bool. ((\x. x) ->-> a) (matrix_at a within s)`,
  REWRITE_TAC[MATRIX_LIM_WITHIN] THEN MESON_TAC[]);;

let UNIFORM_MATRIX_LIM_BILINEAR = prove
 (`!net:(A)net P (h:real^N^M->real^Q^P->real^S^R) f g l m b1 b2.
        bimlinear h /\
        eventually (\x. !n. P n ==> fnorm(l n) <= b1) net /\
        eventually (\x. !n. P n ==> fnorm(m n) <= b2) net /\
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> fnorm(f n x - l n) < e) net) /\
        (!e. &0 < e
             ==> eventually (\x. !n. P n ==> fnorm(g n x - m n) < e) net)
        ==> !e. &0 < e
                ==> eventually
                     (\x. !n. P n
                              ==> fnorm(h (f n x) (g n x) - h (l n) (m n)) < e)
                     net`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o  MATCH_MP
   BIMLINEAR_BOUNDED_POS) THEN
  REWRITE_TAC[AND_FORALL_THM; RIGHT_AND_FORALL_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `min (abs b2 + &1) (e / &2 / (B * (abs b1 + abs b2 + &2)))`) THEN
  ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; REAL_LT_MUL; REAL_LT_MIN;
               REAL_ARITH `&0 < abs x + &1`;
               REAL_ARITH `&0 < abs x + abs y + &2`] THEN
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:B` THEN
  ASM_CASES_TAC `(P:B->bool) n` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ONCE_REWRITE_TAC[CMATRIX_ARITH
    `h a b - h c d :real^Q^P = (h a b - h a d) + (h a d - h c d)`] THEN
  ASM_SIMP_TAC[GSYM BIMLINEAR_LSUB; GSYM BIMLINEAR_RSUB] THEN
  MATCH_MP_TAC FNORM_TRIANGLE_LT THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (MESON[REAL_LE_ADD2; REAL_LET_TRANS]
     `(!x y. fnorm((h:real^N^M->real^Q^P->real^S^R) x y) <= B * fnorm x * fnorm y)
       ==> B * fnorm a * fnorm b + B * fnorm c * fnorm d < e
           ==> fnorm(h a b) + fnorm(h c d) < e`)) THEN
  MATCH_MP_TAC(REAL_ARITH
   `x * B < e / &2 /\ y * B < e / &2 ==> B * x + B * y < e`) THEN
  CONJ_TAC THEN ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `e / &2 / (B * (abs b1 + abs b2 + &2)) *
             (abs b1 + abs b2 + &1)` THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL2 THEN
     ASM_SIMP_TAC[FNORM_POS_LE; REAL_LT_IMP_LE] THEN
     ASM_SIMP_TAC[REAL_ARITH `a <= b2 ==> a <= abs b1 + abs b2 + &1`] THEN
     ASM_MESON_TAC[prove
       (`fnorm(f - l:real^S^R) < abs b2 + &1 /\ fnorm(l) <= b1
        ==> fnorm(f) <= abs b1 + abs b2 + &1`, 
        REWRITE_TAC [FNORM_EQ_NORM_VECTORIZE;VECTORIZE_SUB] THEN NORM_ARITH_TAC)];
     ONCE_REWRITE_TAC[real_div] THEN
     ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_HALF; GSYM REAL_MUL_ASSOC;
                  REAL_INV_MUL] THEN
     REWRITE_TAC[REAL_ARITH `B * inv x * y < B <=> B * y / x < B * &1`] THEN
     ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_LT_LMUL_EQ; REAL_LT_LDIV_EQ;
                  REAL_ARITH `&0 < abs x + abs y + &2`] THEN
     REAL_ARITH_TAC]));;
  
let MATRIX_LIM_BILINEAR = prove
 (`!net:(A)net (h:real^N^M->real^Q^P->real^S^R) f g l m.
        (f ->-> l) net /\ (g ->-> m) net /\ bimlinear h
        ==> ((\x. h (f x) (g x)) ->-> (h l m)) net`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`net:(A)net`; `\x:one. T`; `h:real^N^M->real^Q^P->real^S^R`;
    `\n:one. (f:A->real^N^M)`; `\n:one. (g:A->real^Q^P)`;
    `\n:one. (l:real^N^M)`; `\n:one. (m:real^Q^P)`;
    `fnorm(l:real^N^M)`; `fnorm(m:real^Q^P)`]
   UNIFORM_MATRIX_LIM_BILINEAR) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; EVENTUALLY_TRUE] THEN
  ASM_REWRITE_TAC[GSYM matrix_dist; GSYM matrixtendsto]);;  
 
(* ------------------------------------------------------------------------- *)
(* Fréchet derivative defined in matrix space                                *)
(* ------------------------------------------------------------------------- *)    

parse_as_infix ("has_matrix_derivative",(12,"right"));;
parse_as_infix ("matrix_differentiable",(12,"right"));;
parse_as_infix ("matrix_differentiable_on",(12,"right"));;

let has_matrix_derivative = new_definition
  `((f:real^N^M->real^Q^P) has_matrix_derivative f') net <=>
        mlinear f' /\
        ((\y. inv(fnorm(y - netlimit net)) %%
              (f(y) -
               (f(netlimit net) + f'(y - netlimit net)))) ->-> mat 0) net`;;
               
let matrix_differentiable = new_definition
 `(f:real^N^M->real^Q^P) matrix_differentiable net <=> ?f'. (f has_matrix_derivative f') net`;;
 
let matrix_differentiable_on = new_definition
  `(f:real^N^M->real^Q^P) matrix_differentiable_on s <=> 
                !x. x IN s ==> f matrix_differentiable (matrix_at x within s)`;;
 
let has_matrix_derivative_within = prove
 (`!f:real^N^M->real^Q^P f' x s.
    (f has_matrix_derivative f') (matrix_at x within s) <=>
         mlinear f' /\
         ((\y. inv(fnorm(y - x)) %% (f(y) - (f(x) + f'(y - x)))) ->-> mat 0)
         (matrix_at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_matrix_derivative] THEN AP_TERM_TAC THEN
  ASM_CASES_TAC `trivial_limit(matrix_at (x:real^N^M) within s)` THEN
  ASM_SIMP_TAC[MATRIX_LIM_TRIVIAL; MATRIX_NETLIMIT_WITHIN]);;

let has_matrix_derivative_at = prove
 (`!f:real^N^M->real^Q^P f' x.
    (f has_matrix_derivative f') (matrix_at x) <=>
         mlinear f' /\
         ((\y. inv(fnorm(y - x)) %% (f(y) - (f(x) + f'(y - x)))) ->-> mat 0)
         (matrix_at x)`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  REWRITE_TAC[has_matrix_derivative_within]);;
 
let matrix_derivative = new_definition
 `matrix_derivative (f:real^N^M->real^Q^P) x = @f'. (f has_matrix_derivative f') (matrix_at x)`;;
 
let HAS_MATRIX_DERIVATIVE_WITHIN = prove
 (`((f:real^N^M->real^Q^P) has_matrix_derivative f')(matrix_at x within s) <=>
        mlinear f' /\
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x'. x' IN s /\
                         &0 < fnorm(x' - x) /\ fnorm(x' - x) < d
                         ==> fnorm(f(x') - f(x) - f'(x' - x)) /
                             fnorm(x' - x) < e`,
  SIMP_TAC[has_matrix_derivative_within; MATRIX_LIM_WITHIN] THEN 
  AP_TERM_TAC THEN
  REWRITE_TAC[matrix_dist; CMATRIX_ARITH 
              `(x' - (x + d)) = x' - x - d:real^N^M`] THEN
  REWRITE_TAC[real_div; MATRIX_SUB_RZERO; FNORM_MUL] THEN
  REWRITE_TAC[REAL_MUL_AC; REAL_ABS_INV; REAL_ABS_FNORM]);;
  
let HAS_MATRIX_DERIVATIVE_AT = prove
 (`((f:real^N^M->real^Q^P) has_matrix_derivative f')(matrix_at x) <=>
        mlinear f' /\
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x'. &0 < fnorm(x' - x) /\ fnorm(x' - x) < d
                         ==> fnorm(f(x') - f(x) - f'(x' - x)) /
                             fnorm(x' - x) < e`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  REWRITE_TAC[HAS_MATRIX_DERIVATIVE_WITHIN; IN_UNIV]);;
  
let HAS_MATRIX_DERIVATIVE_AT_WITHIN = prove
 (`!f:real^N^M->real^Q^P x s. (f has_matrix_derivative f') (matrix_at x)
           ==> (f has_matrix_derivative f') (matrix_at x within s)`,
  REWRITE_TAC[HAS_MATRIX_DERIVATIVE_WITHIN; HAS_MATRIX_DERIVATIVE_AT] THEN 
  MESON_TAC[]);;
  
let HAS_MATRIX_DERIVATIVE_WITHIN_OPEN = prove
 (`!f:real^N^M->real^Q^P f' a s.
         a IN s /\ matrix_open s
         ==> ((f has_matrix_derivative f') (matrix_at a within s) <=>
              (f has_matrix_derivative f') (matrix_at a))`,
  SIMP_TAC[has_matrix_derivative_within; has_matrix_derivative_at; 
           MATRIX_LIM_WITHIN_OPEN]);;
           
let HAS_MATRIX_DERIVATIVE_WITHIN_OPEN_IN = prove
 (`!f:real^N^M->real^Q^P f' a s u.
        a IN s /\ open_in (subtopology matrix_space u) s
        ==> ((f has_matrix_derivative f') (matrix_at a within s) <=>
             (f has_matrix_derivative f') (matrix_at a within u))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_matrix_derivative_within] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MATRIX_LIM_WITHIN_OPEN_IN THEN 
  ASM_REWRITE_TAC[]);;
  
(* ------------------------------------------------------------------------- *)
(* Combining theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_MATRIX_DERIVATIVE_LINEAR = prove
 (`!f:real^N^M->real^Q^P net. mlinear f ==> (f has_matrix_derivative f) net`,
  REWRITE_TAC[has_matrix_derivative; mlinear] THEN
  SIMP_TAC[CMATRIX_ARITH `x - y:real^N^M = x + --(&1) %% y`] THEN
  REWRITE_TAC[CMATRIX_ARITH `x:real^N^M + --(&1) %% (y + x + --(&1) %% y) = mat 0`] THEN
  REWRITE_TAC[MATRIX_CMUL_RZERO; MATRIX_LIM_CONST]);;
  
let HAS_MATRIX_DERIVATIVE_DROP2_CMUL = prove
 (`!net A:real^N^M. ((\x. (drop_drop x) %% A) has_matrix_derivative (\x. (drop_drop x) %% A)) net`,
 REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_MATRIX_DERIVATIVE_LINEAR THEN 
 SIMP_TAC [MLINEAR_DROP2_CMUL]);;

let HAS_MATRIX_DERIVATIVE_ID = prove
 (`!net:(real^N^M)net. ((\x. x) has_matrix_derivative (\h. h)) net`,
  SIMP_TAC[HAS_MATRIX_DERIVATIVE_LINEAR; MLINEAR_ID]);;

let HAS_MATRIX_DERIVATIVE_CONST = prove
 (`!c:real^N^M net. ((\x. c) has_matrix_derivative (\h. mat 0)) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_matrix_derivative; mlinear] THEN
  REWRITE_TAC[MATRIX_ADD_RID; MATRIX_SUB_REFL; 
              MATRIX_CMUL_RZERO; MATRIX_LIM_CONST]);;

let HAS_MATRIX_DERIVATIVE_LIFT_COMPONENT = prove
 (`!net:(real^N^M)net. 
      ((\x. lift_lift(x$i$j)) has_matrix_derivative (\x. lift_lift(x$i$j))) net`,
  GEN_TAC THEN MATCH_MP_TAC HAS_MATRIX_DERIVATIVE_LINEAR THEN
  REWRITE_TAC[mlinear; MATRIX_CMUL_COMPONENT; MATRIX_ADD_COMPONENT] THEN
  REWRITE_TAC[LIFT2_ADD; LIFT2_CMUL]);;

let HAS_MATRIX_DERIVATIVE_CMUL = prove
 (`!f:real^N^M->real^Q^P f' net c. (f has_matrix_derivative f') net
                ==> ((\x. c %% f(x)) has_matrix_derivative (\h. c %% f'(h))) net`,
  REPEAT GEN_TAC THEN SIMP_TAC[has_matrix_derivative; MLINEAR_COMPOSE_CMUL] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP MATRIX_LIM_CMUL o CONJUNCT2) THEN
  REWRITE_TAC[MATRIX_CMUL_RZERO] THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN CMATRIX_ARITH_TAC);;

let HAS_MATRIX_DERIVATIVE_CMUL_EQ = prove
 (`!f:real^N^M->real^Q^P f' net c.
       ~(c = &0)
       ==> (((\x. c %% f(x)) has_matrix_derivative (\h. c %% f'(h))) net <=>
            (f has_matrix_derivative f') net)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MATRIX_DERIVATIVE_CMUL) THENL
   [DISCH_THEN(MP_TAC o SPEC `inv(c):real`);
    DISCH_THEN(MP_TAC o SPEC `c:real`)] THEN
  ASM_SIMP_TAC[MATRIX_CMUL_ASSOC; REAL_MUL_LINV; MATRIX_CMUL_LID; ETA_AX]);;

let HAS_MATRIX_DERIVATIVE_NEG = prove
 (`!f:real^N^M->real^Q^P f' net. (f has_matrix_derivative f') net
            ==> ((\x. --(f(x))) has_matrix_derivative (\h. --(f'(h)))) net`,
  ONCE_REWRITE_TAC[MATRIX_NEG_MINUS1] THEN
  SIMP_TAC[HAS_MATRIX_DERIVATIVE_CMUL]);;

let HAS_MATRIX_DERIVATIVE_NEG_EQ = prove
 (`!f:real^N^M->real^Q^P f' net. ((\x. --(f(x))) has_matrix_derivative (\h. --(f'(h)))) net <=>
              (f has_matrix_derivative f') net`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MATRIX_DERIVATIVE_NEG) THEN
  REWRITE_TAC[MATRIX_NEG_NEG; ETA_AX]);;

let HAS_MATRIX_DERIVATIVE_ADD = prove
 (`!f:real^N^M->real^Q^P f' g g' net.
        (f has_matrix_derivative f') net /\ (g has_matrix_derivative g') net
        ==> ((\x. f(x) + g(x)) has_matrix_derivative (\h. f'(h) + g'(h))) net`,
  REPEAT GEN_TAC THEN SIMP_TAC[has_matrix_derivative; MLINEAR_COMPOSE_ADD] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (TAUT `(a /\ b) /\ (c /\ d) ==> b /\ d`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MATRIX_LIM_ADD) THEN 
  REWRITE_TAC[MATRIX_ADD_LID] THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN CMATRIX_ARITH_TAC);;
  
let HAS_MATRIX_DERIVATIVE_ADD_RCONST = prove
(`!f:real^N^M->real^Q^P f' net:(real^N^M)net c.
        (f has_matrix_derivative f') net
        ==> ((\x. f(x) + c) has_matrix_derivative f') net`,
  REPEAT GEN_TAC THEN 
  MP_TAC (ISPECL [`f:real^N^M->real^Q^P`; `f':real^N^M->real^Q^P`;
    `\A:real^N^M. c:real^Q^P`;`\A:real^N^M. mat 0: real^Q^P`;`net:(real^N^M)net`]
    HAS_MATRIX_DERIVATIVE_ADD) THEN 
    SIMP_TAC [MATRIX_ADD_RID; HAS_MATRIX_DERIVATIVE_CONST;ETA_AX]);;
    
let HAS_MATRIX_DERIVATIVE_ADD_LCONST = prove
(`!f:real^N^M->real^Q^P f' net:(real^N^M)net c.
        (f has_matrix_derivative f') net
        ==> ((\x. c + f(x)) has_matrix_derivative f') net`,
  REPEAT GEN_TAC THEN 
  MP_TAC (ISPECL [`\A:real^N^M. c:real^Q^P`;`\A:real^N^M. mat 0: real^Q^P`;`f:real^N^M->real^Q^P`; `f':real^N^M->real^Q^P`;`net:(real^N^M)net`]
    HAS_MATRIX_DERIVATIVE_ADD) THEN 
    SIMP_TAC [MATRIX_ADD_LID; HAS_MATRIX_DERIVATIVE_CONST;ETA_AX]);;
    
let HAS_MATRIX_DERIVATIVE_SUB = prove
 (`!f:real^N^M->real^Q^P f' g g' net.
        (f has_matrix_derivative f') net /\ (g has_matrix_derivative g') net
        ==> ((\x. f(x) - g(x)) has_matrix_derivative (\h. f'(h) - g'(h))) net`,
  SIMP_TAC[MATRIX_SUB; HAS_MATRIX_DERIVATIVE_ADD; HAS_MATRIX_DERIVATIVE_NEG]);;

let HAS_MATRIX_DERIVATIVE_MSUM = prove
 (`!f:real^N^M->real^Q^P net s.
     FINITE s /\
     (!a. a IN s ==> ((f a) has_matrix_derivative (f' a)) net) ==> 
 ((\x. msum s (\a. f a x)) has_matrix_derivative (\h. msum s (\a. f' a h))) net`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MSUM_CLAUSES; HAS_MATRIX_DERIVATIVE_CONST] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MATRIX_DERIVATIVE_ADD THEN
  REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[IN_INSERT]);;

let HAS_MATRIX_DERIVATIVE_MSUM_NUMSEG = prove
 (`!f:real^N^M->real^Q^P net m n.
     (!i. m <= i /\ i <= n ==> ((f i) has_matrix_derivative (f' i)) net)
     ==> ((\x. msum (m..n) (\i. f i x)) has_matrix_derivative
          (\h. msum (m..n) (\i. f' i h))) net`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MATRIX_DERIVATIVE_MSUM THEN
  ASM_REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG]);;

let HAS_MATRIX_DERIVATIVE_COMPONENTWISE_WITHIN = prove
 (`!f:real^N^M->real^Q^P f' a s.
        (f has_matrix_derivative f') (matrix_at a within s) <=>
 !i j. (1 <= i /\ i <= dimindex(:P)) /\ (1 <= j /\ j <= dimindex(:Q))
==> ((\x. lift_lift(f(x)$i$j)) has_matrix_derivative (\x. lift_lift(f'(x)$i$j)))
                (matrix_at a within s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[has_matrix_derivative_within] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [MLINEAR_COMPONENTWISE; MATRIX_LIM_COMPONENTWISE_LIFT2] THEN
  SIMP_TAC[AND_FORALL_THM; TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REWRITE_TAC[GSYM LIFT2_ADD; GSYM LIFT2_CMUL; GSYM LIFT2_SUB] THEN
  SIMP_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT; MAT_COMPONENT;
           MATRIX_SUB_COMPONENT;LIFT2_NUM; 
           MESON [] `(if i = j then &0 else &0) = &0`]);;
           
let HAS_MATRIX_DERIVATIVE_COMPONENTWISE_AT = prove
 (`!f:real^N^M->real^Q^P f' a.
        (f has_matrix_derivative f') (matrix_at a) <=>
        !i j. (1 <= i /\ i <= dimindex(:P)) /\ (1 <= j /\ j <= dimindex(:Q))
==> ((\x. lift_lift(f(x)$i$j)) has_matrix_derivative 
                             (\x. lift_lift(f'(x)$i$j))) (matrix_at a)`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  MATCH_ACCEPT_TAC HAS_MATRIX_DERIVATIVE_COMPONENTWISE_WITHIN);;
  
let HAS_MATRIX_DERIVATIVE_MMUL_COMPONENT = prove
 (`!c:real^N^M->real^Q^P c' i j v:real^S^R.
        (1 <= i /\ i <= dimindex(:P)) /\ (1 <= j /\ j <= dimindex(:Q)) /\ 
        (c has_matrix_derivative c') net
        ==> ((\x. c(x)$i$j %% v) has_matrix_derivative (\x. c'(x)$i$j %% v)) net`,
  SIMP_TAC[has_matrix_derivative; MLINEAR_MMUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM MATRIX_CMUL_ADD_RDISTRIB; GSYM MATRIX_CMUL_SUB_RDISTRIB] THEN
  SUBST1_TAC(CMATRIX_ARITH `mat 0 = &0 %% (v:real^S^R)`) THEN
  REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN MATCH_MP_TAC MATRIX_LIM_MMUL THEN
  ASM_SIMP_TAC[GSYM MATRIX_SUB_COMPONENT; GSYM MATRIX_ADD_COMPONENT] THEN
  ASM_SIMP_TAC[GSYM MATRIX_MUL_COMPONENT] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [matrixtendsto]) THEN
  REWRITE_TAC[matrixtendsto; matrix_dist; LIFT2_NUM; 
              MATRIX_SUB_RZERO; o_THM; FNORM_LIFT2] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  ASM_SIMP_TAC[MATRIX_CMUL_COMPONENT; REAL_ABS_MUL; FNORM_MUL] THEN
  ASM_MESON_TAC[REAL_LET_TRANS; COMPONENT_LE_FNORM;
                REAL_LE_LMUL; REAL_ABS_POS]);;

let HAS_MATRIX_DERIVATIVE_MMUL_DROP2 = prove
 (`!c c' v. (c has_matrix_derivative c') net ==> 
             ((\x. drop_drop(c(x)) %% v) has_matrix_derivative 
                          (\x. drop_drop(c'(x)) %% v)) net`,
  SIMP_TAC[drop_drop; LE_REFL; DIMINDEX_1; 
           HAS_MATRIX_DERIVATIVE_MMUL_COMPONENT]);;
  
let HAS_MATRIX_DERIVATIVE_LIFT2_MIP = prove
 (`!f:real^N^M->real^Q^P f'.
     (f has_matrix_derivative f') net
     ==> ((\x. lift_lift(v mip f(x))) has_matrix_derivative 
              (\t. lift_lift(v mip (f' t)))) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_matrix_derivative] THEN
  REWRITE_TAC[GSYM LIFT2_SUB; GSYM LIFT2_ADD; GSYM LIFT2_CMUL] THEN
  REWRITE_TAC[GSYM MIP_RADD; GSYM MIP_RSUB; GSYM MIP_RMUL] THEN
  SUBGOAL_THEN
   `(\t. lift_lift (v mip (f':real^N^M->real^Q^P) t)) = 
    (\y. lift_lift (v mip y)) o f'`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  SIMP_TAC[MLINEAR_COMPOSE; MLINEAR_LIFT2_MIP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MATRIX_LIM_LIFT2_MIP o CONJUNCT2) THEN
  SIMP_TAC[o_DEF; MIP_RZERO; LIFT2_NUM]);;
  
(* ------------------------------------------------------------------------- *)
(* Differentiability implies continuity.                                     *)
(* ------------------------------------------------------------------------- *)

let MATRIX_LIM_CMUL_FNORM_WITHIN = prove
 (`!f:real^N^M->real^Q^P a s. (f ->-> mat 0) (matrix_at a within s)
           ==> ((\x. fnorm(x - a) %% f(x)) ->-> mat 0) (matrix_at a within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MATRIX_LIM_WITHIN] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN 
  ASM_REWRITE_TAC[matrix_dist; MATRIX_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[FNORM_MUL; REAL_ABS_FNORM] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  ASM_SIMP_TAC[REAL_LT_MUL2; FNORM_POS_LE]);;
  
let MATRIX_DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN = prove
 (`!f:real^N^M->real^Q^P s.
        f matrix_differentiable (matrix_at x within s) ==> 
        f matrix_continuous (matrix_at x within s)`,
  REWRITE_TAC[matrix_differentiable; has_matrix_derivative_within; 
              MATRIX_CONTINUOUS_WITHIN] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^N^M->real^Q^P` MP_TAC) THEN
  STRIP_TAC THEN 
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MATRIX_LIM_CMUL_FNORM_WITHIN) THEN
  SUBGOAL_THEN
   `((f':real^N^M->real^Q^P) o (\y. y - x)) matrix_continuous
    (matrix_at x within s)`
  MP_TAC THENL
   [MATCH_MP_TAC MATRIX_CONTINUOUS_WITHIN_COMPOSE THEN
    ASM_SIMP_TAC[MLINEAR_CONTINUOUS_WITHIN] THEN
    SIMP_TAC[MATRIX_CONTINUOUS_SUB; MATRIX_CONTINUOUS_CONST; 
    MATRIX_CONTINUOUS_WITHIN_ID]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_CONTINUOUS_WITHIN; o_DEF] THEN
  ASM_REWRITE_TAC[MATRIX_CMUL_ASSOC; IMP_IMP; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MATRIX_LIM_ADD) THEN
  SIMP_TAC[MATRIX_LIM_WITHIN; GSYM MATRIX_DIST_NZ; REAL_MUL_RINV; FNORM_EQ_0;
           CMATRIX_ARITH `(x - y:real^N^M = mat 0) <=> (x = y)`;
           MATRIX_CMUL_LID; MATRIX_SUB_REFL] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP MLINEAR_0) THEN
  REWRITE_TAC[matrix_dist; MATRIX_SUB_RZERO] THEN
  REWRITE_TAC[CMATRIX_ARITH `(a + b:real^N^N - (c + a)) - (mat 0 + mat 0) = b - c`]);;
  

let MATRIX_DIFFERENTIABLE_IMP_CONTINUOUS_AT = prove
 (`!f:real^N^M->real^Q^P x:real^N^M.
        f matrix_differentiable (matrix_at x) ==> 
        f matrix_continuous (matrix_at x)`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  MESON_TAC[MATRIX_DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN]);;
  
let HAS_MATRIX_DERIVATIVE_IMP_CONTINUOUS_AT = prove
 (`!f:real^N^M->real^Q^P x:real^N^M.
        (f has_matrix_derivative f') (matrix_at x) ==> 
        f matrix_continuous (matrix_at x)`,
  MESON_TAC[matrix_differentiable;MATRIX_DIFFERENTIABLE_IMP_CONTINUOUS_AT]);;
  
let HAS_MATRIX_DERIVATIVE_WITHIN_SUBSET = prove
 (`!f:real^N^M->real^Q^P s t x. (f has_matrix_derivative f') (matrix_at x within s) /\ t SUBSET s
             ==> (f has_matrix_derivative f') (matrix_at x within t)`,
   REWRITE_TAC[has_matrix_derivative_within] THEN 
   MESON_TAC[MATRIX_LIM_WITHIN_SUBSET]);;
  
(* ------------------------------------------------------------------------- *)
(* The chain rule.                                                           *)
(* ------------------------------------------------------------------------- *)

let HAS_MATRIX_DERIVATIVE_WITHIN_ALT = prove
 (`!f:real^N^M->real^Q^P f' s x.
     (f has_matrix_derivative f') (matrix_at x within s) <=>
            mlinear f' /\
            !e. &0 < e
                ==> ?d. &0 < d /\
                        !y. y IN s /\ fnorm(y - x) < d
                            ==> fnorm(f(y) - f(x) - f'(y - x)) <=
                                e * fnorm(y - x)`,
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[has_matrix_derivative_within; MATRIX_LIM_WITHIN] THEN
  ASM_REWRITE_TAC[matrix_dist; MATRIX_SUB_RZERO] THEN
  ASM_CASES_TAC `mlinear(f':real^N^M->real^Q^P)` THEN
  ASM_REWRITE_TAC[FNORM_MUL; REAL_ABS_INV; REAL_ABS_FNORM] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
  REWRITE_TAC[CMATRIX_ARITH `a - (b + c) = a - b - c :real^N^M`] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N^M` THEN DISCH_TAC THEN
    ASM_CASES_TAC `&0 < fnorm(y - x :real^N^M)` THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [FNORM_POS_LT]) THEN
    ASM_SIMP_TAC[MATRIX_SUB_EQ; MATRIX_SUB_REFL; FNORM_0; REAL_MUL_RZERO;
                 CMATRIX_ARITH `mat 0 - x:real^N^M = --x`; FNORM_NEG] THEN
    ASM_MESON_TAC[MLINEAR_0; FNORM_0; REAL_LE_REFL];
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N^M` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `e / &2 * fnorm(y - x :real^N^M)` THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC]);;

let MATRIX_DIFF_CHAIN_WITHIN = prove
 (`!f:real^N^M->real^Q^P g:real^Q^P->real^S^R f' g' x s.
        (f has_matrix_derivative f') (matrix_at x within s) /\
        (g has_matrix_derivative g') (matrix_at (f x) within (IMAGE f s))
        ==> ((g o f) has_matrix_derivative (g' o f'))(matrix_at x within s)`,
  REPEAT GEN_TAC THEN 
  SIMP_TAC[HAS_MATRIX_DERIVATIVE_WITHIN_ALT; MLINEAR_COMPOSE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `B1:real` o MATCH_MP MLINEAR_BOUNDED_POS) THEN
  DISCH_THEN(fun th -> X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC th) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN X_CHOOSE_TAC `B2:real` (MATCH_MP
              MLINEAR_BOUNDED_POS th)) MP_TAC) THEN
  FIRST_X_ASSUM(fun th -> MP_TAC th THEN MP_TAC(SPEC `e / &2 / B2` th)) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2 / (&1 + B1)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; REAL_LT_ADD] THEN
  DISCH_THEN(X_CHOOSE_THEN `de:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_ADD; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d0:real`; `de / (B1 + &1)`] REAL_DOWN2) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_ADD; REAL_LT_01] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N^M` THEN
  DISCH_TAC THEN UNDISCH_TAC
   `!y. y IN s /\ fnorm(y - x) < d2
  ==> fnorm ((f:real^N^M->real^Q^P) y - f x - f'(y - x)) <= fnorm(y - x)` THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N^M`) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_LT_TRANS]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N^M`) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_LT_TRANS]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^N^M->real^Q^P) y`) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[IN_IMAGE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
     `fnorm(f'(y - x)) + fnorm((f:real^N^M->real^Q^P) y - f x - f'(y - x))` THEN
    REWRITE_TAC[FNORM_TRIANGLE_SUB] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `B1 * fnorm(y - x) + fnorm(y - x :real^N^M)` THEN
    ASM_SIMP_TAC[REAL_LE_ADD2] THEN
    REWRITE_TAC[REAL_ARITH `a * x + x = x * (a + &1)`] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_ADD; REAL_LT_01] THEN
    ASM_MESON_TAC[REAL_LT_TRANS];
    DISCH_TAC] THEN
  REWRITE_TAC[o_THM] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `fnorm((g:real^Q^P->real^S^R)(f(y:real^N^M)) - g(f x) - g'(f y - f x)) +
              fnorm((g(f y) - g(f x) - g'(f'(y - x))) -
                   (g(f y) - g(f x) - g'(f y - f x)))` THEN
  REWRITE_TAC[FNORM_TRIANGLE_SUB] THEN
  REWRITE_TAC[CMATRIX_ARITH `(a - b - c1) - (a - b - c2) = c2 - c1:real^N^M`] THEN
  ASM_SIMP_TAC[GSYM MLINEAR_SUB] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
    `a <= d ==> b <= ee - d ==> a + b <= ee`)) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `B2 * fnorm((f:real^N^M->real^Q^P) y - f x - f'(y - x))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `B2 * e / &2 / B2 * fnorm(y - x :real^N^M)` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE] THEN REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `b * ((e * h) * b') * x <= e * x - d <=>
    d <= e * (&1 - h * b' * b) * x`] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_ADD; REAL_LT_01] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `fnorm(f'(y - x)) + fnorm((f:real^N^M->real^Q^P) y - f x - f'(y - x))` THEN
  REWRITE_TAC[FNORM_TRIANGLE_SUB] THEN MATCH_MP_TAC(REAL_ARITH
   `u <= x * b /\ v <= b ==> u + v <= b * (&1 + x)`) THEN
  ASM_REWRITE_TAC[]);;
  
let MATRIX_DIFF_CHAIN_AT = prove
 (`!f:real^N^M->real^Q^P g:real^Q^P->real^S^R f' g' x.
        (f has_matrix_derivative f') (matrix_at x) /\
        (g has_matrix_derivative g') (matrix_at (f x))
        ==> ((g o f) has_matrix_derivative (g' o f')) (matrix_at x)`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  ASM_MESON_TAC[MATRIX_DIFF_CHAIN_WITHIN; MATRIX_LIM_WITHIN_SUBSET; SUBSET_UNIV;
                HAS_MATRIX_DERIVATIVE_WITHIN_SUBSET]);;
                
let HAS_MATRIX_DERIVATIVE_CHAIN = prove
 (`!P f:real^N^M->real^Q^P g.
        (!x. P x ==> (g has_matrix_derivative g') (matrix_at x))
        ==> (!x s. (f has_matrix_derivative f') (matrix_at x within s) /\ P(f x)
                   ==> ((g o f) has_matrix_derivative (g' o f'))
                       (matrix_at x within s)) /\
            (!x. (f has_matrix_derivative f') (matrix_at x) /\ P(f x)
                 ==> ((g o f) has_matrix_derivative (g' o f'))
                     (matrix_at x))`,
  MESON_TAC [MATRIX_DIFF_CHAIN_WITHIN;MATRIX_DIFF_CHAIN_AT;
             HAS_MATRIX_DERIVATIVE_AT_WITHIN]);;
             
let HAS_MATRIX_DERIVATIVE_CHAIN_UNIV = prove
 (`!f:real^N^M->real^Q^P g:real^Q^P->real^S^R f' g' x. 
        (!x. (g has_matrix_derivative g') (matrix_at x))
         ==> (!x s. (f has_matrix_derivative f') (matrix_at x within s)
                    ==> ((g o f) has_matrix_derivative (g' o f'))
                        (matrix_at x within s)) /\
             (!x. (f has_matrix_derivative f') (matrix_at x)
                  ==> ((g o f) has_matrix_derivative(g' o f'))
                      (matrix_at x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(SIMP_RULE [] (ISPECL [`\x:real^Q^P. T`; `f:real^N^M->real^Q^P`; `g:real^Q^P->real^S^R`] HAS_MATRIX_DERIVATIVE_CHAIN)) THEN ASM_SIMP_TAC[]);;
  
let HAS_MATRIX_DERIVATIVE_BILINEAR_WITHIN = prove
 (`!h:real^N^M->real^Q^P->real^S^R f g f' g' x:real^O^T s.
        (f has_matrix_derivative f') (matrix_at x within s) /\
        (g has_matrix_derivative g') (matrix_at x within s) /\
        bimlinear h
        ==> ((\x. h (f x) (g x)) has_matrix_derivative
             (\d. h (f x) (g' d) + h (f' d) (g x))) (matrix_at x within s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_TAC "contg" `((g:real^O^T->real^Q^P) ->-> g(x)) (matrix_at x within s)`
   [REWRITE_TAC[GSYM MATRIX_CONTINUOUS_WITHIN] THEN
    ASM_MESON_TAC[matrix_differentiable; MATRIX_DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN]] THEN
  UNDISCH_TAC `((f:real^O^T->real^N^M) has_matrix_derivative f') (matrix_at x within s)` THEN
  REWRITE_TAC[has_matrix_derivative_within] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "df")) THEN
  SUBGOAL_TAC "contf"
   `((\y. (f:real^O^T->real^N^M)(x) + f'(y - x)) ->-> f(x)) (matrix_at x within s)`
   [GEN_REWRITE_TAC LAND_CONV [GSYM MATRIX_ADD_RID] THEN
    MATCH_MP_TAC MATRIX_LIM_ADD THEN REWRITE_TAC[MATRIX_LIM_CONST] THEN
    SUBGOAL_THEN `mat 0 = (f':real^O^T->real^N^M)(x - x)` SUBST1_TAC THENL
     [ASM_MESON_TAC[MLINEAR_0; MATRIX_SUB_REFL]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_LIM_LINEAR; MATRIX_LIM_SUB; MATRIX_LIM_CONST; MATRIX_LIM_WITHIN_ID]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_matrix_derivative_within]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dg")) THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [bimlinear]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[mlinear]) THEN ASM_REWRITE_TAC[mlinear] THEN
    REPEAT STRIP_TAC THEN CMATRIX_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`matrix_at (x:real^O^T) within s`; `h:real^N^M->real^Q^P->real^S^R`]
         MATRIX_LIM_BILINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "contg" MP_TAC THEN REMOVE_THEN "df" MP_TAC THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  REMOVE_THEN "dg" MP_TAC THEN REMOVE_THEN "contf" MP_TAC THEN
  ONCE_REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP MATRIX_LIM_ADD) THEN
  SUBGOAL_THEN
   `((\y:real^O^T. inv(fnorm(y - x)) %%
                 (h:real^N^M->real^Q^P->real^S^R) (f'(y - x)) (g'(y - x)))
    ->-> mat 0) (matrix_at x within s)`
  MP_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o MATCH_MP
                BIMLINEAR_BOUNDED_POS) THEN
    X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC
     (MATCH_MP MLINEAR_BOUNDED_POS (ASSUME `mlinear (f':real^O^T->real^N^M)`)) THEN
    X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC
     (MATCH_MP MLINEAR_BOUNDED_POS (ASSUME `mlinear (g':real^O^T->real^Q^P)`)) THEN
    REWRITE_TAC[MATRIX_LIM_WITHIN; matrix_dist; MATRIX_SUB_RZERO] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN EXISTS_TAC `e / ((B * C * D):real)` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; FNORM_MUL; REAL_LT_MUL] THEN
    X_GEN_TAC `x':real^O^T` THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_FNORM; REAL_ABS_INV] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `inv(fnorm(x' - x :real^O^T)) *
                B * (C * fnorm(x' - x)) * (D * fnorm(x' - x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_LE_INV_EQ; FNORM_POS_LE] THEN
      ASM_MESON_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE; REAL_LE_MUL2; FNORM_POS_LE;
                    REAL_LE_TRANS];
      ONCE_REWRITE_TAC[REAL_ARITH 
      `!i b c d x:real.i * b * (c * x) * (d * x) = (i * x) * x * (b * c * d)`] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_MUL]];
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP MATRIX_LIM_ADD) THEN
    REWRITE_TAC (map (C MATCH_MP (ASSUME `bimlinear(h:real^N^M->real^Q^P->real^S^R)`))
     [BIMLINEAR_RZERO; BIMLINEAR_LZERO; BIMLINEAR_LADD; BIMLINEAR_RADD;
      BIMLINEAR_LCMUL; BIMLINEAR_RCMUL; BIMLINEAR_LSUB; BIMLINEAR_RSUB]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
    BINOP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN CMATRIX_ARITH_TAC THEN
    REWRITE_TAC[MATRIX_ADD_LID]]);;
    
let HAS_MATRIX_DERIVATIVE_BILINEAR_AT = prove
 (`!h:real^N^M->real^Q^P->real^S^R  f g f' g' x:real^O^T.
        (f has_matrix_derivative f') (matrix_at x) /\
        (g has_matrix_derivative g') (matrix_at x) /\
        bimlinear h
        ==> ((\x. h (f x) (g x)) has_matrix_derivative
             (\d. h (f x) (g' d) + h (f' d) (g x))) (matrix_at x)`,
  REWRITE_TAC[has_matrix_derivative_at] THEN
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  REWRITE_TAC[GSYM has_matrix_derivative_within; HAS_MATRIX_DERIVATIVE_BILINEAR_WITHIN]);;
  
let HAS_MATRIX_DERIVATIVE_MUL_WITHIN = prove
 (`!f:real^N^M->real^Q^P g:real^N^M->real^S^Q f' g' x:real^N^M s.
    (f has_matrix_derivative f') (matrix_at x within s) /\ 
    (g has_matrix_derivative g') (matrix_at x within s) 
        ==> ((\t:real^N^M. (f(t) ** g(t))) has_matrix_derivative 
            (\h:real^N^M. f(x) ** g'(h) + f'(h) ** g(x))) (matrix_at x within s)`,
  REPEAT GEN_TAC THEN 
  MATCH_MP_TAC (REWRITE_RULE [TAUT `a /\ b /\ c ==> d <=> c ==> (a /\ b) ==> d`] HAS_MATRIX_DERIVATIVE_BILINEAR_WITHIN) THEN
  SIMP_TAC[BIMLINEAR_MUL]);;

  
let HAS_MATRIX_DERIVATIVE_MUL_AT = prove
 (`!f:real^N^M->real^Q^P g:real^N^M->real^S^Q f' g' x:real^N^M.
    (f has_matrix_derivative f') (matrix_at x) /\ 
    (g has_matrix_derivative g') (matrix_at x) 
        ==> ((\t:real^N^M. (f(t) ** g(t))) has_matrix_derivative 
            (\h:real^N^M. f(x) ** g'(h) + f'(h) ** g(x))) (matrix_at x)`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN REWRITE_TAC[HAS_MATRIX_DERIVATIVE_MUL_WITHIN]);;
  
(* ------------------------------------------------------------------------- *)
(* Component of the differential must be zero if it exists at a local        *)
(* maximum or minimum for that corresponding component. Start with slightly  *)
(* sharper forms that fix the sign of the derivative on the boundary.        *)
(* ------------------------------------------------------------------------- *)
 
let MATRIX_DIFFERENTIAL_COMPONENT_POS_AT_MINIMUM = prove
 (`!f:real^N^M->real^Q^P f' x s i j e.
        (1 <= i /\ i <= dimindex(:P)) /\ (1 <= j /\ j <= dimindex(:Q)) /\
        x IN s /\ matrix_convex s /\ 
        (f has_matrix_derivative f') (matrix_at x within s) /\
    &0 < e /\ (!w. w IN s INTER matrix_ball(x,e) ==> (f x)$i$j <= (f w)$i$j)
        ==> !y. y IN s ==> &0 <= (f'(y - x))$i$j`,
  REWRITE_TAC[has_matrix_derivative_within] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `y:real^N^M = x` THENL
   [ASM_MESON_TAC[MATRIX_SUB_REFL; MLINEAR_0; MAT_0_COMPONENT; REAL_LE_REFL];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATRIX_LIM_WITHIN]) THEN
  DISCH_THEN(MP_TAC o SPEC
    `--((f':real^N^M->real^Q^P)(y - x)$i$j) / fnorm(y - x)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; FNORM_POS_LT; MATRIX_SUB_EQ;
               NOT_EXISTS_THM; REAL_ARITH `&0 < --x <=> x < &0`] THEN
  X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ABBREV_TAC `de = min (&1) ((min d e) / &2 / fnorm(y - x:real^N^M))` THEN
  DISCH_THEN(MP_TAC o SPEC `x + de %% (y - x):real^N^M`) THEN
  REWRITE_TAC[matrix_dist; MATRIX_ADD_SUB; NOT_IMP; GSYM CONJ_ASSOC] THEN
  SUBGOAL_THEN `fnorm(de %% (y - x):real^N^M) < min d e` MP_TAC THENL
   [ASM_SIMP_TAC[FNORM_MUL; GSYM REAL_LT_RDIV_EQ;
                 FNORM_POS_LT; MATRIX_SUB_EQ] THEN
    EXPAND_TAC "de" THEN MATCH_MP_TAC(REAL_ARITH
     `&0 < de / x ==> abs(min (&1) (de / &2 / x)) < de / x`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MIN; FNORM_POS_LT; MATRIX_SUB_EQ];
    REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < de /\ de <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "de" THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_01; REAL_HALF; REAL_LT_DIV;
                 FNORM_POS_LT; MATRIX_SUB_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[CMATRIX_ARITH
     `x + a %% (y - x):real^Q^P = (&1 - a) %% x + a %% y`] THEN
    MATCH_MP_TAC IN_MATRIX_CONVEX_SET THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[FNORM_MUL] THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_ARITH `&0 < x ==> &0 < abs x`;
               FNORM_POS_LT; MATRIX_SUB_EQ; MATRIX_SUB_RZERO] THEN
  MATCH_MP_TAC(MESON [REAL_NOT_LT; COMPONENT_LE_FNORM; REAL_LE_TRANS]
   `abs(y$i$j) <= fnorm(y) /\ ~(abs(y$i$j) < e) ==> ~(fnorm y < e)`) THEN
  ASM_SIMP_TAC[COMPONENT_LE_FNORM] THEN REWRITE_TAC[MATRIX_CMUL_COMPONENT] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_MUL; REAL_ABS_FNORM; REAL_ABS_ABS] THEN
  REWRITE_TAC[REAL_NOT_LT; REAL_INV_MUL; REAL_ARITH
   `d <= (a * inv b) * c <=> d <= (c * a) / b`] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; FNORM_POS_LT; MATRIX_SUB_EQ] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; MATRIX_SUB_COMPONENT;
    MATRIX_ADD_COMPONENT; REAL_ARITH `&0 < x ==> &0 < abs x`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `fx <= fy /\ a = --b /\ b < &0 ==> a <= abs(fy - (fx + b))`) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MLINEAR_CMUL th]) THEN
  ASM_SIMP_TAC[real_abs; MATRIX_CMUL_COMPONENT; REAL_LT_IMP_LE] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ] THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; ASM_REAL_ARITH_TAC] THEN
  ASM_REWRITE_TAC[IN_INTER; IN_MATRIX_BALL; 
  MESON [matrix_dist; CMATRIX_ARITH `x - (x + e) = --e:real^N^M`; FNORM_NEG]
        `matrix_dist(x:real^N^M,x + e) = fnorm e`]);;
 
let MATRIX_DIFFERENTIAL_COMPONENT_NEG_AT_MAXIMUM = prove
 (`!f:real^N^M->real^Q^P f' x s i j e.
        (1 <= i /\ i <= dimindex(:P)) /\ (1 <= j /\ j <= dimindex(:Q)) /\
        x IN s /\ matrix_convex s /\ 
        (f has_matrix_derivative f') (matrix_at x within s) /\
    &0 < e /\ (!w. w IN s INTER matrix_ball(x,e) ==> (f w)$i$j <= (f x)$i$j)
        ==> !y. y IN s ==> (f'(y - x))$i$j <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. --((f:real^N^M->real^Q^P) x)`;  `\x. --((f':real^N^M->real^Q^P) x)`;
    `x:real^N^M`; `s:real^N^M->bool`; `i:num`; `j:num`; `e:real`]
        MATRIX_DIFFERENTIAL_COMPONENT_POS_AT_MINIMUM) THEN
  ASM_SIMP_TAC[HAS_MATRIX_DERIVATIVE_NEG] THEN
  ASM_SIMP_TAC[REAL_LE_NEG2; MATRIX_NEG_COMPONENT; REAL_NEG_GE0]);;
 
let MATRIX_DIFFERENTIAL_COMPONENT_ZERO_AT_MAXMIN = prove
 (`!f:real^N^M->real^Q^P f' x s i j.
        (1 <= i /\ i <= dimindex(:P)) /\ (1 <= j /\ j <= dimindex(:Q)) /\
  x IN s /\ matrix_open s /\ (f has_matrix_derivative f') (matrix_at x) /\
        ((!w. w IN s ==> (f w)$i$j <= (f x)$i$j) \/
         (!w. w IN s ==> (f x)$i$j <= (f w)$i$j))
        ==> !h. (f' h)$i$j = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATRIX_OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N^M`) THEN ASM_REWRITE_TAC[SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [MP_TAC(ISPECL [`f:real^N^M->real^Q^P`; `f':real^N^M->real^Q^P`;
                   `x:real^N^M`; `matrix_cball(x:real^N^M,e)`; 
                   `i:num`; `j:num`; `e:real`]
        MATRIX_DIFFERENTIAL_COMPONENT_NEG_AT_MAXIMUM);
    MP_TAC(ISPECL [`f:real^N^M->real^Q^P`; `f':real^N^M->real^Q^P`;
                   `x:real^N^M`; `matrix_cball(x:real^N^M,e)`; 
                   `i:num`; `j:num`; `e:real`]
        MATRIX_DIFFERENTIAL_COMPONENT_POS_AT_MINIMUM)] THEN
  ASM_SIMP_TAC[HAS_MATRIX_DERIVATIVE_AT_WITHIN; CENTRE_IN_MATRIX_CBALL;
               MATRIX_CONVEX_CBALL; REAL_LT_IMP_LE; IN_INTER] THEN
  DISCH_THEN(LABEL_TAC "ass") THEN X_GEN_TAC `h:real^N^M` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I 
                [has_matrix_derivative_at]) THEN
  (ASM_CASES_TAC `h:real^N^M = mat 0` THENL
    [ASM_MESON_TAC[MLINEAR_0; MAT_0_COMPONENT]; ALL_TAC]) THEN
  REMOVE_THEN "ass" (fun th ->
    MP_TAC(SPEC `x + e / fnorm h %% h:real^N^M` th) THEN
    MP_TAC(SPEC `x - e / fnorm h %% h:real^N^M` th)) THEN
  SIMP_TAC[IN_MATRIX_CBALL; MESON [matrix_dist; MATRIX_SUB; MATRIX_NEG_NEG;
    CMATRIX_ARITH `x + --(x + e) = --e:real^Q^P`; FNORM_NEG]
    `matrix_dist(x:real^Q^P,x - e) = fnorm e /\ 
     matrix_dist(x:real^Q^P,x + e) = fnorm e`] THEN
  REWRITE_TAC[FNORM_MUL; REAL_ABS_DIV; REAL_ABS_FNORM] THEN
  ASM_SIMP_TAC[real_abs; REAL_DIV_RMUL; FNORM_EQ_0; REAL_LT_IMP_LE;
               REAL_LE_REFL] THEN
  REWRITE_TAC[CMATRIX_ARITH `x - e - x:real^Q^P = --e /\ (x + e) - x = e`] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MLINEAR_NEG th]) THEN
  REWRITE_TAC[IMP_IMP; REAL_ARITH `&0 <= --x /\ &0 <= x <=> x = &0`;
    MATRIX_NEG_COMPONENT; REAL_ARITH `--x <= &0 /\ x <= &0 <=> x = &0`] THEN
  DISCH_THEN(MP_TAC o AP_TERM `( * ) (fnorm(h:real^N^M) / e)`) THEN
  REWRITE_TAC[GSYM MATRIX_CMUL_COMPONENT] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MLINEAR_CMUL th)]) THEN
  REWRITE_TAC[REAL_MUL_RZERO; MATRIX_CMUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(x = &0) /\ ~(y = &0) ==> x / y * y / x = &1`;
               FNORM_EQ_0; REAL_LT_IMP_NZ; MATRIX_CMUL_LID]);;
 
let MATRIX_DIFFERENTIAL_ZERO_MAXMIN = prove
 (`!f:real^N^M->real^1^1 f' x s.
        x IN s /\ matrix_open s /\ (f has_matrix_derivative f') (matrix_at x) /\
        ((!y. y IN s ==> drop_drop(f y) <= drop_drop(f x)) \/
         (!y. y IN s ==> drop_drop(f x) <= drop_drop(f y)))
        ==> (f' = \v. mat 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N^M->real^1^1`; `f':real^N^M->real^1^1`;
                 `x:real^N^M`; `s:real^N^M->bool`; `1:num`; `1:num`]
        MATRIX_DIFFERENTIAL_COMPONENT_ZERO_AT_MAXMIN) THEN
  ASM_REWRITE_TAC[GSYM drop_drop; DIMINDEX_1; LE_REFL] THEN
  REWRITE_TAC[GSYM LIFT2_EQ; LIFT2_NUM; FUN_EQ_THM; LIFT2_DROP]);;
 
(* ------------------------------------------------------------------------- *)
(* lift The traditional Rolle theorem in one dimension to matrix space       *)
(* ------------------------------------------------------------------------- *)

let MATRIX_ROLLE = prove
 (`!f:real^1^1->real^1^1 f' a b.
        drop_drop a < drop_drop b /\ (f a = f b) /\
        f matrix_continuous_on matrix_interval[a,b] /\
        (!x. x IN matrix_interval(a,b) ==> 
             (f has_matrix_derivative f'(x)) (matrix_at x))
        ==> ?x. x IN matrix_interval(a,b) /\ (f'(x) = \v. mat 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1^1->real^1^1`; `a:real^1^1`; `b:real^1^1`]
        MATRIX_CONTINUOUS_IVT_LOCAL_EXTREMUM) THEN
  ASM_SIMP_TAC[MATRIX_SEGMENT_1; REAL_LT_IMP_LE] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_REFL]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `c:real^1^1` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MATRIX_DIFFERENTIAL_ZERO_MAXMIN THEN MAP_EVERY EXISTS_TAC
   [`f:real^1^1->real^1^1`; `c:real^1^1`; 
    `matrix_interval(a:real^1^1,b)`] THEN
  ASM_MESON_TAC[MATRIX_INTERVAL_OPEN_SUBSET_CLOSED; SUBSET; 
                MATRIX_OPEN_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* One-dimensional mean value theorem. (matrix space)                        *)
(* ------------------------------------------------------------------------- *)
 
let MATRIX_MVT = prove
 (`!f:real^1^1->real^1^1 f' a b.
        drop_drop a < drop_drop b /\
        f matrix_continuous_on matrix_interval[a,b] /\
        (!x. x IN matrix_interval(a,b) ==> 
             (f has_matrix_derivative f'(x)) (matrix_at x))
        ==> ?x. x IN matrix_interval(a,b) /\ (f(b) - f(a) = f'(x) (b - a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x. f(x) - (drop_drop(f b - f a) / drop_drop(b - a)) %% x`;
                `\k:real^1^1 x:real^1^1.
                    f'(k)(x) - (drop_drop(f b - f a) / drop_drop(b - a)) %% x`;
                `a:real^1^1`; `b:real^1^1`]
               MATRIX_ROLLE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[MATRIX_CONTINUOUS_ON_SUB; MATRIX_CONTINUOUS_ON_CMUL; 
                 MATRIX_CONTINUOUS_ON_ID] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CMATRIX_ARITH
       `(fa - k %% a = fb - k %% b:real^N^M) <=> (fb - fa = k %% (b - a))`];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MATRIX_DERIVATIVE_SUB THEN
      ASM_SIMP_TAC[HAS_MATRIX_DERIVATIVE_CMUL; 
                   HAS_MATRIX_DERIVATIVE_ID; ETA_AX]];
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `x:real^1^1` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `b - a:real^1^1`))] THEN
  SIMP_TAC[MATRIX_SUB_EQ; GSYM DROP2_EQ; DROP2_SUB; DROP2_CMUL] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_SUB_LT; REAL_LT_IMP_NZ]);;
 
(* ------------------------------------------------------------------------- *)
(* A generalization of MVT in matrix_space                                   *)
(* ------------------------------------------------------------------------- *)

let MATRIX_MVT_GENERAL = prove
 (`!f:real^1^1->real^N^M f' a b.
        drop_drop a < drop_drop b /\
        f matrix_continuous_on matrix_interval[a,b] /\
        (!x. x IN matrix_interval(a,b) ==> 
             (f has_matrix_derivative f'(x)) (matrix_at x))
        ==> ?x. x IN matrix_interval(a,b) /\
                fnorm(f(b) - f(a)) <= fnorm(f'(x) (b - a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`(lift_lift o (\y. (f(b) - f(a)) mip y)) o (f:real^1^1->real^N^M)`;
                `\x t. lift_lift((f(b:real^1^1) - f(a)) mip
                      ((f':real^1^1->real^1^1->real^N^M) x t))`;
                `a:real^1^1`; `b:real^1^1`]  MATRIX_MVT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MATRIX_CONTINUOUS_ON_LIFT2_MIP; 
                 MATRIX_CONTINUOUS_ON_COMPOSE] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC HAS_MATRIX_DERIVATIVE_LIFT2_MIP THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^1^1` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[o_THM; GSYM LIFT2_SUB; GSYM MIP_RSUB; LIFT2_EQ] THEN
  DISCH_TAC THEN ASM_CASES_TAC `(f:real^1^1->real^N^M) b = f a` THENL
   [ASM_REWRITE_TAC[MATRIX_SUB_REFL; FNORM_0; FNORM_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
  EXISTS_TAC `fnorm((f:real^1^1->real^N^M) b - f a)` THEN
  ASM_REWRITE_TAC[FNORM_POS_LT; MATRIX_SUB_EQ; GSYM REAL_POW_2] THEN
  ASM_REWRITE_TAC[FNORM_POW_2; GSYM mip] THEN 
  REWRITE_TAC [REWRITE_RULE [GSYM mip] FNORM_CAUCHY_SCHWARZ]);;
  
(* ------------------------------------------------------------------------- *)
(* general bound theorem.                                                    *)
(* ------------------------------------------------------------------------- *)

let MATRIX_DIFFERENTIABLE_BOUND = prove
 (`!f:real^N^M->real^Q^P f' s B.
        matrix_convex s /\
        (!x. x IN s ==> 
        (f has_matrix_derivative f'(x)) (matrix_at x within s)) /\
        (!x. x IN s ==> monorm(f'(x)) <= B)
        ==> !x y. x IN s /\ y IN s ==> fnorm(f(x) - f(y)) <= B * fnorm(x - y)`,
  ONCE_REWRITE_TAC[FNORM_SUB_SYM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!x y. x IN s ==> 
     fnorm((f':real^N^M->real^N^M->real^Q^P)(x) y) <= B * fnorm(y)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MONORM; has_matrix_derivative; REAL_LE_TRANS; FNORM_POS_LE;
                  REAL_LE_RMUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN matrix_interval[mat 0:real^1^1,mat 1] ==> 
        (x + drop_drop u %% (y - x) :real^N^M) IN s`
  ASSUME_TAC THENL
   [SIMP_TAC[IN_MATRIX_INTERVAL; FORALL_DIMINDEX_1; drop_drop] THEN
    SIMP_TAC[MAT_COMPONENT; LE_REFL; LE_ANTISYM; DIMINDEX_1;
             EQ_SYM_EQ] THEN
    REWRITE_TAC[CMATRIX_ARITH `x + u %% (y - x):real^N^M = (&1 - u) %% x + u %% y`] THEN
    ASM_MESON_TAC[MATRIX_CONVEX_ALT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN matrix_interval(mat 0:real^1^1, mat 1) ==> 
        (x + drop_drop u %% (y - x) :real^N^M) IN s`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; MATRIX_INTERVAL_OPEN_SUBSET_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(f:real^N^M->real^Q^P) o (\u. x + drop_drop u %% (y - x))`;
    `\u. (f':real^N^M->real^N^M->real^Q^P) (x + drop_drop u %% (y - x)) o
         (\u. mat 0 + drop_drop u %% (y - x))`;
    `mat 0:real^1^1`; `mat 1:real^1^1`] MATRIX_MVT_GENERAL) THEN
  REWRITE_TAC[o_THM; DROP2_MAT; CMATRIX_ARITH `x:real^N^M + &1 %% (y - x) = y`;
              MATRIX_CMUL_LZERO; MATRIX_SUB_RZERO; MATRIX_ADD_RID] THEN
  REWRITE_TAC[MATRIX_CMUL_LID] THEN ANTS_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[MATRIX_ADD_LID; REAL_LE_TRANS]] THEN
  REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MATRIX_CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[MATRIX_CONTINUOUS_ON_ADD; MATRIX_CONTINUOUS_ON_CONST; 
             MATRIX_CONTINUOUS_ON_MMUL;
             o_DEF; LIFT2_DROP; MATRIX_CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC MATRIX_CONTINUOUS_ON_SUBSET THEN 
    EXISTS_TAC `s:real^N^M->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[MATRIX_DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN; 
                  matrix_differentiable;
                  MATRIX_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN];
    ALL_TAC] THEN
  X_GEN_TAC `a:real^1^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `a IN matrix_interval(mat 0:real^1^1,mat 1) /\
                matrix_open(matrix_interval(mat 0:real^1^1,mat 1))`
  MP_TAC THENL [ASM_MESON_TAC[MATRIX_OPEN_INTERVAL]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP
    HAS_MATRIX_DERIVATIVE_WITHIN_OPEN th)]) THEN
  MATCH_MP_TAC MATRIX_DIFF_CHAIN_WITHIN THEN
  ASM_SIMP_TAC[HAS_MATRIX_DERIVATIVE_ADD; HAS_MATRIX_DERIVATIVE_CONST;
               HAS_MATRIX_DERIVATIVE_MMUL_DROP2; HAS_MATRIX_DERIVATIVE_ID] THEN
  MATCH_MP_TAC HAS_MATRIX_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `s:real^N^M->bool` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  ASM_MESON_TAC[MATRIX_INTERVAL_OPEN_SUBSET_CLOSED; SUBSET]);; 
  
(* ------------------------------------------------------------------------- *)
(* derivative of constant function                                           *)
(* ------------------------------------------------------------------------- *)

let HAS_MATRIX_DERIVATIVE_ZERO_CONSTANT = prove
 (`!f:real^N^M->real^Q^P s.
        matrix_convex s /\
        (!x. x IN s ==> 
             (f has_matrix_derivative (\h. mat 0)) (matrix_at x within s))
        ==> ?c. !x. x IN s ==> f(x) = c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N^M->real^Q^P`; 
                 `(\x h. mat 0):real^N^M->real^N^M->real^Q^P`;
                 `s:real^N^M->bool`; `&0`] MATRIX_DIFFERENTIABLE_BOUND) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; MONORM_CONST; FNORM_0; REAL_LE_REFL] THEN
  SIMP_TAC[FNORM_LE_0; MATRIX_SUB_EQ] THEN MESON_TAC[]);;
  
let HAS_MATRIX_DERIVATIVE_ZERO_UNIQUE = prove
 (`!f s a c. matrix_convex s /\ a IN s /\ f a = c /\
        (!x. x IN s ==> 
             (f has_matrix_derivative (\h. mat 0)) (matrix_at x within s))
             ==> !x. x IN s ==> f x = c`,
  MESON_TAC[HAS_MATRIX_DERIVATIVE_ZERO_CONSTANT]);;
 
(* ------------------------------------------------------------------------- *)
(* some transcendental matrix functions generated by matrix series           *)
(* ------------------------------------------------------------------------- *)

make_overloadable "matrix_exp" `:A->A`;;

overload_interface ("matrix_exp", `rmatrix_exp:real^N^N->real^N^N`);;

overload_interface ("matrix_exp", `cmatrix_exp:complex^N^N->complex^N^N`);;

let rmatrix_exp = new_definition
    `!A:real^N^N. rmatrix_exp A = 
                infmsum (from 0) (\n. (&1 / &(FACT n)) %% (A matrix_pow n))`;;
                
let cmatrix_exp = new_definition
    `!A:complex^N^N. cmatrix_exp A = 
                infmsum (from 0) (\n. Cx(&1 / &(FACT n)) %%% (A matrix_pow n))`;;
                
let matrix_exp = prove
    (`(!A:real^N^N. rmatrix_exp A = 
                infmsum (from 0) (\n. (&1 / &(FACT n)) %% (A matrix_pow n))) /\
    (!A:complex^N^N. cmatrix_exp A = 
                infmsum (from 0) (\n. Cx(&1 / &(FACT n)) %%% (A matrix_pow n)))`,
    SIMP_TAC[rmatrix_exp;cmatrix_exp]);;

let MATRIX_EXP_0 = prove
 (`matrix_exp(mat 0:real^N^N) = mat 1`,
  REWRITE_TAC[matrix_exp] THEN MATCH_MP_TAC INFMSUM_UNIQUE THEN
  MP_TAC(ISPECL [`\i. ( &1 / &(FACT i)) %% ((mat 0:real^N^N) matrix_pow i)`;
                 `{0}`; `from 0`] MSERIES_FINITE_SUPPORT) THEN
  SIMP_TAC[FROM_0; INTER_UNIV; FINITE_INSERT; FINITE_RULES] THEN ANTS_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[IN_SING; NOT_SUC] THEN
    REWRITE_TAC[MATRIX_POW_0;MATRIX_CMUL_RZERO];
    REWRITE_TAC[MSUM_SING; FACT; REAL_DIV_1; MATRIX_CMUL_LID; matrix_pow]]);;
    
let MATRIX_EXP_CONVERGES = prove
 (`!A:real^N^N. ((\n. (&1 / &(FACT n)) %% (A matrix_pow n)) 
          msums matrix_exp(A)) (from 0)`,
  let lem = MESON [REAL_ABS_REFL] `!x. &0 <= x ==> abs x = x` in
  GEN_TAC THEN REWRITE_TAC[matrix_exp; MSUMS_INFSUM; msummable] THEN
  MATCH_MP_TAC MSERIES_RATIO THEN SIMP_TAC [GE;FNORM_MUL] THEN
  SIMP_TAC [FACT; matrix_pow;real_div;REAL_MUL_LID] THEN 
  EXISTS_TAC `fnorm(A:real^N^N) * inv (fnorm(A) + &1)` THEN 
  EXISTS_TAC `num_of_real (fnorm(A:real^N^N)) + 1` THEN
  SIMP_TAC [GSYM real_div] THEN 
  SIMP_TAC [FNORM_POS_LE; REAL_ARITH `&0 <= a ==> &0 < a + &1`;
            REAL_LT_LDIV_EQ] THEN CONJ_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN GEN_TAC THEN
  SIMP_TAC [GSYM REAL_OF_NUM_LE; NUM_OF_REAL_ADD] THEN 
  SIMP_TAC [GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUC] THEN 
  SIMP_TAC [FNORM_POS_LE; lem; REAL_LE_INV;LE_0;
            REAL_OF_NUM_LE; REAL_LE_ADD; REAL_ABS_MUL;REAL_INV_MUL;
            GSYM REAL_MUL_ASSOC] THEN 
  STRIP_TAC THEN 
  ONCE_REWRITE_TAC [REAL_ARITH `!c:real. a * b * c = b * a * c`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
  [SIMP_TAC [REAL_LT_INV; REAL_OF_NUM_LT; REAL_LE_LT; FACT_LT];ALL_TAC]
  THEN SIMP_TAC [real_div; GSYM REAL_MUL_ASSOC] THEN 
  ONCE_REWRITE_TAC [REAL_ARITH `!c:real. a * b * c = b * a * c`] THEN 
  MATCH_MP_TAC REAL_LE_MUL2 THEN 
  SIMP_TAC [FNORM_SUBMULT; REAL_LE_ADD; REAL_OF_NUM_LE;
            FNORM_POS_LE;REAL_LE_INV; LE_0] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN 
  SIMP_TAC [FNORM_POS_LE; REAL_ARITH `&0 <= a ==> &0 < a + &1`] THEN
  MP_TAC (CONJUNCT2 (SPEC `fnorm (A:real^N^N)` FLOOR)) THEN
  ASM_ARITH_TAC);;
  
let MATRIX_EXP_CONVERGES_UNIQUE = prove
(`!A:real^N^N B.  ((\n. (&1 / &(FACT n)) %% (A matrix_pow n)) 
          msums B) (from 0) <=> B = matrix_exp (A)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC [MATRIX_EXP_CONVERGES] THEN
  DISCH_THEN(MP_TAC o C CONJ (SPEC `A:real^N^N` MATRIX_EXP_CONVERGES)) THEN
  REWRITE_TAC [MSERIES_UNIQUE]);;
  
let MATRIX_EXP_TRANSP = prove
 (`!A:real^N^N.transp (matrix_exp A) = matrix_exp (transp  A)`,
    GEN_TAC THEN REWRITE_TAC [matrix_exp] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    MATCH_MP_TAC INFMSUM_UNIQUE THEN 
    REWRITE_TAC [GSYM TRANSP_MATRIX_CMUL;MATRIX_POW_TRANSP;
    GSYM MSUMS_TRANSP] THEN SIMP_TAC[GSYM matrix_exp;MATRIX_EXP_CONVERGES]);;
    
let TRANSP_TRANS_EXP = prove
 (`!c A:real^N^N. transp( matrix_exp (c %% A)) = matrix_exp (c %% transp(A))`,
   REPEAT GEN_TAC THEN SIMP_TAC[MATRIX_EXP_TRANSP;TRANSP_MATRIX_CMUL] );;
   
(******proving the commutative properties of matrix exponential******)
   
let LIMIT_REAL_SUM = prove
(`!f:A->B->real l s. 
    FINITE s /\ (!i. i IN s ==> limit euclideanreal (f i) (l i) net)
    ==> (limit euclideanreal (\x. sum s (\i. f i x)) (sum s l) net)`,
    GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN 
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN 
    SIMP_TAC [SUM_CLAUSES; NOT_IN_EMPTY; LIMIT_REAL_CONST; 
              LIMIT_REAL_ADD; IN_INSERT; ETA_AX]);;

let MATRIX_LIM_LMUL = prove
 (`!net:(A)net f:A->real^N^M l A:real^M^P. (f ->-> l) net ==> 
    ((\x.  (A ** (f x))) ->->  (A ** l)) net`,
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[MATRIX_LIM_COMPONENTWISE_REAL] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [matrix_mul; CART_EQ; LAMBDA_BETA] THEN 
  MATCH_MP_TAC LIMIT_REAL_SUM THEN 
  SIMP_TAC [FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN 
  MATCH_MP_TAC LIMIT_REAL_LMUL THEN ASM_SIMP_TAC[]);;
              
let MATRIX_LIM_RMUL = prove
 (`!net:(A)net f:A->real^N^M l A. (f ->-> l) net ==> 
    ((\x.  ((f x) ** A)) ->->  (l ** A)) net`,
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[MATRIX_LIM_COMPONENTWISE_REAL] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [matrix_mul; CART_EQ; LAMBDA_BETA] THEN 
  MATCH_MP_TAC LIMIT_REAL_SUM THEN 
  SIMP_TAC [FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN 
  MATCH_MP_TAC LIMIT_REAL_RMUL THEN ASM_SIMP_TAC[]);;
    
let MSERIES_LMUL = prove
 (`!A:num->real^N^M A0 B:real^M^P s. (A msums A0) s ==> ((\n.B ** (A n)) msums (B ** A0)) s`,
 SIMP_TAC [msums; FINITE_INTER_NUMSEG;GSYM MSUM_MATRIX_LMUL; MATRIX_LIM_LMUL]);;
 
let MSERIES_RMUL = prove
 (`!A:num->real^N^M A0 B:real^P^N s. (A msums A0) s ==> ((\n.(A n) ** B) msums (A0 ** B)) s`,
 SIMP_TAC [msums; FINITE_INTER_NUMSEG;GSYM MSUM_MATRIX_RMUL; MATRIX_LIM_RMUL]);;

let INFMSUM_LMUL = prove
(`!s x:num->real^N^M A:real^M^P. msummable s x ==>
    infmsum s (\n. A ** (x n)) = A ** (infmsum s x)`,
        REPEAT STRIP_TAC THEN MATCH_MP_TAC INFMSUM_UNIQUE THEN
        MATCH_MP_TAC MSERIES_LMUL THEN ASM_REWRITE_TAC[MSUMS_INFSUM]);;
 
let INFMSUM_RMUL = prove
(`!s x:num->real^N^M A:real^P^N. msummable s x ==>
    infmsum s (\n. (x n) ** A) = (infmsum s x) ** A`,
        REPEAT STRIP_TAC THEN MATCH_MP_TAC INFMSUM_UNIQUE THEN
        MATCH_MP_TAC MSERIES_RMUL THEN ASM_REWRITE_TAC[MSUMS_INFSUM]);;

let MATRIX_EXP_COMM_LEMMA = prove
 (`!A B:real^N^N. A ** B = B ** A ==> matrix_exp A ** B = B ** matrix_exp A`,
    REPEAT STRIP_TAC THEN SIMP_TAC[matrix_exp] THEN ASSUME_TAC MATRIX_EXP_CONVERGES THEN 
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP MSUMS_SUMMABLE o SPEC `A:real^N^N`) THEN
    ASM_SIMP_TAC[GSYM INFMSUM_LMUL;GSYM INFMSUM_RMUL] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    SIMP_TAC[MATRIX_MUL_LMUL;MATRIX_MUL_RMUL] THEN
    ASM_SIMP_TAC[GSYM MATRIX_POW_SYM]);;
    
(*************derivative of R^1^1->R^N^N **********************************)

(* ------------------------------------------------------------------------- *)
(* supplement to mbasis                                                 *)
(* ------------------------------------------------------------------------- *)

(*
let MBASIS_EQ_0 = prove
 (`!i j. (mbasis i j :real^N^M = mat 0) <=>
         ~((i IN 1..dimindex(:M)) /\ (j IN 1..dimindex(:N)))`,
  SIMP_TAC[CART_EQ; MBASIS_COMPONENT; MAT_COMPONENT; IN_NUMSEG] THEN
  MESON_TAC[REAL_ARITH `~(&1 = &0)`]);;
  
let MBASIS_NONZERO = prove
 (`!i j. (1 <= i /\ i <= dimindex(:M)) /\ (1 <= j /\ j <= dimindex(:N))
       ==> ~(mbasis i j :real^N^M = mat 0)`,
  REWRITE_TAC[MBASIS_EQ_0; IN_NUMSEG]);;
*)

let TRIVIAL_MATRIX_LIMIT_WITHIN = prove
 (`!a:real^N^M. trivial_limit (matrix_at a within s) <=> ~(a matrix_limit_point_of s)`,
  REWRITE_TAC[matrix_at; GSYM MTOPOLOGY_EUCLIDEAN_METRIC] THEN
  SIMP_TAC[TRIVIAL_LIMIT_ATPOINTOF_WITHIN; HAUSDORFF_SPACE_MTOPOLOGY] THEN
  REWRITE_TAC[MTOPOLOGY_EUCLIDEAN_METRIC; MATRIX_LIMIT_POINT_IN_DERIVED_SET]);;
  
(* ------------------------------------------------------------------------- *)
(* Uniqueness of derivative.                                                 *)
(* ------------------------------------------------------------------------- *)

let FRECHET_MATRIX_DERIVATIVE_UNIQUE_WITHIN = prove
 (`!f:real^Q^P->real^N^M f' f'' x s.
     (f has_matrix_derivative f') (matrix_at x within s) /\
     (f has_matrix_derivative f'') (matrix_at x within s) /\
     (!i j e. ((1 <= i /\ i <= dimindex(:P)) /\ (1 <= j /\ j <= dimindex(:Q))) /\ &0 < e
            ==> ?d. &0 < abs(d) /\ abs(d) < e /\ (x + d %% mbasis i j) IN s)
     ==> f' = f''`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_matrix_derivative] THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^Q^P) matrix_limit_point_of s` ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_LIMPT_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`1`; `1`; `e:real`]) THEN
    ASM_REWRITE_TAC[DIMINDEX_GE_1; LE_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(x:real^Q^P) + d %% mbasis 1 1` THEN
    ASM_REWRITE_TAC[matrix_dist] THEN ONCE_REWRITE_TAC[GSYM MATRIX_SUB_EQ] THEN
    ASM_SIMP_TAC[MATRIX_ADD_SUB; FNORM_MUL; FNORM_BASIS; DIMINDEX_GE_1; LE_REFL;
                 MATRIX_CMUL_EQ_0; REAL_MUL_RID; DE_MORGAN_THM; REAL_ABS_NZ;
                 MBASIS_NONZERO];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP MATRIX_LIM_SUB) THEN
  SUBGOAL_THEN `netlimit(matrix_at x within s) = x:real^Q^P` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[MATRIX_NETLIMIT_WITHIN; TRIVIAL_MATRIX_LIMIT_WITHIN]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_SUB_LDISTRIB; FNORM_MUL] THEN
  REWRITE_TAC[CMATRIX_ARITH
   `fx - (fa + f'') - (fx - (fa + f')):real^Q^P = f' - f''`] THEN
  DISCH_TAC THEN MATCH_MP_TAC MLINEAR_EQ_STDBASIS THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM MATRIX_SUB_EQ] THEN
  GEN_REWRITE_TAC I [TAUT `p = ~ ~p`] THEN
  PURE_REWRITE_TAC[GSYM FNORM_POS_LT] THEN DISCH_TAC THEN ABBREV_TAC
   `e = fnorm((f':real^Q^P->real^N^M) (mbasis i j) - f''(mbasis i j :real^Q^P))` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATRIX_LIM_WITHIN]) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[matrix_dist; MATRIX_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`; `d:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x:real^Q^P) + c %% mbasis i j`) THEN
  ASM_REWRITE_TAC[MATRIX_ADD_SUB; FNORM_MUL] THEN
  ASM_SIMP_TAC[FNORM_BASIS; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[CMATRIX_ARITH ` !A:real B C:real^N^M. A %% B - A %% C = A %% (B - C)`] THEN
  ASM_SIMP_TAC[MLINEAR_CMUL;FNORM_MUL] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_ABS] THEN
  SIMP_TAC[CMATRIX_ARITH `!c:real A B C D:real^N^M. 
              A -(B + c %% C) -(A - (B + c %% D)) = c %% (D - C)`] THEN 
  ASM_SIMP_TAC[FNORM_MUL] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_LT_REFL]);;

let FRECHET_MATRIX_DERIVATIVE_UNIQUE_AT = prove
 (`!f:real^Q^P->real^N^M f' f'' x.
     (f has_matrix_derivative f') (matrix_at x) /\ (f has_matrix_derivative f'') (matrix_at x)
     ==> f' = f''`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_MATRIX_DERIVATIVE_UNIQUE_WITHIN THEN
  MAP_EVERY EXISTS_TAC
   [`f:real^Q^P->real^N^M`; `x:real^Q^P`; `(:real^Q^P)`] THEN
  ASM_REWRITE_TAC[IN_UNIV; MATRIX_WITHIN_UNIV] THEN
  MESON_TAC[REAL_ARITH `&0 < e ==> &0 < abs(e / &2) /\ abs(e / &2) < e`]);;
  
(*------------------------------------------------------------------------------*)
(*           lift and drop for matrix                                           *)
(*                                                                              *)
(*------------------------------------------------------------------------------*)

let LIFT_LIFT_NUM = prove
 (`!n. lift_lift(&n) = mat n`,
  SIMP_TAC[CART_EQ; lift_lift; mat; LAMBDA_BETA;DIMINDEX_1;LE_ANTISYM]);;
  
let LIFT_LIFT_CMUL = prove
 (`!x c. lift_lift(c * x) = c %% lift_lift(x)`,
  SIMP_TAC[CART_EQ; lift_lift; LAMBDA_BETA; MATRIX_CMUL_COMPONENT]);;
  
let LIFT_DROP2 = prove
 (`(!x. lift_lift(drop_drop x) = x) /\ (!x. drop_drop(lift_lift x) = x)`,
  SIMP_TAC[lift_lift; drop_drop; CART_EQ; LAMBDA_BETA; DIMINDEX_1; LE_ANTISYM]);;
  
let DROP_DROP_EQ = prove
 (`!x y. (drop_drop x = drop_drop y) <=> (x = y)`,
  MESON_TAC[LIFT_DROP2]);;
  
let DROP_DROP_CMUL = prove
 (`!x c. drop_drop(c %% x) = c * drop_drop(x)`,
  MESON_TAC[LIFT_DROP2; LIFT_LIFT_CMUL]);;
  
let DROP_DROP_MAT = prove
 (`!n. drop_drop(mat n) = &n`,
  MESON_TAC[LIFT_DROP2; LIFT_LIFT_NUM]);;  

(* ------------------------------------------------------------------------- *)
(* Considering derivative R(^1^1)->R^N^M as a matrix.                            *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("has_m_derivative",(12,"right"));;

let has_m_derivative = new_definition
 `(f has_m_derivative f') net <=>
        (f has_matrix_derivative (\x. drop_drop(x) %% f')) net`;;

let m_derivative = new_definition
 `m_derivative (f:real^1^1->real^N^M) net =
        @f'. (f has_m_derivative f') net`;;
        
parse_as_infix ("m_differentiable",(12,"right"));;

let m_differentiable = new_definition
 `f m_differentiable net <=> ?f'. (f has_m_derivative f') net`;;
        
let M_DERIVATIVE_UNIQUE_AT = prove
 (`!f:real^1^1->real^N^M x f' f''.
     (f has_m_derivative f') (matrix_at x) /\
     (f has_m_derivative f'') (matrix_at x)
     ==> f' = f''`,
  REWRITE_TAC[has_m_derivative; drop_drop] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1^1->real^N^M`;
                 `\x. drop_drop x %% (f':real^N^M)`; `\x. drop_drop x %% (f'':real^N^M)`;
                `x:real^1^1`] FRECHET_MATRIX_DERIVATIVE_UNIQUE_AT) THEN
  ASM_SIMP_TAC[DIMINDEX_1; LE_ANTISYM; drop_drop] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `mat 1:real^1^1`) THEN
  SIMP_TAC[MAT_COMPONENT; DIMINDEX_1; ARITH; MATRIX_CMUL_LID]);;
  
let M_DERIVATIVE_AT = prove
 (`!f:real^1^1->real^N^M f' x.
        (f has_m_derivative f') (matrix_at x)
        ==> m_derivative f (matrix_at x) = f'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC M_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC [`f:real^1^1->real^N^M`; `x:real^1^1`] THEN
  ASM_REWRITE_TAC[m_derivative] THEN CONV_TAC SELECT_CONV THEN
  ASM_MESON_TAC[]);;
  
let HAS_M_DERIVATIVE_CONST = prove
 (`!c net. ((\x. c) has_m_derivative mat 0) net`,
  REWRITE_TAC[has_m_derivative] THEN
  REWRITE_TAC[MATRIX_CMUL_RZERO; HAS_MATRIX_DERIVATIVE_CONST]);;

let M_DERIVATIVE_CONST_AT = prove
 (`!c:real^N^M a. m_derivative (\x. c) (matrix_at a) = mat 0`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC M_DERIVATIVE_AT THEN
  REWRITE_TAC[HAS_M_DERIVATIVE_CONST]);;
  
let HAS_M_DERIVATIVE_ID = prove
 (`!net. ((\x. x) has_m_derivative (mat 1)) net`,
  REWRITE_TAC[has_m_derivative] THEN
  SUBGOAL_THEN `(\x. drop_drop x %% mat 1) = (\x. x)`
   (fun th -> REWRITE_TAC[HAS_MATRIX_DERIVATIVE_ID; th]) THEN
  REWRITE_TAC[FUN_EQ_THM; GSYM DROP_DROP_EQ; DROP_DROP_CMUL; DROP_DROP_MAT] THEN
  REAL_ARITH_TAC);;
  
let HAS_M_DERIVATIVE_CMUL = prove
 (`!f f' net c. (f has_m_derivative f') net
                ==> ((\x. c %% f(x)) has_m_derivative (c %% f')) net`,
  SIMP_TAC[has_m_derivative] THEN
  ONCE_REWRITE_TAC[CMATRIX_ARITH `a %% b %% x:real^N^M = b %% a %% x`] THEN
  SIMP_TAC[HAS_MATRIX_DERIVATIVE_CMUL]);;
  
let HAS_M_DERIVATIVE_DROP2_CMUL = REWRITE_RULE [GSYM has_m_derivative]
    HAS_MATRIX_DERIVATIVE_DROP2_CMUL;;
      
(* ------------------------------------------------------*)

let HAS_M_DERIVATIVE_CMUL_EQ = prove
 (`!f:real^1^1->real^N^M f' net c.
       ~(c = &0)
       ==> (((\x. c %% f(x)) has_m_derivative (c %% f')) net <=>
            (f has_m_derivative f') net)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_M_DERIVATIVE_CMUL) THENL
   [DISCH_THEN(MP_TAC o SPEC `inv(c):real`);
    DISCH_THEN(MP_TAC o SPEC `c:real`)] THEN
  ASM_SIMP_TAC[MATRIX_CMUL_ASSOC; REAL_MUL_LINV; MATRIX_CMUL_LID; ETA_AX]);;

let HAS_M_DERIVATIVE_NEG = prove
 (`!f:real^1^1->real^N^M f' net. (f has_m_derivative f') net
            ==> ((\x. --(f(x))) has_m_derivative (--f')) net`,
  SIMP_TAC[has_m_derivative; MATRIX_CMUL_RNEG; HAS_MATRIX_DERIVATIVE_NEG]);;

let HAS_M_DERIVATIVE_NEG_EQ = prove
 (`!f:real^1^1->real^N^M f' net. ((\x. --(f(x))) has_m_derivative --f') net <=>
              (f has_m_derivative f') net`,
  SIMP_TAC[has_m_derivative; HAS_MATRIX_DERIVATIVE_NEG_EQ; MATRIX_CMUL_RNEG]);;
  
let HAS_M_DERIVATIVE_ADD = prove
 (`!f:real^1^1->real^N^M f' g g' net.
        (f has_m_derivative f') net /\ (g has_m_derivative g') net
        ==> ((\x. f(x) + g(x)) has_m_derivative (f' + g')) net`,
  SIMP_TAC[has_m_derivative; MATRIX_CMUL_ADD_LDISTRIB; HAS_MATRIX_DERIVATIVE_ADD]);;

let HAS_M_DERIVATIVE_SUB = prove
 (`!f:real^1^1->real^N^M f' g g' net.
        (f has_m_derivative f') net /\ (g has_m_derivative g') net
        ==> ((\x. f(x) - g(x)) has_m_derivative (f' - g')) net`,
  SIMP_TAC[has_m_derivative; MATRIX_CMUL_SUB_LDISTRIB; HAS_MATRIX_DERIVATIVE_SUB]);;
  
let HAS_M_DERIVATIVE_MUL_WITHIN = prove
 (`!f:real^1^1->real^N^M f' g:real^1^1->real^P^N g' x:real^1^1 s.
        (f has_m_derivative f') (matrix_at x within s) /\
        (g has_m_derivative g') (matrix_at x within s)
        ==> ((\x. f(x) ** g(x)) has_m_derivative
             (f(x) ** g' + f' ** g(x))) (matrix_at x within s)`,
  REPEAT GEN_TAC THEN SIMP_TAC[has_m_derivative] THEN
  MP_TAC (ISPECL[`f:real^1^1->real^N^M`;`g:real^1^1->real^P^N`;
                 `\x:real^1^1. drop_drop x %% (f':real^N^M)`;
                 `\x:real^1^1. drop_drop x %% (g':real^P^N)`;
                 `x:real^1^1`;`s:real^1^1->bool`] HAS_MATRIX_DERIVATIVE_MUL_WITHIN) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[FUN_EQ_THM] THEN GEN_TAC THEN 
  SIMP_TAC[MATRIX_CMUL_ADD_LDISTRIB;MATRIX_MUL_RMUL;MATRIX_MUL_LMUL]);;

let HAS_M_DERIVATIVE_MUL_AT = prove
 (`!f f' g g' x.
        (f has_m_derivative f') (matrix_at x) /\
        (g has_m_derivative g') (matrix_at x)
        ==> ((\x. f(x) ** g(x)) has_m_derivative
             (f(x) ** g' + f' ** g(x))) (matrix_at x)`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  REWRITE_TAC[HAS_M_DERIVATIVE_MUL_WITHIN]);;

let HAS_M_DERIVATIVE_BILINEAR_WITHIN = prove
 (`!h:real^N^M->real^Q^P->real^S^R f g f' g' x s.
        (f has_m_derivative f') (matrix_at x within s) /\
        (g has_m_derivative g') (matrix_at x within s) /\
        bimlinear h
        ==> ((\x. h (f x) (g x)) has_m_derivative
             (h (f x) g' + h f' (g x))) (matrix_at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_m_derivative] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_MATRIX_DERIVATIVE_BILINEAR_WITHIN) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bimlinear; mlinear]) THEN
  ASM_REWRITE_TAC[MATRIX_CMUL_ADD_LDISTRIB]);;  
  
let HAS_M_DERIVATIVE_BILINEAR_AT = prove
 (`!h:real^N^M->real^Q^P->real^S^R f g f' g' x.
        (f has_m_derivative f') (matrix_at x) /\
        (g has_m_derivative g') (matrix_at x) /\
        bimlinear h
        ==> ((\x. h (f x) (g x)) has_m_derivative
             (h (f x) g' + h f' (g x))) (matrix_at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_m_derivative] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_MATRIX_DERIVATIVE_BILINEAR_AT) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bimlinear; mlinear]) THEN
  ASM_REWRITE_TAC[MATRIX_CMUL_ADD_LDISTRIB]);;

let HAS_M_DERIVATIVE_AT_WITHIN = prove
 (`!f x s. (f has_m_derivative f') (matrix_at x)
           ==> (f has_m_derivative f') (matrix_at x within s)`,
  SIMP_TAC[has_m_derivative; HAS_MATRIX_DERIVATIVE_AT_WITHIN]);;
  
let M_DIFF_CHAIN_AT = prove
 (`!f g f' g' x.
         (f has_m_derivative f') (matrix_at x) /\
         (g has_m_derivative g') (matrix_at (f x))
         ==> ((g o f) has_m_derivative (drop_drop f' %% g')) (matrix_at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_m_derivative] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MATRIX_DIFF_CHAIN_AT) THEN
  REWRITE_TAC[o_DEF; DROP_DROP_CMUL; GSYM MATRIX_CMUL_ASSOC]);;

let M_DIFF_CHAIN_WITHIN = prove
 (`!f g f' g' s x.
         (f has_m_derivative f') (matrix_at x within s) /\
         (g has_m_derivative g') (matrix_at (f x) within IMAGE f s)
         ==> ((g o f) has_m_derivative (drop_drop f' %% g')) (matrix_at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_m_derivative] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MATRIX_DIFF_CHAIN_WITHIN) THEN
  REWRITE_TAC[o_DEF; DROP_DROP_CMUL; GSYM MATRIX_CMUL_ASSOC]);;  
  
let HAS_M_DERIVATIVE_ZERO_CONSTANT = prove
 (`!f s.
        matrix_convex s /\
        (!x. x IN s ==> (f has_m_derivative mat 0) (matrix_at x within s))
        ==> ?c. !x. x IN s ==> f(x) = c`,
  REWRITE_TAC[has_m_derivative; MATRIX_CMUL_RZERO] THEN
  REWRITE_TAC[HAS_MATRIX_DERIVATIVE_ZERO_CONSTANT]);;

let HAS_M_DERIVATIVE_ZERO_UNIQUE = prove
 (`!f s c a.
        matrix_convex s /\ a IN s /\ f a = c /\
        (!x. x IN s ==> (f has_m_derivative mat 0) (matrix_at x within s))
        ==> !x. x IN s ==> f(x) = c`,
  REWRITE_TAC[has_m_derivative; MATRIX_CMUL_RZERO] THEN
  REWRITE_TAC[ HAS_MATRIX_DERIVATIVE_ZERO_UNIQUE]);;
 
let HAS_M_DERIVATIVE_CHAIN = prove
 (`!P f g.
        (!x. P x ==> (g has_m_derivative g'(x)) (matrix_at x))
        ==> (!x s. (f has_m_derivative f') (matrix_at x within s) /\ P(f x)
                   ==> ((\x. g(f x)) has_m_derivative drop_drop f' %% g'(f x))
                       (matrix_at x within s)) /\
            (!x. (f has_m_derivative f') (matrix_at x) /\ P(f x)
                 ==> ((\x. g(f x)) has_m_derivative drop_drop f' %% g'(f x))
                     (matrix_at x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM o_DEF] THEN
  ASM_MESON_TAC[M_DIFF_CHAIN_WITHIN; M_DIFF_CHAIN_AT;
                HAS_M_DERIVATIVE_AT_WITHIN]);;
                
let HAS_M_DERIVATIVE_CHAIN_UNIV = prove
 (`!f:real^1^1->real^1^1 g:real^1^1->real^N^M. (!x. (g has_m_derivative g'(x)) (matrix_at x))
         ==> (!x s. (f has_m_derivative f') (matrix_at x within s)
                    ==> ((\x. g(f x)) has_m_derivative drop_drop f' %% g'(f x))
                        (matrix_at x within s)) /\
             (!x. (f has_m_derivative f') (matrix_at x)
                  ==> ((\x. g(f x)) has_m_derivative drop_drop f' %% g'(f x))
                      (matrix_at x))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\x:real^1^1. T`;`f:real^1^1->real^1^1`;`g:real^1^1->real^N^M`] HAS_M_DERIVATIVE_CHAIN) THEN SIMP_TAC[]);;
  
let M_DIFFERENTIABLE_AT_WITHIN = prove
 (`!f s z. f m_differentiable (matrix_at z)
           ==> f m_differentiable (matrix_at z within s)`,
  REWRITE_TAC[m_differentiable] THEN
  MESON_TAC[HAS_M_DERIVATIVE_AT_WITHIN]);;
  
let HAS_M_DERIVATIVE_IMP_CONTINUOUS_AT = prove
 (`!f f' x. (f has_m_derivative f') (matrix_at x) ==> f matrix_continuous matrix_at x`,
  REWRITE_TAC[has_m_derivative] THEN
  MESON_TAC[matrix_differentiable; MATRIX_DIFFERENTIABLE_IMP_CONTINUOUS_AT]);;
 
(* ------------------------------------------------------------------------- *)
(* Uniformly convergent sequence of matrix derivatives.                      *)
(* ------------------------------------------------------------------------- *)

let HAS_MATRIX_DERIVATIVE_SEQUENCE_LIPSCHITZ = prove
 (`!s f:num->real^N^M->real^Q^P f' g'.
        matrix_convex s /\
        (!n x. x IN s ==> ((f n) has_matrix_derivative (f' n x)) (matrix_at x within s)) /\
        (!e. &0 < e
             ==> ?N. !n x h. n >= N /\ x IN s
                             ==> fnorm(f' n x h - g' x h) <= e * fnorm(h))
        ==> !e. &0 < e
                ==> ?N. !m n x y. m >= N /\ n >= N /\ x IN s /\ y IN s
                                  ==> fnorm((f m x - f n x) - (f m y - f n y))
                                      <= e * fnorm(x - y)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
  ASM_CASES_TAC `m:num >= N` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n:num >= N` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MATRIX_DIFFERENTIABLE_BOUND THEN
  EXISTS_TAC `\x h. (f':num->real^N^M->real^N^M->real^Q^P) m x h - f' n x h` THEN
  ASM_SIMP_TAC[HAS_MATRIX_DERIVATIVE_SUB; ETA_AX] THEN
  X_GEN_TAC `x:real^N^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!h. fnorm((f':num->real^N^M->real^N^M->real^Q^P) m x h - f' n x h) <= e * fnorm(h)`
  MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[HAS_MATRIX_DERIVATIVE_WITHIN_ALT]) THEN
  ASM_SIMP_TAC[MONORM; MLINEAR_COMPOSE_SUB; ETA_AX] THEN
  X_GEN_TAC `h:real^N^M` THEN SUBST1_TAC(CMATRIX_ARITH
   `(f':num->real^N^M->real^N^M->real^Q^P) m x h - f' n x h =
    (f' m x h - g' x h) + --(f' n x h - g' x h)`) THEN
  MATCH_MP_TAC FNORM_TRIANGLE_LE THEN
  ASM_SIMP_TAC[FNORM_NEG; REAL_ARITH
   `a <= e / &2 * h /\ b <= e / &2 * h ==> a + b <= e * h`]);;

let HAS_MATRIX_DERIVATIVE_SEQUENCE = prove
 (`!s f:num->real^N^M->real^Q^P f' g'.
        matrix_convex s /\
        (!n x. x IN s ==> ((f n) has_matrix_derivative (f' n x)) (matrix_at x within s)) /\
        (!e. &0 < e
             ==> ?N. !n x h. n >= N /\ x IN s
                             ==> fnorm(f' n x h - g' x h) <= e * fnorm(h)) /\
        (?x l. x IN s /\ ((\n. f n x) ->-> l) sequentially)
        ==> ?g. !x. x IN s
                    ==> ((\n. f n x) ->-> g x) sequentially /\
                        (g has_matrix_derivative g'(x)) (matrix_at x within s)`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "O") MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_TAC "A"
   `!e. &0 < e
        ==> ?N. !m n x y. m >= N /\ n >= N /\ x IN s /\ y IN s
                          ==> fnorm(((f:num->real^N^M->real^Q^P) m x - f n x) -
                                   (f m y - f n y))
                               <= e * fnorm(x - y)`
   [MATCH_MP_TAC HAS_MATRIX_DERIVATIVE_SEQUENCE_LIPSCHITZ THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN
   `?g:real^N^M->real^Q^P. !x. x IN s ==> ((\n. f n x) ->-> g x) sequentially`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `x:real^N^M` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [MATRIX_CONVERGENT_EQ_CAUCHY] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MATRIX_CONVERGENT_IMP_CAUCHY) THEN
    REWRITE_TAC[matrix_cauchy; matrix_dist] THEN DISCH_THEN(LABEL_TAC "B") THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:real^N^M = x0` THEN ASM_SIMP_TAC[] THEN
    REMOVE_THEN "B" (MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "A" (MP_TAC o SPEC `e / &2 / fnorm(x - x0:real^N^M)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; FNORM_POS_LT; REAL_HALF; MATRIX_SUB_EQ] THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
    EXISTS_TAC `N1 + N2:num` THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (STRIP_ASSUME_TAC o MATCH_MP
      (ARITH_RULE `m >= N1 + N2:num ==> m >= N1 /\ m >= N2`))) THEN
    SUBST1_TAC(CMATRIX_ARITH
     `(f:num->real^N^M->real^Q^P) m x - f n x =
      (f m x - f n x - (f m x0 - f n x0)) + (f m x0 - f n x0)`) THEN
    MATCH_MP_TAC FNORM_TRIANGLE_LT THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`m:num`; `n:num`; `x:real^N^M`; `x0:real^N^M`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; FNORM_EQ_0; MATRIX_SUB_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(LABEL_TAC "B") THEN X_GEN_TAC `x:real^N^M` THEN DISCH_TAC THEN
  REWRITE_TAC[HAS_MATRIX_DERIVATIVE_WITHIN_ALT] THEN
  SUBGOAL_TAC "C"
   `!e. &0 < e
        ==> ?N. !n x y. n >= N /\ x IN s /\ y IN s
                        ==> fnorm(((f:num->real^N^M->real^Q^P) n x - f n y) -
                                 (g x - g y))
                             <= e * fnorm(x - y)`
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "A" (MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`u:real^N^M`; `v:real^N^M`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN `m:num` o SPECL
      [`m:num`; `u:real^N^M`; `v:real^N^M`]) THEN
    DISCH_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` MATRIX_LIM_FNORM_UBOUND) THEN
    EXISTS_TAC
      `\m. ((f:num->real^N^M->real^Q^P) n u - f n v) - (f m u - f m v)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    ASM_SIMP_TAC[SEQUENTIALLY; MATRIX_LIM_SUB; MATRIX_LIM_CONST] THEN EXISTS_TAC `N:num` THEN
    ONCE_REWRITE_TAC[CMATRIX_ARITH
     `(x - y) - (u - v) = (x - u) - (y -  v):real^Q^P`] THEN
    REWRITE_TAC[GSYM GE]  THEN ASM_MESON_TAC[]] THEN
  CONJ_TAC THENL
   [SUBGOAL_TAC "D"
    `!u. ((\n. (f':num->real^N^M->real^N^M->real^Q^P) n x u) ->-> g' x u) sequentially`
     [REWRITE_TAC[MATRIX_LIM_SEQUENTIALLY; matrix_dist] THEN REPEAT STRIP_TAC THEN
      ASM_CASES_TAC `u = mat 0:real^N^M` THENL
       [REMOVE_THEN "O" (MP_TAC o SPEC `e:real`);
        REMOVE_THEN "O" (MP_TAC o SPEC `e / &2 / fnorm(u:real^N^M)`)] THEN
      ASM_SIMP_TAC[FNORM_POS_LT; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^N^M`; `u:real^N^M`]) THEN
      DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
      ASM_SIMP_TAC[GE; FNORM_0; REAL_MUL_RZERO; FNORM_LE_0] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; FNORM_EQ_0] THEN
      UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC] THEN
    REWRITE_TAC[mlinear] THEN ONCE_REWRITE_TAC[GSYM MATRIX_SUB_EQ] THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`u:real^N^M`; `v:real^N^M`];
      MAP_EVERY X_GEN_TAC [`c:real`; `u:real^N^M`]] THEN
    MATCH_MP_TAC(ISPEC `sequentially` MATRIX_LIM_UNIQUE) THENL
     [EXISTS_TAC
       `\n. (f':num->real^N^M->real^N^M->real^Q^P) n x (u + v) -
            (f' n x u + f' n x v)`;
      EXISTS_TAC
       `\n. (f':num->real^N^M->real^N^M->real^Q^P) n x (c %% u) -
            c %% f' n x u`] THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; MATRIX_LIM_SUB; MATRIX_LIM_ADD; MATRIX_LIM_CMUL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[has_matrix_derivative_within; mlinear]) THEN
    ASM_SIMP_TAC[MATRIX_SUB_REFL; MATRIX_LIM_CONST];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MAP_EVERY (fun s -> REMOVE_THEN s (MP_TAC o SPEC `e / &3`)) ["C"; "O"] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "C")) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "A")) THEN
  REMOVE_THEN "C" (MP_TAC o GEN `y:real^N^M` o
   SPECL [`N1 + N2:num`; `x:real^N^M`; `y - x:real^N^M`]) THEN
  REMOVE_THEN "A" (MP_TAC o GEN `y:real^N^M` o
   SPECL [`N1 + N2:num`; `y:real^N^M`; `x:real^N^M`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N1 + N2:num`; `x:real^N^M`]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `m + n >= m:num /\ m + n >= n`] THEN
  REWRITE_TAC[HAS_MATRIX_DERIVATIVE_WITHIN_ALT] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3` o CONJUNCT2) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(LABEL_TAC "D1") THEN DISCH_THEN(LABEL_TAC "D2") THEN
  EXISTS_TAC `d1:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N^M` THEN
  DISCH_TAC THEN REMOVE_THEN "D2" (MP_TAC o SPEC `y:real^N^M`) THEN
  REMOVE_THEN "D1" (MP_TAC o SPEC `y:real^N^M`) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_LT_TRANS; FNORM_SUB_SYM]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N^M`) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_LT_TRANS; FNORM_SUB_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `d <= a + b + c
    ==> a <= e / &3 * n ==> b <= e / &3 * n ==> c <= e / &3 * n
        ==> d <= e * n`) THEN
  GEN_REWRITE_TAC (funpow 2 RAND_CONV o LAND_CONV) [FNORM_SUB_SYM] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(fnorm(x + y + z) = fnorm(a)) /\
    fnorm(x + y + z) <= fnorm(x) + fnorm(y + z) /\
    fnorm(y + z) <= fnorm(y) + fnorm(z)
    ==> fnorm(a) <= fnorm(x) + fnorm(y) + fnorm(z)`) THEN
  REWRITE_TAC[FNORM_TRIANGLE] THEN AP_TERM_TAC THEN CMATRIX_ARITH_TAC);;
  
(* ------------------------------------------------------------------------- *)
(* Differentiation of a series.                                              *)
(* ------------------------------------------------------------------------- *)

let HAS_MATRIX_DERIVATIVE_SERIES = prove
 (`!s f:num->real^N^M->real^Q^P f' g' k.
        matrix_convex s /\
        (!n x. x IN s ==> ((f n) has_matrix_derivative (f' n x)) (matrix_at x within s)) /\
        (!e. &0 < e
             ==> ?N. !n x h. n >= N /\ x IN s
                             ==> fnorm(msum(k INTER (0..n)) (\i. f' i x h) -
                                      g' x h) <= e * fnorm(h)) /\
        (?x l. x IN s /\ ((\n. f n x) msums l) k)
        ==> ?g. !x. x IN s ==> ((\n. f n x) msums (g x)) k /\
                               (g has_matrix_derivative g'(x)) (matrix_at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[msums] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_MATRIX_DERIVATIVE_SEQUENCE THEN EXISTS_TAC
   `\n:num x:real^N^M h:real^N^M. msum(k INTER (0..n)) (\n. f' n x h):real^Q^P` THEN
  ASM_SIMP_TAC[ETA_AX; FINITE_INTER_NUMSEG; HAS_MATRIX_DERIVATIVE_MSUM]);;

(* ------------------------------------------------------------------------- *)
(* Matrix differentiation of sequences and series.                          *)
(* ------------------------------------------------------------------------- *)

let HAS_M_DERIVATIVE_SEQUENCE = prove
 (`!s f:num->real^1^1->real^N^M f' g'.
     matrix_convex s /\
     (!n x. x IN s ==> ((f n) has_m_derivative (f' n x)) (matrix_at x within s)) /\
     (!e. &0 < e
             ==> ?N. !n x. n >= N /\ x IN s
                             ==> fnorm(f' n x - g' x) <= e) /\
     (?x l. x IN s /\ ((\n. f n x) ->-> l) sequentially)
     ==> ?g. !x. x IN s
                    ==> ((\n. f n x) ->-> g x) sequentially /\
                        (g has_m_derivative g'(x)) (matrix_at x within s)`,
  REWRITE_TAC[has_m_derivative] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_MATRIX_DERIVATIVE_SEQUENCE THEN
  EXISTS_TAC `\n x h:real^1^1. drop_drop h %% 
   (f':num->real^1^1->real^N^M) n x` THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[GSYM MATRIX_CMUL_SUB_LDISTRIB; FNORM_MUL] THEN
  SIMP_TAC[drop_drop;FNORM_REAL] THEN
  ASM_MESON_TAC[REAL_LE_LMUL; REAL_ABS_POS; FNORM_POS_LE; REAL_MUL_SYM]);;

let HAS_M_DERIVATIVE_SERIES = prove
 (`!s f:num->real^1^1->real^N^M  f' g' k.
         matrix_convex s /\
         (!n x. x IN s
                ==> (f n has_m_derivative f' n x) (matrix_at x within s)) /\
         (!e. &0 < e
              ==> ?N. !n x. n >= N /\ x IN s
                            ==> fnorm(msum (k INTER (0..n)) (\i. f' i x) - g' x)
                                    <= e) /\
         (?x l. x IN s /\ ((\n. f n x) msums l) k)
         ==> ?g. !x. x IN s
                     ==> ((\n. f n x) msums g x) k /\
                         (g has_m_derivative g' x) (matrix_at x within s)`,
  REWRITE_TAC[has_m_derivative] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_MATRIX_DERIVATIVE_SERIES THEN
  EXISTS_TAC `\n x h:real^1^1. drop_drop h %% 
   (f':num->real^1^1->real^N^M) n x` THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  SIMP_TAC[GSYM MATRIX_CMUL_SUB_LDISTRIB; MSUM_LMUL;
          FNORM_MUL] THEN
  SIMP_TAC[drop_drop;FNORM_REAL] THEN
  ASM_MESON_TAC[REAL_LE_LMUL; REAL_ABS_POS; FNORM_POS_LE; REAL_MUL_SYM]);;
  
let HAS_M_DERIVATIVE_WITHIN_OPEN = prove
 (`!f f' a s.
         a IN s /\ matrix_open s
         ==> ((f has_m_derivative f') (matrix_at a within s) <=>
              (f has_m_derivative f') (matrix_at a))`,
  REWRITE_TAC[has_m_derivative; HAS_MATRIX_DERIVATIVE_WITHIN_OPEN]);;
  
 (* ------------------------------------------------------------------------- *)
(* Limit transformation for derivatives.                                     *)
(* ------------------------------------------------------------------------- *)

let MATRIX_LIM_TRANSFORM = prove
 (`!net f g l.
     ((\x. f x - g x) ->-> mat 0) net /\ (f ->-> l) net ==> (g ->-> l) net`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MATRIX_LIM_SUB) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MATRIX_LIM_NEG) THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN BINOP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  CMATRIX_ARITH_TAC);;
(*
let MATRIX_LIM_TRANSFORM_EVENTUALLY = prove
 (`!net f g l.
        eventually (\x. f x = g x) net /\ (f ->-> l) net ==> (g ->-> l) net`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP LIM_EVENTUALLY) MP_TAC) THEN
  MESON_TAC[LIM_TRANSFORM]);;*)

let MATRIX_LIM_TRANSFORM_WITHIN = prove
 (`!f g x s d.
        &0 < d /\
        (!x'. x' IN s /\ &0 < matrix_dist(x',x) /\ matrix_dist(x',x) < d ==> f(x') = g(x')) /\
        (f ->-> l) (matrix_at x within s)
        ==> (g ->-> l) (matrix_at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] MATRIX_LIM_TRANSFORM) THEN
  REWRITE_TAC[MATRIX_LIM_WITHIN] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `d:real` THEN
  ASM_SIMP_TAC[MATRIX_SUB_REFL; MATRIX_DIST_REFL]);;


let HAS_MATRIX_DERIVATIVE_TRANSFORM_WITHIN = prove
 (`!f f' g x:real^N^M s d.
       &0 < d /\ x IN s /\
       (!x':real^N^M. x' IN s /\ matrix_dist (x',x) < d ==> f x' = g x') /\
       (f has_matrix_derivative f') (matrix_at x within s)
       ==> (g has_matrix_derivative f') (matrix_at x within s)`,
  REPEAT GEN_TAC THEN SIMP_TAC[has_matrix_derivative_within; IMP_CONJ] THEN
  REPLICATE_TAC 4 DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
    MATRIX_LIM_TRANSFORM_WITHIN) THEN
  EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[MATRIX_DIST_REFL]);;
  
let HAS_MATRIX_DERIVATIVE_TRANSFORM_AT = prove
 (`!f f' g x d.
       &0 < d /\ (!x'. matrix_dist (x',x) < d ==> f x' = g x') /\
       (f has_matrix_derivative f') (matrix_at x)
       ==> (g has_matrix_derivative f') (matrix_at x)`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  MESON_TAC[HAS_MATRIX_DERIVATIVE_TRANSFORM_WITHIN; IN_UNIV]);;
(*
let LIM_TRANSFORM_WITHIN_OPEN = prove
 (`!f g:real^M->real^N s a l.
        open s /\ a IN s /\
        (!x. x IN s /\ ~(x = a) ==> f x = g x) /\
        (f ->-> l) (at a)
        ==> (g ->-> l) (at a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_TRANSFORM_AT THEN
  EXISTS_TAC `f:real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
  ASM_MESON_TAC[DIST_NZ; DIST_SYM]);;  

let HAS_MATRIX_DERIVATIVE_TRANSFORM_WITHIN_OPEN = prove
 (`!f g:real^N^M->real^Q^P s x.
        open s /\ x IN s /\
        (!y. y IN s ==> f y = g y) /\
        (f has_matrix_derivative f') (matrix_at x)
        ==> (g has_matrix_derivative f') (matrix_at x)`,
  REPEAT GEN_TAC THEN SIMP_TAC[has_matrix_derivative_at; IMP_CONJ] THEN
  REPLICATE_TAC 4 DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE
    [TAUT `a /\ b /\ c /\ d ==> e <=> a /\ b /\ c ==> d ==> e`]
    MATRIX_LIM_TRANSFORM_WITHIN_OPEN) THEN
  EXISTS_TAC `s:real^N^M->bool` THEN ASM_SIMP_TAC[]);; *)

(* ------------------------------------------------------------------------- *)
(* Limit transformation for derivatives.                                     *)
(* ------------------------------------------------------------------------- *)

let HAS_M_DERIVATIVE_TRANSFORM_WITHIN = prove
 (`!f f' g x s d.
       &0 < d /\ x IN s /\
       (!x'. x' IN s /\ matrix_dist (x',x) < d ==> f x' = g x') /\
       (f has_m_derivative f') (matrix_at x within s)
       ==> (g has_m_derivative f') (matrix_at x within s)`,
  REWRITE_TAC[has_m_derivative] THEN
  MESON_TAC[HAS_MATRIX_DERIVATIVE_TRANSFORM_WITHIN]);;

let HAS_M_DERIVATIVE_TRANSFORM_AT = prove
 (`!f f' g x d.
       &0 < d /\ (!x'. matrix_dist (x',x) < d ==> f x' = g x') /\
       (f has_m_derivative f') (matrix_at x)
       ==> (g has_m_derivative f') (matrix_at x)`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  MESON_TAC[HAS_M_DERIVATIVE_TRANSFORM_WITHIN; IN_UNIV]);;

(*let HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN = prove
 (`!f g:real^M->real^N s x.
        open s /\ x IN s /\
        (!y. y IN s ==> f y = g y) /\
        (f has_derivative f') (at x)
        ==> (g has_derivative f') (at x)`,
  REPEAT GEN_TAC THEN SIMP_TAC[has_derivative_at; IMP_CONJ] THEN
  REPLICATE_TAC 4 DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE
    [TAUT `a /\ b /\ c /\ d ==> e <=> a /\ b /\ c ==> d ==> e`]
    LIM_TRANSFORM_WITHIN_OPEN) THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[]);;*)
  
(* ------------------------------------------------------------------------- *)
(* The matrix exponential function.                                         *)
(* ------------------------------------------------------------------------- *)
  
let MATRIX_EXP_CONVERGES_UNIFORMLY_CAUCHY = prove
 (`!R e. &0 < e /\ &0 < R
         ==> ?N. !m n z:real^N^N. m >= N /\ fnorm(z) <= R
    ==> fnorm(msum(m..n) (\i. (&1 / &(FACT i)) %% (z matrix_pow i)))
                                     < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&1 / &2`; `(\i. (&1 / &(FACT i)) %% (R %% mat 1:real^N^N) matrix_pow i)`; `from 0`] MSERIES_RATIO) THEN
  REWRITE_TAC[MSERIES_CAUCHY; LEFT_FORALL_IMP_THM] THEN
  MP_TAC(SPEC `&2 * abs (R) :real` REAL_ARCH_SIMPLE) THEN
  SIMP_TAC [MATRIX_POW_CMUL; MATRIX_POW_ONE] THEN 
  REWRITE_TAC[FNORM_MUL; FNORM_MAT; REAL_MUL_LID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (c ==> d) ==> a ==> (b ==> c) ==> d`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN
    SIMP_TAC[FACT; real_pow; GSYM REAL_OF_NUM_MUL; real_div; REAL_INV_MUL] THEN
    SIMP_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN 
    SIMP_TAC [REAL_OF_NUM_LE; DIMINDEX_GE_1; SQRT_POS_LE; 
              ARITH_RULE `1 <= n ==> 0 <= n`; REAL_MUL_LID; REAL_MUL_RID;REAL_ABS_MUL] THEN 
    REWRITE_TAC[REAL_ARITH
     `(is * ik) * (z * zn) <= ((inv(&2)) * ik) * zn <=>
      &0 <= (&1 - (&2 * z) * is) * zn * ik`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_POW_LE; REAL_SUB_LE;
             REAL_LE_INV_EQ; REAL_ABS_POS] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LT_0] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_SUC] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN 
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    REWRITE_TAC[FROM_0; INTER_UNIV] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC [] THEN 
    MATCH_MP_TAC (REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN 
    REWRITE_TAC [MATRIX_CMUL_ASSOC; GSYM MSUM_MMUL;FNORM_MUL;
                 FNORM_MAT; REAL_MUL_LID] THEN 
    SUBGOAL_THEN `abs (sum (m..n) (\i. &1 / &(FACT i) * R pow i)) =
                  sum (m..n) (\i. &1 / &(FACT i) * R pow i)`
      SUBST1_TAC THENL  
      [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
       ASM_SIMP_TAC[REAL_LT_IMP_LE;REAL_LT_DIV; REAL_OF_NUM_LT;REAL_LT_MUL; LE_1;
                   FACT_LT; REAL_POW_LT;REAL_LT_01];
       ALL_TAC] THEN SIMP_TAC [GSYM SUM_RMUL] THEN 
    MATCH_MP_TAC MSUM_FNORM_LE THEN REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = 0` THENL 
    [ASM_SIMP_TAC [FACT; real_pow; matrix_pow] THEN 
     SIMP_TAC [REAL_DIV_1; MATRIX_CMUL_LID; REAL_MUL_LID;
     FNORM_MAT; REAL_LE_REFL];
     ALL_TAC] THEN STRIP_TAC THEN 
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN 
    SIMP_TAC [REAL_LE_01; REAL_LE_MUL; REAL_ABS_POS; FNORM_POS_LE] THEN
    CONJ_TAC THENL 
    [ALL_TAC; 
     MESON_TAC [SQRT_1; SQRT_MONO_LE; DIMINDEX_GE_1;REAL_OF_NUM_LE]] THEN 
    SIMP_TAC [FNORM_MUL] THEN 
    SUBGOAL_THEN `abs (&1 / &(FACT i)) = &1 / &(FACT i)` SUBST1_TAC THENL  
    [SIMP_TAC[REAL_ABS_REFL; REAL_LT_IMP_LE;REAL_LT_DIV;
                 REAL_OF_NUM_LT;REAL_LT_MUL; LE_1;
                 FACT_LT; REAL_POW_LT;REAL_LT_01]; ALL_TAC] THEN 
    MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC[REAL_LT_IMP_LE;REAL_LT_DIV;
             REAL_OF_NUM_LT;REAL_LT_MUL; LE_1;
             FACT_LT; REAL_LT_01] THEN 
    MP_TAC (SPECL [`z:real^N^N`; `i:num`] FNORM_MATRIX_POW_LE) THEN 
    ASM_SIMP_TAC [ARITH_RULE `!n. ~(n = 0) ==> 1 <= n`] THEN 
    MATCH_MP_TAC (REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN 
    ASM_SIMP_TAC[REAL_POW_LE2; FNORM_POS_LE]);;
    
let MATRIX_EXP_CONVERGES_UNIFORMLY_CAUCHY_LMUL = prove
 (`!R e. &0 < e /\ &0 < R
         ==> ?N. !m n z:real^N^N. m >= N /\ fnorm(z) <= R
    ==> fnorm(z ** msum(m..n) (\i. (&1 / &(FACT i)) %% (z matrix_pow i)))
                                     < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&1 / &2`; `(\i. (R %% mat 1:real^N^N) ** ((&1 / &(FACT i)) %% (R %% mat 1:real^N^N) matrix_pow i))`; `from 0`] MSERIES_RATIO) THEN
  REWRITE_TAC[MSERIES_CAUCHY; LEFT_FORALL_IMP_THM] THEN
  MP_TAC(SPEC `&2 * abs (R) :real` REAL_ARCH_SIMPLE) THEN
  SIMP_TAC [MATRIX_POW_CMUL; MATRIX_POW_ONE] THEN 
  SIMP_TAC [MATRIX_MUL_RMUL; MATRIX_MUL_RID] THEN 
  REWRITE_TAC[FNORM_MUL; FNORM_MAT; REAL_MUL_LID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (c ==> d) ==> a ==> (b ==> c) ==> d`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN
    SIMP_TAC[FACT; real_pow; GSYM REAL_OF_NUM_MUL; real_div; REAL_INV_MUL] THEN
    SIMP_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN 
    SIMP_TAC [REAL_OF_NUM_LE; DIMINDEX_GE_1; SQRT_POS_LE; 
              ARITH_RULE `1 <= n ==> 0 <= n`; REAL_MUL_LID; REAL_MUL_RID;REAL_ABS_MUL;REAL_ABS_POS] THEN 
    MATCH_MP_TAC REAL_LE_RMUL THEN 
    SIMP_TAC [REAL_OF_NUM_LE; DIMINDEX_GE_1; SQRT_POS_LE; 
              ARITH_RULE `1 <= n ==> 0 <= n`; REAL_MUL_LID; REAL_MUL_RID;REAL_ABS_MUL;REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ARITH
     `(is * ik) * (z * zn) <= ((inv(&2)) * ik) * zn <=>
      &0 <= (&1 - (&2 * z) * is) * zn * ik`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_POW_LE; REAL_SUB_LE;
             REAL_LE_INV_EQ; REAL_ABS_POS] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LT_0] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_SUC] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN 
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    REWRITE_TAC[FROM_0; INTER_UNIV] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC [] THEN 
    MATCH_MP_TAC (REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN 
    REWRITE_TAC [MATRIX_CMUL_ASSOC; GSYM MSUM_MMUL;FNORM_MUL;
                 FNORM_MAT; REAL_MUL_LID] THEN 
    SUBGOAL_THEN `abs (sum (m..n) (\i. (&1 / &(FACT i) * R pow i) * R)) =
                  sum (m..n) (\i. (&1 / &(FACT i) * R pow i) * R)`
      SUBST1_TAC THENL  
      [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
       ASM_SIMP_TAC[REAL_LT_IMP_LE;REAL_LT_DIV; REAL_OF_NUM_LT;REAL_LT_MUL; LE_1;
                   FACT_LT; REAL_POW_LT;REAL_LT_01] THEN 
       REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
       ASM_SIMP_TAC[REAL_LT_IMP_LE;REAL_LT_DIV; REAL_OF_NUM_LT;REAL_LT_MUL; LE_1;
                   FACT_LT; REAL_POW_LT;REAL_LT_01];
       ALL_TAC] THEN  
    W(MP_TAC o PART_MATCH lhand FNORM_SUBMULT o lhand o snd) THEN
    MATCH_MP_TAC (REAL_ARITH `!c:real. b <= c ==> a <= b ==> a <= c`) THEN
    ONCE_REWRITE_TAC [SUM_RMUL] THEN REWRITE_TAC [GSYM REAL_MUL_ASSOC] THEN 
    REWRITE_TAC [REAL_ARITH 
    `!e:real. a * b <= c * d * e <=> b * a <= (c * e) * d`] THEN 
    MATCH_MP_TAC REAL_LE_MUL2 THEN 
    ASM_SIMP_TAC [FNORM_POS_LE] THEN 
    SIMP_TAC [GSYM SUM_RMUL] THEN 
    MATCH_MP_TAC MSUM_FNORM_LE THEN REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = 0` THENL 
    [ASM_SIMP_TAC [FACT; real_pow; matrix_pow] THEN 
     SIMP_TAC [REAL_DIV_1; MATRIX_CMUL_LID; REAL_MUL_LID;
     FNORM_MAT; REAL_LE_REFL];
     ALL_TAC] THEN STRIP_TAC THEN 
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN 
    SIMP_TAC [REAL_LE_01; REAL_LE_MUL; REAL_ABS_POS; FNORM_POS_LE] THEN
    CONJ_TAC THENL 
    [ALL_TAC; 
     MESON_TAC [SQRT_1; SQRT_MONO_LE; DIMINDEX_GE_1;REAL_OF_NUM_LE]] THEN 
    SIMP_TAC [FNORM_MUL] THEN 
    SUBGOAL_THEN `abs (&1 / &(FACT i)) = &1 / &(FACT i)` SUBST1_TAC THENL  
    [SIMP_TAC[REAL_ABS_REFL; REAL_LT_IMP_LE;REAL_LT_DIV;
                 REAL_OF_NUM_LT;REAL_LT_MUL; LE_1;
                 FACT_LT; REAL_POW_LT;REAL_LT_01]; ALL_TAC] THEN 
    MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC[REAL_LT_IMP_LE;REAL_LT_DIV;
             REAL_OF_NUM_LT;REAL_LT_MUL; LE_1;
             FACT_LT; REAL_LT_01] THEN 
    MP_TAC (SPECL [`z:real^N^N`; `i:num`] FNORM_MATRIX_POW_LE) THEN 
    ASM_SIMP_TAC [ARITH_RULE `!n. ~(n = 0) ==> 1 <= n`] THEN 
    MATCH_MP_TAC (REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN 
    ASM_SIMP_TAC[REAL_POW_LE2; FNORM_POS_LE]);;
    
let MATRIX_EXP_CONVERGES_UNIFORMLY_CAUCHY_LMUL1 = prove
 (`!R e A:real^N^N. &0 < e /\ &0 < R
         ==> ?N. !m n z:real^1^1. m >= N /\ fnorm(z) <= R
    ==> fnorm(A ** msum(m..n) (\i. (&1 / &(FACT i)) %% ((drop_drop z %% A) matrix_pow i))) < e`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `A = mat 0:real^N^N` THENL
  [ASM_SIMP_TAC [MATRIX_MUL_LZERO; FNORM_MAT;REAL_MUL_LZERO];ALL_TAC] THEN
  MP_TAC(ISPECL [`&1 / &2`; `(\i. (mat 1:real^N^N) ** ((&1 / &(FACT i)) %%
  ((R * fnorm(A:real^N^N)) %% mat 1:real^N^N) matrix_pow i))`; `from 0`] MSERIES_RATIO) THEN
  REWRITE_TAC[MSERIES_CAUCHY; LEFT_FORALL_IMP_THM] THEN
  MP_TAC(SPEC `&2 * abs (R) * fnorm (A:real^N^N) :real` REAL_ARCH_SIMPLE) THEN
  SIMP_TAC [MATRIX_POW_CMUL; MATRIX_POW_ONE] THEN
  SIMP_TAC [MATRIX_MUL_RMUL; MATRIX_MUL_RID] THEN
  REWRITE_TAC[FNORM_MUL; FNORM_MAT; REAL_MUL_LID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (c ==> d) ==> a ==> (b ==> c) ==> d`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN
    SIMP_TAC[FACT; real_pow; GSYM REAL_OF_NUM_MUL; real_div; REAL_INV_MUL] THEN
    SIMP_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC [REAL_OF_NUM_LE; DIMINDEX_GE_1; SQRT_POS_LE;
              ARITH_RULE `1 <= n ==> 0 <= n`; REAL_MUL_LID; REAL_MUL_RID;REAL_ABS_MUL;REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ARITH
     `(is * ik) * (z * zn) <= ((inv(&2)) * ik) * zn <=>
      &0 <= (&1 - (&2 * z) * is) * zn * ik`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_POW_LE; REAL_SUB_LE;
             REAL_LE_INV_EQ; REAL_ABS_POS] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ;
                 REAL_OF_NUM_LT; LT_0;
                 MESON [REAL_ABS_REFL] `!x:real. &0 <= x ==> abs x = x`;
                 FNORM_POS_LE] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_SUC] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e / fnorm(A:real^N^N):real`) THEN
    FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE [GSYM FNORM_POS_LT]) THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    REWRITE_TAC[FROM_0; INTER_UNIV] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC [] THEN
    UNDISCH_TAC `&0 < fnorm (A:real^N^N)` THEN SIMP_TAC [IMP_IMP] THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN
    DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_RMUL) THEN
    UNDISCH_TAC `~(A = mat 0:real^N^N)` THEN
    DISCH_THEN (ASSUME_TAC o REWRITE_RULE [GSYM FNORM_POS_LT]) THEN
    ASM_SIMP_TAC [REAL_FIELD `&0 < b ==> a / b * b = a`] THEN
    MATCH_MP_TAC (REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
    W(MP_TAC o PART_MATCH lhand FNORM_SUBMULT o lhand o snd) THEN
    MATCH_MP_TAC (REAL_ARITH `!c:real. b <= c ==> a <= b ==> a <= c`) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC [FNORM_POS_LE] THEN
    REWRITE_TAC [MATRIX_CMUL_ASSOC; GSYM MSUM_MMUL;FNORM_MUL;
                 FNORM_MAT; REAL_MUL_LID; MATRIX_MUL_LID] THEN
    SUBGOAL_THEN `abs (sum (m..n) (\i. &1 / &(FACT i) * (R * fnorm (A:real^N^N)) pow i)) = sum (m..n) (\i. &1 / &(FACT i) * (R * fnorm A) pow i)`
      SUBST1_TAC THENL 
      [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
       ASM_SIMP_TAC[REAL_LT_IMP_LE;REAL_LT_DIV; REAL_OF_NUM_LT;REAL_LT_MUL; LE_1;
                   FACT_LT; REAL_POW_LT;REAL_LT_01] THEN
       REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
       ASM_SIMP_TAC[REAL_LT_IMP_LE;REAL_LT_DIV; REAL_OF_NUM_LT;REAL_LT_MUL; LE_1;
                   FACT_LT; REAL_POW_LT;REAL_LT_01; REAL_LE_MUL];
       ALL_TAC] THEN 
    SIMP_TAC [GSYM SUM_RMUL] THEN
     MATCH_MP_TAC MSUM_FNORM_LE THEN REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = 0` THENL
    [ASM_SIMP_TAC [FACT; real_pow; matrix_pow] THEN
     SIMP_TAC [REAL_DIV_1; MATRIX_CMUL_LID; REAL_MUL_LID;
     FNORM_MAT; REAL_LE_REFL];
     ALL_TAC] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC [REAL_LE_01; REAL_LE_MUL; REAL_ABS_POS; FNORM_POS_LE] THEN
    CONJ_TAC THENL
    [ALL_TAC;
     MESON_TAC [SQRT_1; SQRT_MONO_LE; DIMINDEX_GE_1;REAL_OF_NUM_LE]] THEN
    SIMP_TAC [GSYM MATRIX_CMUL_ASSOC] THEN
    ONCE_REWRITE_TAC [FNORM_MUL] THEN
    SUBGOAL_THEN `abs (&1 / &(FACT i)) = &1 / &(FACT i)` SUBST1_TAC THENL 
    [SIMP_TAC[REAL_ABS_REFL; REAL_LT_IMP_LE;REAL_LT_DIV;
                 REAL_OF_NUM_LT;REAL_LT_MUL; LE_1;
                 FACT_LT; REAL_POW_LT;REAL_LT_01]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC[REAL_LT_IMP_LE;REAL_LT_DIV;
             REAL_OF_NUM_LT;REAL_LT_MUL; LE_1;
             FACT_LT; REAL_LT_01] THEN
    SIMP_TAC [drop_drop; FNORM_MUL; REAL_ABS_POW;
              GSYM FNORM_REAL; REAL_POW_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC [REAL_POW_LE; FNORM_POS_LE] THEN
    ASM_SIMP_TAC[REAL_POW_LE2; FNORM_POS_LE] THEN
    MP_TAC (SPECL [`A:real^N^N`; `i:num`] FNORM_MATRIX_POW_LE) THEN
    ASM_SIMP_TAC [ARITH_RULE `!n. ~(n = 0) ==> 1 <= n`]);;
    
let MSUM_ADD_SPLIT = prove
 (`!f m n p.
       m <= n + 1 ==> msum(m..n + p) f = msum(m..n) f + msum(n + 1..n + p) f`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; MSUM_COMPONENT; MATRIX_ADD_COMPONENT;
           SUM_ADD_SPLIT]);;

let MATRIX_EXP_CONVERGES_UNIFORMLY = prove
 (`!R e. &0 < R /\ &0 < e
         ==> ?N. !n z:real^N^N. n >= N /\ fnorm(z) < R
                       ==> fnorm(msum(0..n) (\i. (&1 / &(FACT i)) %% (z matrix_pow i)) -
                                matrix_exp(z)) <= e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`R:real`; `e / &2`] MATRIX_EXP_CONVERGES_UNIFORMLY_CAUCHY) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^N^N`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `z:real^N^N` MATRIX_EXP_CONVERGES) THEN
  REWRITE_TAC[msums; MATRIX_LIM_SEQUENTIALLY; FROM_0; INTER_UNIV; matrix_dist] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `n + M + 1`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n + 1`; `n + M + 1`; `z:real^N^N`]) THEN
  ASM_SIMP_TAC[ARITH_RULE `(n >= N ==> n + 1 >= N) /\ M <= n + M + 1`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; MSUM_ADD_SPLIT; LE_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV(ALPHA_CONV `i:num`)) THEN 
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM FNORM_NEG] THEN
  MATCH_MP_TAC (REAL_ARITH `c <= a + b ==> a < e / &2 ==> b < e / &2 ==> c <= e`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN 
  EXISTS_TAC ` fnorm (--msum (n + 1..n + M + 1) (\i:num. &1 / &(FACT i) %% (z:real^N^N) matrix_pow i) + (msum (0..n) (\i. &1 / &(FACT i) %% z matrix_pow i) +
   msum (n + 1..n + M + 1) (\i. &1 / &(FACT i) %% z matrix_pow i)) - matrix_exp z)` THEN CONJ_TAC THENL
  [SIMP_TAC[CMATRIX_ARITH `!A B C:real^N^N.(--B) + (A + B) - C = A - C`] THEN
  REAL_ARITH_TAC ;ALL_TAC] THEN SIMP_TAC[GSYM FNORM_TRIANGLE]);;
  
let MATRIX_EXP_CONVERGES_UNIFORMLY_LMUL = prove
 (`!R e. &0 < R /\ &0 < e
         ==> ?N. !n z: real^N^N. n >= N /\ fnorm(z) < R
                       ==> fnorm(z ** msum(0..n) (\i. (&1 / &(FACT i)) %% (z matrix_pow i)) - z ** matrix_exp(z)) <= e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`R:real`; `e / &2`] MATRIX_EXP_CONVERGES_UNIFORMLY_CAUCHY_LMUL) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^N^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `z:real^N^N` (MATCH_MP MSERIES_LMUL (SPEC `z:real^N^N` MATRIX_EXP_CONVERGES))) THEN
  REWRITE_TAC[msums; MATRIX_LIM_SEQUENTIALLY; FROM_0; INTER_UNIV; matrix_dist] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `n + M + 1`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n + 1`; `n + M + 1`; `z:real^N^N`]) THEN
  ASM_SIMP_TAC[ARITH_RULE `(n >= N ==> n + 1 >= N) /\ M <= n + M + 1`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; MSUM_ADD_SPLIT; LE_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV(ALPHA_CONV `i:num`)) THEN 
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM FNORM_NEG] THEN
  MATCH_MP_TAC (REAL_ARITH `c <= a + b ==> a < e / &2 ==> b < e / &2 ==> c <= e`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN 
  EXISTS_TAC ` fnorm (--(z ** msum (n + 1..n + M + 1) (\i:num. &1 / &(FACT i) %% (z:real^N^N) matrix_pow i)) + 
  (msum (0..n) (\i. z ** &1 / &(FACT i) %% z matrix_pow i) +
    msum (n + 1..n + M + 1) (\i. z ** &1 / &(FACT i) %% z matrix_pow i)) - 
    z ** matrix_exp z)` THEN CONJ_TAC THEN
    SIMP_TAC[FINITE_NUMSEG;GSYM MSUM_MATRIX_LMUL] THENL
  [SIMP_TAC[CMATRIX_ARITH `!A B C:real^N^N.(--B) + (A + B) - C = A - C`] THEN
  REAL_ARITH_TAC ;SIMP_TAC[GSYM FNORM_TRIANGLE]]);;
  
let MATRIX_EXP_CONVERGES_UNIFORMLY_LMUL1 = prove
 (`!R e A:real^N^N. &0 < R /\ &0 < e
         ==> ?N. !n z:real^1^1. n >= N /\ fnorm(z) < R
                       ==> fnorm ( A ** msum(0..n) (\i. (&1 / &(FACT i)) %% (drop_drop z %% A) matrix_pow i) -  A ** matrix_exp((drop_drop z %% A))) <= e`,
  REPEAT STRIP_TAC THEN 
  MP_TAC(SPECL [`R :real`; `e / &2`] MATRIX_EXP_CONVERGES_UNIFORMLY_CAUCHY_LMUL1) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN 
  DISCH_THEN(MP_TAC o SPEC `A:real^N^N`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^1^1`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `A:real^N^N` (MATCH_MP MSERIES_LMUL 
  (SPEC `drop_drop (z: real^1^1) %% (A:real^N^N)` MATRIX_EXP_CONVERGES))) THEN
  REWRITE_TAC[msums; MATRIX_LIM_SEQUENTIALLY; FROM_0; INTER_UNIV; matrix_dist] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `n + M + 1`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n + 1`; `n + M + 1`; ` z:real^1^1`]) THEN
  ASM_SIMP_TAC[ARITH_RULE `(n >= N ==> n + 1 >= N) /\ M <= n + M + 1`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; MSUM_ADD_SPLIT; LE_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV(ALPHA_CONV `i:num`)) THEN 
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM FNORM_NEG] THEN
  MATCH_MP_TAC (REAL_ARITH `c <= a + b ==> a < e / &2 ==> b < e / &2 ==> c <= e`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN 
  EXISTS_TAC ` fnorm (--((A:real^N^N) ** msum (n + 1..n + M + 1) (\i:num. &1 / &(FACT i) %% (drop_drop (z:real^1^1) %% A) matrix_pow i)) + 
  (msum (0..n) (\i. A ** &1 / &(FACT i) %% (drop_drop z %% A) matrix_pow i) +
    msum (n + 1..n + M + 1) (\i. A ** &1 / &(FACT i) %% (drop_drop z %% A) matrix_pow i)) - 
    A ** matrix_exp (drop_drop z %% A))` THEN CONJ_TAC THEN
    SIMP_TAC[FINITE_NUMSEG;GSYM MSUM_MATRIX_LMUL] THENL
  [SIMP_TAC[CMATRIX_ARITH `!A B C:real^N^N.(--B) + (A + B) - C = A - C`] THEN
  REAL_ARITH_TAC ;SIMP_TAC[GSYM FNORM_TRIANGLE]]);;

parse_as_infix ("matrix_convex_on",(12,"right"));;

let matrix_convex_on = new_definition
  `f matrix_convex_on s <=>
        !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
                  ==> f(u %% x + v %% y) <= u * f(x) + v * f(y)`;;
  
let MATRIX_CONVEX_DISTANCE = prove
 (`!s a. (\x. matrix_dist(a,x)) matrix_convex_on s`,
  REWRITE_TAC[matrix_convex_on; matrix_dist] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
   [GSYM MATRIX_CMUL_LID] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[CMATRIX_ARITH
   `(u + v) %% z - (u %% x + v %% y):real^N^M = u %% (z - x) + v %% (z - y)`] THEN
  ASM_MESON_TAC[FNORM_TRIANGLE; FNORM_MUL; REAL_ABS_REFL]);;  
  
let MATRIX_CONVEX_BALL = prove
 (`!x:real^N^M e. matrix_convex(matrix_ball(x,e))`,
  let lemma = REWRITE_RULE[matrix_convex_on; IN_UNIV]
   (ISPEC `(:real^N^M)` MATRIX_CONVEX_DISTANCE) in
  REWRITE_TAC[matrix_convex; IN_MATRIX_BALL] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) lemma o lhand o snd) THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_CONVEX_BOUND_LT]);; 
 
let HAS_M_DERIVATIVE_POW_WITHIN = prove
 (`!t:real^1^1 A:real^N^N s n. 
       ((\t. (drop_drop t %% A) matrix_pow n) has_m_derivative 
           ((&n * (drop_drop t) pow (n-1)) %% (A matrix_pow n))) (matrix_at t within s)`,        
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THENL 
  [SIMP_TAC[matrix_pow;HAS_M_DERIVATIVE_CONST;
           REAL_ARITH `&0 * a = &0`;MATRIX_CMUL_LZERO]; ALL_TAC] THEN
  MP_TAC (ISPECL [`matrix_at (t:real^1^1) within (s:real^1^1->bool)`;`A:real^N^N`] HAS_M_DERIVATIVE_DROP2_CMUL) THEN
  STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL 
  [ASM_SIMP_TAC[matrix_pow;real_pow;ARITH_RULE `(SUC 0) = 1`; ARITH_RULE `1 - 1 = 0`;
               REAL_MUL_LID;MATRIX_MUL_RID;
               MATRIX_CMUL_LID;HAS_M_DERIVATIVE_DROP2_CMUL]; ALL_TAC] THEN
  ASM_SIMP_TAC [ARITH_RULE `~(n = 0) ==> SUC n - 1 = SUC (n - 1)`] THEN
  SIMP_TAC[matrix_pow;real_pow;ARITH_RULE `SUC n = n + 1`] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_RDISTRIB;
           MATRIX_CMUL_ADD_RDISTRIB; REAL_MUL_LID] THEN 
  SIMP_TAC[GSYM MATRIX_MUL_RMUL] THEN 
  SIMP_TAC[CMATRIX_ARITH `A ** (&n * x * y) %% B:real^N^M = (x %% A) ** ((&n * y) %% B)`] THEN
  SIMP_TAC[REAL_FIELD `!a:real. a * a pow (n - 1) = a pow 1 * a pow (n - 1)`] THEN
  SIMP_TAC[GSYM REAL_POW_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> 1 + n - 1 = n`] THEN
  SIMP_TAC[GSYM MATRIX_POW_CMUL] THEN MATCH_MP_TAC HAS_M_DERIVATIVE_MUL_WITHIN THEN
  ASM_SIMP_TAC[]);;

let HAS_M_DERIVATIVE_POW_AT = prove
 (`!t:real^1^1 A:real^N^N n. 
       ((\t. (drop_drop t %% A) matrix_pow n) has_m_derivative 
           ((&n * (drop_drop t) pow (n-1)) %% (A matrix_pow n))) (matrix_at t)`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  REWRITE_TAC[HAS_M_DERIVATIVE_POW_WITHIN]);;

(**********************************)

let HAS_M_DERIVATIVE_EXP_CMUL_MAT = prove
 (`!z:real^1^1. ((\x. matrix_exp (drop_drop x %% (mat 1:real^N^N))) has_m_derivative (matrix_exp (drop_drop z %% (mat 1:real^N^N)))) (matrix_at z)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL
   [`matrix_ball(mat 0:real^1^1,fnorm(z:real^1^1) + &1)`;
    `\n z:real^1^1. (&1 / &(FACT n)) %% ((drop_drop z %% mat 1:real^N^N) matrix_pow n)`;
    `\n z:real^1^1. if n = 0 then (mat 0:real^N^N)
                    else (&1 / &(FACT (n - 1))) 
                    %% ((drop_drop z %% mat 1:real^N^N) matrix_pow (n - 1))`;
    `\z:real^1^1. matrix_exp (drop_drop z %% (mat 1:real^N^N))`;
    `(from 0)`]
   HAS_M_DERIVATIVE_SERIES) THEN
  REWRITE_TAC[MATRIX_CONVEX_BALL; MATRIX_OPEN_BALL; IN_MATRIX_BALL; matrix_dist] THEN
  SIMP_TAC[HAS_M_DERIVATIVE_WITHIN_OPEN; MATRIX_OPEN_BALL; IN_MATRIX_BALL;
           matrix_dist; MATRIX_SUB_LZERO; MATRIX_SUB_RZERO; FNORM_NEG] THEN
  ANTS_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC;ALL_TAC;ALL_TAC;ALL_TAC] THENL 
    [ASM_SIMP_TAC[matrix_pow;HAS_M_DERIVATIVE_CONST];
     ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC] THENL
     [SUBGOAL_THEN `&1 / &(FACT (n - 1)) = &1 / &(FACT n) * &n` SUBST1_TAC ;
      ALL_TAC;ALL_TAC;ALL_TAC] THENL 
        [FIRST_ASSUM 
         (SUBST1_TAC o MATCH_MP (ARITH_RULE `~(n = 0) ==> n = SUC (n-1) `)) THEN 
         SIMP_TAC [FACT; SUC_SUB1; real_div ] THEN 
         SIMP_TAC [GSYM REAL_OF_NUM_MUL; REAL_INV_MUL] THEN 
         REWRITE_TAC [REAL_ARITH `!d:real. (a * b * c)* d = a * c * b * d`] THEN 
         FIRST_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM REAL_OF_NUM_EQ] o
                    MATCH_MP (ARITH_RULE `~(n = 0) ==> ~(SUC (n -1) = 0)`)) THEN 
         SIMP_TAC [REAL_FIELD `!x:real. ~(x = &0) <=> inv x * x = &1`] THEN
         REAL_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THENL
         [SIMP_TAC[GSYM MATRIX_CMUL_ASSOC] THEN
          MATCH_MP_TAC HAS_M_DERIVATIVE_CMUL THEN
          SIMP_TAC[MATRIX_POW_CMUL] THEN
          SIMP_TAC[MESON [MATRIX_POW_ONE] `(mat 1:real^N^N) matrix_pow (n - 1) = mat 1 matrix_pow n`] THEN
          SIMP_TAC[GSYM MATRIX_POW_CMUL] THEN
          SIMP_TAC[SIMP_RULE [GSYM MATRIX_CMUL_ASSOC] HAS_M_DERIVATIVE_POW_AT];
          ALL_TAC;ALL_TAC;ALL_TAC] THENL
          [REPEAT STRIP_TAC THEN
           MP_TAC(SPECL [`(fnorm(z:real^1^1) + &1) * (sqrt (&(dimindex(:N))))`; `e:real`]
           MATRIX_EXP_CONVERGES_UNIFORMLY) THEN
           ASM_SIMP_TAC[FNORM_POS_LE; REAL_ARITH `&0 <= x ==> &0 < x + &1`;
                    REAL_LT_MUL; 
                    SIMP_RULE [GSYM REAL_OF_NUM_LE] DIMINDEX_GE_1;  
                    REAL_ARITH `&1 <= x ==> &0 < x`; SQRT_POS_LT] THEN
        DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N + 1` THEN
        MAP_EVERY X_GEN_TAC [`n:num`; `w:real^1^1`] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(
            MP_TAC o SPECL [`n - 1`; `drop_drop w %% mat 1:real^N^N`]) THEN
        ASM_SIMP_TAC[ARITH_RULE `n >= m + 1 ==> n - 1 >= m`] THEN 
        ASM_SIMP_TAC [FNORM_MUL; FNORM_MAT; drop_drop; 
                        GSYM FNORM_REAL; REAL_MUL_LID] THEN 
        ASM_SIMP_TAC [REAL_LT_RMUL;
                        SIMP_RULE [GSYM REAL_OF_NUM_LE] DIMINDEX_GE_1;  
                        REAL_ARITH `&1 <= x ==> &0 < x`; SQRT_POS_LT] THEN 
        REWRITE_TAC[FROM_0; INTER_UNIV] THEN MATCH_MP_TAC EQ_IMP THEN 
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
       SUBGOAL_THEN `0..n = 0 INSERT (IMAGE SUC (0..n-1))` SUBST1_TAC ;
       ALL_TAC;ALL_TAC] THENL
       [REWRITE_TAC[EXTENSION; IN_INSERT; IN_IMAGE; IN_NUMSEG] THEN
        INDUCT_TAC THEN REWRITE_TAC[LE_0; NOT_SUC; SUC_INJ; UNWIND_THM1] THEN
        UNDISCH_TAC `n >= N + 1` THEN ARITH_TAC;
        ALL_TAC;ALL_TAC;ALL_TAC] THENL 
        [SIMP_TAC[MSUM_CLAUSES; FINITE_IMAGE; FINITE_NUMSEG] THEN 
         REWRITE_TAC[IN_IMAGE; NOT_SUC; MATRIX_ADD_LID] THEN 
         SIMP_TAC[MSUM_IMAGE; FINITE_NUMSEG; SUC_INJ] THEN 
         MATCH_MP_TAC MSUM_EQ THEN 
         SIMP_TAC[IN_NUMSEG; NOT_SUC; o_THM; SUC_SUB1];
         ALL_TAC;ALL_TAC] THENL
        [MAP_EVERY EXISTS_TAC [`mat 0:real^1^1`; 
                                `matrix_exp(mat 0:real^N^N)`] THEN 
        SIMP_TAC[MATRIX_EXP_CONVERGES;FNORM_0;DROP2_MAT; 
                    MATRIX_CMUL_LZERO] THEN 
        SIMP_TAC[REAL_ARITH `&0 <= z ==> &0 < z + &1`; FNORM_POS_LE];
        ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `g:real^1^1->real^N^N` MP_TAC) THEN 
        REWRITE_TAC[MATRIX_EXP_CONVERGES_UNIQUE] THEN STRIP_TAC THEN
        MATCH_MP_TAC HAS_M_DERIVATIVE_TRANSFORM_AT THEN
        MAP_EVERY EXISTS_TAC [`g:real^1^1->real^N^N`; `&1`] THEN
        REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
        [ALL_TAC;
            FIRST_X_ASSUM(MP_TAC o SPEC `z:real^1^1`) THEN
            ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]]] THEN 
        POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
        X_GEN_TAC `w:real^1^1` THEN MATCH_MP_TAC MONO_IMP THEN SIMP_TAC[] THEN
        SIMP_TAC [matrix_dist; FNORM_EQ_NORM_VECTORIZE; VECTORIZE_SUB] THEN 
        NORM_ARITH_TAC );;
    
let HAS_M_DERIVATIVE_EXP = prove
 (`!A:real^N^N z:real^1^1. ((\z. matrix_exp (drop_drop z %% A)) has_m_derivative (A ** matrix_exp(drop_drop z %% A))) (matrix_at z)`, 
    REPEAT GEN_TAC THEN ASM_CASES_TAC `A = mat 0:real^N^N` THENL 
    [ASM_SIMP_TAC [MATRIX_CMUL_RZERO; MATRIX_MUL_LZERO; 
                  MATRIX_EXP_0; HAS_M_DERIVATIVE_CONST]; ALL_TAC] THEN
    MP_TAC(ISPECL
   [`matrix_ball(mat 0:real^1^1,fnorm(z:real^1^1) + &1)`;
    `\n z:real^1^1. (&1 / &(FACT n)) %% ((drop_drop z %% A:real^N^N) matrix_pow n)`;
    `\n z:real^1^1. if n = 0 then (mat 0:real^N^N)
                    else (&1 / &(FACT (n - 1))) 
                    %% (A ** (drop_drop z %% A:real^N^N) matrix_pow (n - 1))`;
    `\z:real^1^1. A ** matrix_exp (drop_drop z %% (A:real^N^N))`;
    `(from 0)`]
   HAS_M_DERIVATIVE_SERIES) THEN
  REWRITE_TAC[MATRIX_CONVEX_BALL; MATRIX_OPEN_BALL; IN_MATRIX_BALL; matrix_dist] THEN
  SIMP_TAC[HAS_M_DERIVATIVE_WITHIN_OPEN; MATRIX_OPEN_BALL; IN_MATRIX_BALL;
           matrix_dist; MATRIX_SUB_LZERO; MATRIX_SUB_RZERO; FNORM_NEG] THEN
  ANTS_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC;ALL_TAC;ALL_TAC;ALL_TAC] THENL 
    [ASM_SIMP_TAC[matrix_pow;HAS_M_DERIVATIVE_CONST];
     ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC] THENL
     [SUBGOAL_THEN `&1 / &(FACT (n - 1)) = &1 / &(FACT n) * &n` SUBST1_TAC ;
      ALL_TAC;ALL_TAC;ALL_TAC] THENL 
        [FIRST_ASSUM 
         (SUBST1_TAC o MATCH_MP (ARITH_RULE `~(n = 0) ==> n = SUC (n-1) `)) THEN 
         SIMP_TAC [FACT; SUC_SUB1; real_div ] THEN 
         SIMP_TAC [GSYM REAL_OF_NUM_MUL; REAL_INV_MUL] THEN 
         REWRITE_TAC [REAL_ARITH `!d:real. (a * b * c)* d = a * c * b * d`] THEN 
         FIRST_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM REAL_OF_NUM_EQ] o
                    MATCH_MP (ARITH_RULE `~(n = 0) ==> ~(SUC (n -1) = 0)`)) THEN 
         SIMP_TAC [REAL_FIELD `!x:real. ~(x = &0) <=> inv x * x = &1`] THEN
         REAL_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THENL
         [SIMP_TAC[GSYM MATRIX_CMUL_ASSOC] THEN
          MATCH_MP_TAC HAS_M_DERIVATIVE_CMUL THEN
          SIMP_TAC[MATRIX_POW_CMUL] THEN
          SIMP_TAC [MATRIX_MUL_RMUL] THEN 
          ASM_SIMP_TAC[GSYM matrix_pow;
                       ARITH_RULE `~(n = 0) ==> SUC (n-1) = n `] THEN
          SIMP_TAC[GSYM MATRIX_POW_CMUL] THEN
          SIMP_TAC[SIMP_RULE [GSYM MATRIX_CMUL_ASSOC] HAS_M_DERIVATIVE_POW_AT];
          ALL_TAC;ALL_TAC;ALL_TAC] THENL
          [REPEAT STRIP_TAC THEN
           MP_TAC(SPECL [`(fnorm(z:real^1^1) + &1)`; `e:real`]
           MATRIX_EXP_CONVERGES_UNIFORMLY_LMUL1) THEN
           DISCH_THEN (MP_TAC o SPEC `A:real^N^N`) THEN
           UNDISCH_TAC `~(A = mat 0:real^N^N)` THEN 
           SIMP_TAC [GSYM FNORM_POS_LT] THEN 
           ASM_SIMP_TAC[FNORM_POS_LE; REAL_ARITH `&0 <= x ==> &0 < x + &1`;
                    REAL_LT_MUL; 
                    SIMP_RULE [GSYM REAL_OF_NUM_LE] DIMINDEX_GE_1;  
                    REAL_ARITH `&1 <= x ==> &0 < x`; SQRT_POS_LT;
                    GSYM FNORM_POS_LT] THEN STRIP_TAC THEN 
        DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N + 1` THEN
        MAP_EVERY X_GEN_TAC [`n:num`; `w:real^1^1`] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(
            MP_TAC o SPECL [`n - 1`; `w:real^1^1`]) THEN
        ASM_SIMP_TAC[ARITH_RULE `n >= m + 1 ==> n - 1 >= m`] THEN 
        ASM_SIMP_TAC [FNORM_MUL; FNORM_MAT; drop_drop; 
                        GSYM FNORM_REAL; REAL_MUL_LID] THEN
        ASM_SIMP_TAC [REAL_LT_RMUL] THEN 
        REWRITE_TAC[FROM_0; INTER_UNIV] THEN MATCH_MP_TAC EQ_IMP THEN 
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        SIMP_TAC [FINITE_NUMSEG; MSUM_MATRIX_LMUL] THEN 
        AP_THM_TAC THEN AP_TERM_TAC THEN
       SUBGOAL_THEN `0..n = 0 INSERT (IMAGE SUC (0..n-1))` SUBST1_TAC ;
       ALL_TAC;ALL_TAC] THENL
       [REWRITE_TAC[EXTENSION; IN_INSERT; IN_IMAGE; IN_NUMSEG] THEN
        INDUCT_TAC THEN REWRITE_TAC[LE_0; NOT_SUC; SUC_INJ; UNWIND_THM1] THEN
        UNDISCH_TAC `n >= N + 1` THEN ARITH_TAC;
        ALL_TAC;ALL_TAC;ALL_TAC] THENL 
        [SIMP_TAC[MSUM_CLAUSES; FINITE_IMAGE; FINITE_NUMSEG] THEN 
         REWRITE_TAC[IN_IMAGE; NOT_SUC; MATRIX_ADD_LID] THEN 
         SIMP_TAC[MSUM_IMAGE; FINITE_NUMSEG; SUC_INJ] THEN 
         MATCH_MP_TAC MSUM_EQ THEN 
         SIMP_TAC[IN_NUMSEG; NOT_SUC; o_THM; SUC_SUB1] THEN
         REPEAT STRIP_TAC THEN 
         SIMP_TAC [MATRIX_MUL_LMUL;MATRIX_MUL_RMUL];
         ALL_TAC;ALL_TAC] THENL
        [MAP_EVERY EXISTS_TAC [`mat 0:real^1^1`; 
                                `matrix_exp(mat 0:real^N^N)`] THEN 
        SIMP_TAC[MATRIX_EXP_CONVERGES;FNORM_0;DROP2_MAT; 
                    MATRIX_CMUL_LZERO] THEN 
        SIMP_TAC[REAL_ARITH `&0 <= z ==> &0 < z + &1`; FNORM_POS_LE];
        ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `g:real^1^1->real^N^N` MP_TAC) THEN 
        REWRITE_TAC[MATRIX_EXP_CONVERGES_UNIQUE] THEN STRIP_TAC THEN
        MATCH_MP_TAC HAS_M_DERIVATIVE_TRANSFORM_AT THEN
        MAP_EVERY EXISTS_TAC [`g:real^1^1->real^N^N`; `&1`] THEN
        REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
        [ALL_TAC;
            FIRST_X_ASSUM(MP_TAC o SPEC `z:real^1^1`) THEN
            ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]]] THEN 
        POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
        X_GEN_TAC `w:real^1^1` THEN MATCH_MP_TAC MONO_IMP THEN SIMP_TAC[] THEN
        SIMP_TAC [matrix_dist; FNORM_EQ_NORM_VECTORIZE; VECTORIZE_SUB] THEN 
        NORM_ARITH_TAC);;
        
let M_DIFFERENTIABLE_AT_MATRIX_EXP = prove
 (`!z:real^1^1 A:real^N^N. (\z. matrix_exp (drop_drop z %% A)) m_differentiable (matrix_at z)`,
  REWRITE_TAC[m_differentiable] THEN
  MESON_TAC[HAS_M_DERIVATIVE_EXP]);;

let M_DIFFERENTIABLE_WITHIN_MATRIX_EXP = prove
 (`!s z:real^1^1 A:real^N^N. (\z. matrix_exp (drop_drop z %% A)) m_differentiable (matrix_at z within s)`,
  MESON_TAC[M_DIFFERENTIABLE_AT_WITHIN;
            M_DIFFERENTIABLE_AT_MATRIX_EXP]);;
            
let CONTINUOUS_AT_MATRIX_EXP = prove
 (`!z:real^1^1 A:real^N^N. (\z. matrix_exp (drop_drop z %% A)) matrix_continuous (matrix_at z)`,
  MESON_TAC[HAS_M_DERIVATIVE_EXP;
            HAS_M_DERIVATIVE_IMP_CONTINUOUS_AT]);;

let CONTINUOUS_WITHIN_MATRIX_EXP = prove
 (`!s z:real^1^1 A:real^N^N. (\z. matrix_exp (drop_drop z %% A)) matrix_continuous (matrix_at z within s)`,
  MESON_TAC[MATRIX_CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_MATRIX_EXP]);;

let CONTINUOUS_ON_MATRIX_EXP = prove
 (`!s z:real^1^1 A:real^N^N. (\z. matrix_exp (drop_drop z %% A)) matrix_continuous_on s`,
  MESON_TAC[MATRIX_CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_MATRIX_EXP]);;
    
 (*   
let HAS_MATRIX_DERIVATIVE_EXP_ADD_LCONST = prove
(`!z b:real^N^N. ((\a. matrix_exp (b + a)) has_matrix_derivative (\a. matrix_exp (a))) (matrix_at z)`,
REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [GSYM o_DEF] THEN 
MATCH_MP_TAC (CONJUNCT2(REWRITE_RULE[FORALL_AND_THM]
   (MATCH_MP HAS_MATRIX_DERIVATIVE_CHAIN_UNIV
             HAS_MATRIX_DERIVATIVE_EXP))) THEN 
MP_TAC (ISPECL [`\a:real^N^N. a:real^N^N`; `\h:real^N^N. h:real^N^N`; `matrix_at z:(real^N^N)net`;`b:real^N^N`] HAS_MATRIX_DERIVATIVE_ADD_LCONST) THEN 
SIMP_TAC [HAS_MATRIX_DERIVATIVE_ID]);;

ket 

`!z b:real^N^N. ((\a. matrix_exp (--a)) has_matrix_derivative (\a. matrix_exp (--a))) (matrix_at z)`

ISPECL [`\B:real^N^N. matrix_exp (A + B)`;  `\B:real^N^N. matrix_exp (--B)`; `\B:real^N^N. matrix_exp B`; `\B:real^N^N. matrix_exp (--B)`; `x:real^N^N`] 
HAS_MATRIX_DERIVATIVE_MUL_AT


PART_MATCH HAS_MATRIX_DERIVATIVE_ADD_LCONST HAS_MATRIX_DERIVATIVE_ID
             
add_m_differentiation_theorems
 (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
   ()));;
*)

let MATRIX_EXP_INV_FUN = prove
(`!A:real^N^N t. matrix_exp (drop_drop t %% (--A)) ** matrix_exp (drop_drop t %% A) = mat 1`,
    let lem = prove
    (`!t A.matrix_exp (t %% --A) ** A = A ** matrix_exp (t %% --A)`,
    REPEAT GEN_TAC THEN MATCH_MP_TAC MATRIX_EXP_COMM_LEMMA THEN 
    CMATRIX_ARITH_TAC) in
    REPEAT STRIP_TAC THEN SPEC_TAC (`t:real^1^1`,`t:real^1^1`) THEN
    ONCE_REWRITE_TAC[SET_RULE `(!x. P x) <=> (!x. x IN UNIV ==> P x)`] THEN
    MATCH_MP_TAC HAS_M_DERIVATIVE_ZERO_UNIQUE THEN 
    EXISTS_TAC `mat 0:real^1^1` THEN 
    REWRITE_TAC[MATRIX_OPEN_UNIV; MATRIX_CONVEX_UNIV; IN_UNIV] THEN 
    REWRITE_TAC [DROP2_MAT; MATRIX_CMUL_LZERO; MATRIX_EXP_0;MATRIX_MUL_RID] THEN 
    GEN_TAC THEN 
    SUBGOAL_THEN 
    `mat 0:real^N^N = matrix_exp (drop_drop t %% --A) ** A ** matrix_exp (drop_drop t %% A) +
    (--A ** matrix_exp (drop_drop t %% --A)) **
          matrix_exp (drop_drop t %% A) ` SUBST1_TAC THENL
    [REWRITE_TAC [MATRIX_MUL_ASSOC] THEN ONCE_REWRITE_TAC [lem] THEN 
     REWRITE_TAC [MATRIX_MUL_LNEG; MATRIX_ADD_RNEG]; ALL_TAC] THEN 
    MATCH_MP_TAC HAS_M_DERIVATIVE_MUL_WITHIN THEN 
    SIMP_TAC [MATRIX_WITHIN_UNIV; HAS_M_DERIVATIVE_EXP]);;
    
let MATRIX_EXP_INV = prove
(`!A:real^N^N. matrix_inv (matrix_exp A) = matrix_exp (--A)`,
    let comm_lem = prove
    (`!A. matrix_exp  (--A) ** matrix_exp (A) = matrix_exp (A) ** matrix_exp  (--A)`,
    REPEAT GEN_TAC THEN MATCH_MP_TAC MATRIX_EXP_COMM_LEMMA THEN 
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN 
    MATCH_MP_TAC MATRIX_EXP_COMM_LEMMA THEN 
    CMATRIX_ARITH_TAC) in
    GEN_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN 
    MP_TAC (ISPECL [`A:real^N^N`; `mat 1:real^1^1`] MATRIX_EXP_INV_FUN) THEN 
    MP_TAC (ISPECL [`A:real^N^N`] comm_lem) THEN 
    SIMP_TAC [MATRIX_CMUL_LID; DROP2_MAT; MATRIX_MUL_RID; TRANSP_MAT;symmetric_matrix]);;
    
let MATRIX_EXP_ADD_MUL_FUN = prove
(`!A:real^N^N B t:real^1^1. A ** B = B ** A ==>
    matrix_exp (drop_drop t %% (A + B)) ** matrix_exp (drop_drop t %% (--A)) **
    matrix_exp (drop_drop t %% (--B))= mat 1`,
    let comm_lem1 = prove
    (`!A:real^N^N B:real^N^N. A ** B = B ** A ==>
    matrix_exp (drop_drop t %% --A) ** --B = --B ** matrix_exp (drop_drop t %% --A)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_EXP_COMM_LEMMA THEN 
    SIMP_TAC [MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN 
    AP_TERM_TAC THEN ASM_SIMP_TAC [MATRIX_MUL_LNEG; MATRIX_MUL_RNEG;
                                   MATRIX_NEG_NEG]) in
    let comm_lem2 = prove
    (`!A:real^N^N B:real^N^N. A ** B = B ** A ==>
    matrix_exp (drop_drop t %% --B) ** --A = --A ** matrix_exp (drop_drop t %% --B)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_EXP_COMM_LEMMA THEN 
    SIMP_TAC [MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN 
    AP_TERM_TAC THEN ASM_SIMP_TAC [MATRIX_MUL_LNEG; MATRIX_MUL_RNEG;
                                   MATRIX_NEG_NEG]) in
    let comm_lem3 = prove
    (`!A:real^N^N B:real^N^N. A ** B = B ** A ==>
    matrix_exp (drop_drop t %% (A+B)) ** --B = --B ** matrix_exp (drop_drop t %% (A + B))`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_EXP_COMM_LEMMA THEN 
    SIMP_TAC [MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN 
    AP_TERM_TAC THEN SIMP_TAC [MATRIX_MUL_LNEG; MATRIX_MUL_RNEG] THEN 
    AP_TERM_TAC THEN ASM_SIMP_TAC [MATRIX_ADD_RDISTRIB; MATRIX_ADD_LDISTRIB]) in 
    let comm_lem4 = prove
    (`!A:real^N^N B:real^N^N. A ** B = B ** A ==>
    matrix_exp (drop_drop t %% (A+B)) ** --A = --A ** matrix_exp (drop_drop t %% (A + B))`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_EXP_COMM_LEMMA THEN 
    SIMP_TAC [MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN 
    AP_TERM_TAC THEN SIMP_TAC [MATRIX_MUL_LNEG; MATRIX_MUL_RNEG] THEN 
    AP_TERM_TAC THEN ASM_SIMP_TAC [MATRIX_ADD_RDISTRIB; MATRIX_ADD_LDISTRIB]) in
    REPEAT STRIP_TAC THEN SPEC_TAC (`t:real^1^1`,`t:real^1^1`) THEN
    ONCE_REWRITE_TAC[SET_RULE `(!x. P x) <=> (!x. x IN UNIV ==> P x)`] THEN
    MATCH_MP_TAC HAS_M_DERIVATIVE_ZERO_UNIQUE THEN
    EXISTS_TAC `mat 0:real^1^1` THEN 
    REWRITE_TAC[MATRIX_OPEN_UNIV; MATRIX_CONVEX_UNIV; IN_UNIV] THEN
    REWRITE_TAC [DROP2_MAT; MATRIX_CMUL_LZERO; MATRIX_EXP_0;MATRIX_MUL_RID] THEN
    GEN_TAC THEN 
    SUBGOAL_THEN 
    `mat 0: real^N^N = matrix_exp (drop_drop t %% (A + B:real^N^N)) ** 
    (matrix_exp (drop_drop t %% (--A)) ** ((--B) ** matrix_exp (drop_drop t %% --B))
    + (--A ** matrix_exp (drop_drop t %% --A)) ** matrix_exp (drop_drop t %% --B)) +
    ((A + B) ** matrix_exp (drop_drop t %% (A + B))) **
          matrix_exp (drop_drop t %% --A) ** matrix_exp (drop_drop t %% --B)` 
          SUBST1_TAC THENL
    [SIMP_TAC [MATRIX_ADD_LDISTRIB] THEN 
    SIMP_TAC [GSYM MATRIX_ADD_ASSOC; GSYM MATRIX_MUL_ASSOC] THEN 
    SIMP_TAC [MESON [MATRIX_MUL_ASSOC]
    `!A:real^N^N B:real^N^N C:real^N^N D:real^N^N. 
    A ** B ** C ** D = A ** (B ** C) ** D`] THEN 
    ASM_SIMP_TAC [comm_lem1; comm_lem2] THEN 
    SIMP_TAC [GSYM (MESON [MATRIX_MUL_ASSOC]
    `!A:real^N^N B:real^N^N C:real^N^N D:real^N^N. 
    A ** B ** C ** D = A ** (B ** C) ** D`)] THEN 
    SIMP_TAC [MATRIX_MUL_ASSOC] THEN 
    ASM_SIMP_TAC [comm_lem3; comm_lem4] THEN SIMP_TAC [GSYM MATRIX_MUL_ASSOC] THEN
    SIMP_TAC [CMATRIX_ARITH 
    `!c:real^N^M e:real^P^N. a ** e + b ** e + c ** e = (a + b + c) ** e`] THEN 
    SIMP_TAC [CMATRIX_ARITH `--B + --A + A + B = mat 0`; MATRIX_MUL_LZERO];
    ALL_TAC] THEN 
    MATCH_MP_TAC HAS_M_DERIVATIVE_MUL_WITHIN THEN 
    SIMP_TAC [MATRIX_WITHIN_UNIV; HAS_M_DERIVATIVE_EXP] THEN 
    MATCH_MP_TAC HAS_M_DERIVATIVE_MUL_AT THEN 
    SIMP_TAC [MATRIX_WITHIN_UNIV; HAS_M_DERIVATIVE_EXP]);;
    
let MATRIX_EXP_ADD = prove
(`!A:real^N^N B. A ** B = B ** A ==> matrix_exp (A + B) = matrix_exp A ** matrix_exp B`,
let lem = prove
(`!A B:real^N^N C:real^N^N. invertible C /\ A ** C = B ** C ==> A = B `,
MESON_TAC [MATRIX_MUL_RCANCEL]) in
let comm_lem = prove 
(`!A:real^N^N B. A ** B = B ** A ==> matrix_exp A ** matrix_exp B = matrix_exp B ** matrix_exp A`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_EXP_COMM_LEMMA THEN 
ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC MATRIX_EXP_COMM_LEMMA THEN 
ASM_SIMP_TAC [] ) in 
let comm_lem1 = prove
(`!A. matrix_exp  (--A) ** matrix_exp (A) = matrix_exp (A) ** matrix_exp  (--A)`,
    REPEAT GEN_TAC THEN MATCH_MP_TAC MATRIX_EXP_COMM_LEMMA THEN 
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN 
    MATCH_MP_TAC MATRIX_EXP_COMM_LEMMA THEN 
    CMATRIX_ARITH_TAC) in 
REPEAT STRIP_TAC THEN
FIRST_ASSUM (SUBST1_TAC o MATCH_MP comm_lem) THEN 
FIRST_ASSUM (MP_TAC o SPEC `mat 1:real^1^1` o MATCH_MP MATRIX_EXP_ADD_MUL_FUN) THEN 
MP_TAC (ISPECL [`A:real^N^N`; `mat 1:real^1^1`] MATRIX_EXP_INV_FUN) THEN 
MP_TAC (ISPECL [`B:real^N^N`; `mat 1:real^1^1`] MATRIX_EXP_INV_FUN) THEN 
SIMP_TAC [MATRIX_CMUL_LID; DROP2_MAT] THEN REPEAT STRIP_TAC THEN 
SUBGOAL_THEN `invertible (matrix_exp (--A:real^N^N)) /\ invertible (matrix_exp (--B:real^N^N))` STRIP_ASSUME_TAC THENL 
[ASM_MESON_TAC [INVERTIBLE_LEFT_INVERSE; INVERTIBLE_RIGHT_INVERSE]; ALL_TAC] THEN 
MATCH_MP_TAC lem THEN EXISTS_TAC `matrix_exp (--A:real^N^N)` THEN 
ASM_SIMP_TAC [GSYM MATRIX_MUL_ASSOC] THEN 
ASM_SIMP_TAC [GSYM comm_lem1; MATRIX_MUL_RID] THEN 
MATCH_MP_TAC lem THEN EXISTS_TAC `matrix_exp (--B:real^N^N)` THEN 
ASM_SIMP_TAC [GSYM MATRIX_MUL_ASSOC] THEN 
ASM_SIMP_TAC [GSYM comm_lem1; MATRIX_MUL_RID]);; 
 
 
(* ------------------------------------------------------------------------- *)
(* Continuity of special function (like det)                                           *)
(* ------------------------------------------------------------------------- *)
          
let COMPONENT_LE_FNORM2 = prove
    (`!A:real^N^M B:real^N^M i j.
     abs(A$i$j) <= fnorm (A-B) + fnorm B /\ abs(B$i$j) <= fnorm (A-B) + fnorm B`,
    REPEAT GEN_TAC THEN CONJ_TAC THEN
    W(MP_TAC o PART_MATCH lhand COMPONENT_LE_FNORM o lhand o snd) THEN
    SIMP_TAC[FNORM_EQ_NORM_VECTORIZE;VECTORIZE_SUB] THEN NORM_ARITH_TAC);;   

let DET_SUB_LE = prove
    (`!A:real^N^N B:real^N^N. abs(det A - det B) <= 
      sum { p | p permutes 1..dimindex(:N) } 
      (\p. abs (product (1..dimindex(:N)) (\i. A$i$(p i)) - product (1..dimindex(:N)) (\i. B$i$(p i))))`,
    REPEAT GEN_TAC THEN SIMP_TAC[det] THEN 
    MP_TAC (SIMP_RULE [FINITE_NUMSEG] (ISPECL [`1..dimindex (:N)`] FINITE_PERMUTATIONS)) THEN STRIP_TAC THEN
    ASM_SIMP_TAC [GSYM SUM_SUB;GSYM REAL_SUB_LDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {p | p permutes 1..dimindex (:N)}
     (\p. abs
           (sign p *(product (1..dimindex (:N)) (\i. (A:real^N^N)$i$p i) -
           product (1..dimindex (:N)) (\i. (B:real^N^N)$i$p i))))` THEN 
    ASM_SIMP_TAC [REAL_ABS_MUL;REAL_ABS_SIGN;REAL_MUL_LID;SUM_ABS] THEN
    SIMP_TAC[REAL_LE_REFL]);;

let matrix_component_max = new_definition
    `(matrix_component_max:real^N^N->real^N^N->real) A B =
     real_max (sup {A$i$j | (i IN (1..dimindex(:N))) /\ (j IN (1..dimindex(:N)))})
              (sup {B$i$j | (i IN (1..dimindex(:N))) /\ (j IN (1..dimindex(:N)))})` ;;
              
let matrix_max_element_abs_compare = new_definition
    `(matrix_max_element_abs_compare:real^N^M->real^Q^P->real) A B =
     real_max (sup {abs(A$i$j) | (i IN (1..dimindex(:M))) /\ (j IN (1..dimindex(:N)))})
              (sup {abs(B$i$j) | (i IN (1..dimindex(:P))) /\ (j IN (1..dimindex(:Q)))})` ;;

let MATRIX_ABS_MAX_ELEMENT_SET_IMAGE = prove
 (` {abs ((A:real^N^M)$i$j) | 
        i IN 1..dimindex (:M) /\ j IN 1..dimindex (:N)}
     = IMAGE (\(i,j). abs (A$i$j)) 
        {i,j | i IN 1..dimindex (:M) /\ j IN 1..dimindex (:N)}`,
  SIMP_TAC [IMAGE; EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN 
   EQ_TAC THENL 
   [REPEAT STRIP_TAC THEN 
    EXISTS_TAC `(i:num,j:num)` THEN CONJ_TAC; ALL_TAC] THENL
    [EXISTS_TAC `i:num` THEN EXISTS_TAC `j:num` THEN
     ASM_SIMP_TAC [PAIR_EQ];
     ASM_SIMP_TAC [];
     REPEAT STRIP_TAC THEN EXISTS_TAC `i:num` THEN 
     EXISTS_TAC `j:num` THEN ASM_SIMP_TAC [IN_NUMSEG]]);;              
              
let MATRIX_ABS_MAX_ELEMENT_SET_LEMMA = prove
 (`!x:real^N^M. FINITE {abs(x$i$j) |  i IN 1..dimindex (:M) /\ j IN 1..dimindex (:N)}
   /\
   ~({abs(x$i$j) |  i IN 1..dimindex (:M) /\ j IN 1..dimindex (:N)} = {})`,
  SIMP_TAC[MATRIX_ABS_MAX_ELEMENT_SET_IMAGE] THEN 
  SIMP_TAC[GSYM CROSS] THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FINITE_IMAGE; IMAGE_EQ_EMPTY;CROSS_EQ_EMPTY] THEN
  REWRITE_TAC[NUMSEG_EMPTY; DE_MORGAN_THM; NOT_LT; DIMINDEX_GE_1]);;
  
let MATRIX_LCOMPONENT_ABS_LE_MAX = prove
    (`!A:real^N^M B:real^Q^P i j. (1 <= i /\ i <= dimindex(:M)) /\ 
                                 (1 <= j /\ j <= dimindex(:N)) ==>
         abs (A$i$j) <= matrix_max_element_abs_compare A B`,
    SIMP_TAC [matrix_max_element_abs_compare; GSYM IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN 
    MATCH_MP_TAC REAL_LE_TRANS THEN 
    EXISTS_TAC `sup {abs ((A:real^N^M)$i$j) | i IN 1..dimindex (:M) /\ j IN 1..dimindex (:N)}` THEN SIMP_TAC [REAL_MAX_MAX] THEN 
    MP_TAC(SPEC `{abs ((A:real^N^M)$i$j) | i IN 1..dimindex (:M) /\ 
                                           j IN 1..dimindex (:N)}`
              SUP_FINITE) THEN
    SIMP_TAC[MATRIX_ABS_MAX_ELEMENT_SET_LEMMA] THEN
    SIMP_TAC[MATRIX_ABS_MAX_ELEMENT_SET_IMAGE; FORALL_IN_IMAGE] THEN 
    REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o SPEC `(i:num,j:num)`) THEN 
    SIMP_TAC [IN_ELIM_THM] THEN SIMP_TAC [PAIR_EQ] THEN 
    ASM_MESON_TAC []);;
    
let MATRIX_RCOMPONENT_ABS_LE_MAX = prove
    (`!A:real^N^M B:real^Q^P i j. (1 <= i /\ i <= dimindex(:P)) /\ 
                                 (1 <= j /\ j <= dimindex(:Q)) ==>
         abs (B$i$j) <= matrix_max_element_abs_compare A B`,
    SIMP_TAC [matrix_max_element_abs_compare; GSYM IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN 
    MATCH_MP_TAC REAL_LE_TRANS THEN 
    EXISTS_TAC `sup {abs ((B:real^Q^P)$i$j) | i IN 1..dimindex (:P) /\ j IN 1..dimindex (:Q)}` THEN SIMP_TAC [REAL_MAX_MAX] THEN 
    MP_TAC(SPEC `{abs ((B:real^Q^P)$i$j) | i IN 1..dimindex (:P) /\ 
                                           j IN 1..dimindex (:Q)}`
              SUP_FINITE) THEN
    SIMP_TAC[MATRIX_ABS_MAX_ELEMENT_SET_LEMMA] THEN
    SIMP_TAC[MATRIX_ABS_MAX_ELEMENT_SET_IMAGE; FORALL_IN_IMAGE] THEN 
    REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o SPEC `(i:num,j:num)`) THEN 
    SIMP_TAC [IN_ELIM_THM] THEN SIMP_TAC [PAIR_EQ] THEN 
    ASM_MESON_TAC []);;
 
let PRODUCT_SUM_LEMMA = prove
(`!a:num->real b:num->real n:num.
 product (1..n) (\i. a(i)) - product (1..n) (\j. b(j)) = 
 sum (1..n) (\k.  (product (1..(k - 1)) (\u. b(u))) * (a(k) - b(k)) * (product ((SUC k)..n) (\v. a(v))))`,
 GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
 SIMP_TAC [PRODUCT_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG] THENL
 [SIMP_TAC [ARITH_RULE `~(1 = 0)`; SUB_REFL;REAL_SUB_REFL]; ALL_TAC] THEN 
 SIMP_TAC [ARITH_RULE `1 <= SUC n`; ARITH_RULE `~(SUC (SUC n) <= SUC n)`;
           ARITH_RULE `SUC a <= SUC b <=> a <= b`] THEN 
 SIMP_TAC [SUC_SUB1] THEN 
 SUBGOAL_THEN `(SUC (SUC n)..n) = {}` SUBST1_TAC THENL
 [SIMP_TAC [NUMSEG_EMPTY] THEN ARITH_TAC; ALL_TAC] THEN 
 SIMP_TAC [PRODUCT_CLAUSES; REAL_MUL_RID] THEN 
 REWRITE_TAC [REAL_MUL_ASSOC] THEN SIMP_TAC [SUM_RMUL] THEN
 SIMP_TAC [GSYM REAL_MUL_ASSOC] THEN 
 FIRST_ASSUM (SUBST1_TAC o SYM) THEN 
 SUBGOAL_THEN `product (1..n) (\u. (b:num->real) u)  = product (1..n) (\j. b j)`
 SUBST1_TAC THENL 
 [AP_TERM_TAC THEN SIMP_TAC [FUN_EQ_THM]; ALL_TAC] THEN 
 REAL_ARITH_TAC);;
 
let DET_SUB_LE1 = prove
    (`!A:real^N^N B:real^N^N.
      sum { p | p permutes 1..dimindex(:N) } 
      (\p. abs (product (1..dimindex(:N)) (\i. A$i$(p i)) - product (1..dimindex(:N)) (\i. B$i$(p i)))) <=
      sum { p | p permutes 1..dimindex(:N) }
      (\p. sum (1..dimindex(:N)) 
           (\i. ((matrix_max_element_abs_compare A B) pow (dimindex(:N)-1)) * abs(A$i$(p i) - B$i$(p i))))`,
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (SIMP_RULE [FINITE_NUMSEG] (ISPECL [`1..dimindex (:N)`] FINITE_PERMUTATIONS)) THEN
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC [PRODUCT_SUM_LEMMA] THEN MATCH_MP_TAC SUM_ABS_LE THEN 
    SIMP_TAC [FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN 
    SIMP_TAC [REAL_ABS_MUL] THEN 
    ASM_SIMP_TAC[ARITH_RULE `1 <= x' /\ (x' <= dimindex (:N)) ==> (dimindex (:N) - 1 = (((x' - 1) + 1) - 1) + ((dimindex (:N) + 1) - SUC x'))`] THEN
    SIMP_TAC[REAL_POW_ADD; GSYM CARD_NUMSEG; GSYM PRODUCT_CONST; FINITE_NUMSEG] THEN
    SIMP_TAC[REAL_ARITH `a * b * c <= (d * e) * b <=> (a * c) * b <= (d * e) * b`] THEN MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[REAL_ABS_POS] THEN 
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_ABS_POS;GSYM PRODUCT_ABS;FINITE_NUMSEG] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC PRODUCT_LE THEN
    SIMP_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN 
    UNDISCH_TAC `(x:num->num) IN {p | p permutes 1..dimindex (:N)}` THEN
    SIMP_TAC[IN_ELIM_THM;REAL_ABS_POS; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_TAC "a" `1 <= k /\ k <= dimindex (:N)`
    [POP_ASSUM MP_TAC THEN SIMP_TAC [IN_NUMSEG] THEN ASM_ARITH_TAC] THEN 
    FIRST_ASSUM (MP_TAC o SIMP_RULE [GSYM IN_NUMSEG]) THEN 
    ASM_SIMP_TAC [GSYM PERMUTES_IN_IMAGE] THEN 
    FIRST_X_ASSUM (SUBST1_TAC o MATCH_MP (ISPECL [`x:num->num`; `1..dimindex (:N)`; `k:num`] (GSYM PERMUTES_IN_IMAGE))) THEN 
    ASM_SIMP_TAC [IN_NUMSEG; MATRIX_RCOMPONENT_ABS_LE_MAX; 
                  MATRIX_LCOMPONENT_ABS_LE_MAX]);;

let DET_SUB_LE2 = prove
    (`!A:real^N^N B:real^N^N.
      sum { p | p permutes 1..dimindex(:N) } 
      (\p. abs (product (1..dimindex(:N)) (\i. A$i$(p i)) - product (1..dimindex(:N)) (\i. B$i$(p i)))) <=
      sum { p | p permutes 1..dimindex(:N) }
      (\p. sum (1..dimindex(:N)) 
           (\i. ((fnorm (A - B) + fnorm(B)) pow (dimindex(:N)-1)) * abs(A$i$(p i) - B$i$(p i))))`,
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (SIMP_RULE [FINITE_NUMSEG] (ISPECL [`1..dimindex (:N)`] FINITE_PERMUTATIONS)) THEN
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC [PRODUCT_SUM_LEMMA] THEN MATCH_MP_TAC SUM_ABS_LE THEN 
    SIMP_TAC [FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN 
    SIMP_TAC [REAL_ABS_MUL] THEN 
    ASM_SIMP_TAC[ARITH_RULE `1 <= x' /\ (x' <= dimindex (:N)) ==> (dimindex (:N) - 1 = (((x' - 1) + 1) - 1) + ((dimindex (:N) + 1) - SUC x'))`] THEN
    SIMP_TAC[REAL_POW_ADD; GSYM CARD_NUMSEG; GSYM PRODUCT_CONST; FINITE_NUMSEG] THEN
    SIMP_TAC[REAL_ARITH `a * b * c <= (d * e) * b <=> (a * c) * b <= (d * e) * b`] THEN MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[REAL_ABS_POS] THEN 
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_ABS_POS;GSYM PRODUCT_ABS;FINITE_NUMSEG] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC PRODUCT_LE THEN
    SIMP_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN 
    UNDISCH_TAC `(x:num->num) IN {p | p permutes 1..dimindex (:N)}` THEN
    SIMP_TAC[IN_ELIM_THM;REAL_ABS_POS; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_TAC "a" `1 <= k /\ k <= dimindex (:N)`
    [POP_ASSUM MP_TAC THEN SIMP_TAC [IN_NUMSEG] THEN ASM_ARITH_TAC] THEN 
    FIRST_ASSUM (MP_TAC o SIMP_RULE [GSYM IN_NUMSEG]) THEN 
    ASM_SIMP_TAC [GSYM PERMUTES_IN_IMAGE] THEN 
    FIRST_X_ASSUM (SUBST1_TAC o MATCH_MP (ISPECL [`x:num->num`; `1..dimindex (:N)`; `k:num`] (GSYM PERMUTES_IN_IMAGE))) THEN 
    ASM_SIMP_TAC [IN_NUMSEG; COMPONENT_LE_FNORM2]);;
    
let SUM_PERMUTES_SUM_CONST = prove
    (`!c:real. sum { p | p permutes 1..dimindex(:N) } 
     (\p. (sum (1..dimindex(:N)) (\i. c))) = 
     &(FACT (dimindex(:N))) * &(dimindex(:N)) * c`,
     GEN_TAC THEN SIMP_TAC [SUM_CONST_NUMSEG] THEN
     ASSUME_TAC (SIMP_RULE [FINITE_NUMSEG] (ISPECL [`1..dimindex (:N)`] FINITE_PERMUTATIONS)) THEN
     ASM_SIMP_TAC [SUM_CONST;CARD_PERMUTATIONS; FINITE_NUMSEG] THEN
     SIMP_TAC [CARD_NUMSEG;ADD_SUB]);;
     
let NUMSEG_DIMINDEX_PAIR_NONEMPTY = prove
 (`?i j. i IN 1..dimindex(:N) /\ j IN 1..dimindex (:M)`,
  MP_TAC NUMSEG_DIMINDEX_NONEMPTY THEN MATCH_MP_TAC MONO_EXISTS THEN 
  ASM_SIMP_TAC [NUMSEG_DIMINDEX_NONEMPTY]);;

let MATRIX_ABS_MAX_POS_LE = prove
 (`!A:real^N^M. &0 <= sup {abs (A$i$j) | i IN 1..dimindex (:M) /\ j IN 1..dimindex (:N)}`,
  SIMP_TAC[REAL_LE_SUP_FINITE; MATRIX_ABS_MAX_ELEMENT_SET_LEMMA] THEN
  SIMP_TAC[MATRIX_ABS_MAX_ELEMENT_SET_IMAGE; NUMSEG_DIMINDEX_PAIR_NONEMPTY;
              EXISTS_IN_IMAGE; REAL_ABS_POS; GSYM CROSS;EXISTS_IN_CROSS]);;
              
let MATRIX_ABS_MAX_EQ_0 = prove
 (`!A:real^N^M. sup {abs (A$i$j) | i IN 1..dimindex (:M) /\ j IN 1..dimindex (:N)} = &0 <=> A = mat 0`,
  GEN_TAC THEN 
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; MATRIX_ABS_MAX_POS_LE] THEN
  SIMP_TAC[REAL_SUP_LE_FINITE; MATRIX_ABS_MAX_ELEMENT_SET_LEMMA] THEN
  SIMP_TAC[FORALL_IN_IMAGE; MATRIX_ABS_MAX_ELEMENT_SET_IMAGE] THEN 
  SIMP_TAC [GSYM CROSS; FORALL_PAIR_THM; IN_CROSS; 
            CART_EQ; MAT_COMPONENT; IN_NUMSEG] THEN
  MESON_TAC[ REAL_ARITH `abs(x) <= &0 <=> x = &0`]);;
  
let MATRIX_ABS_MAX_COMPARE_EQ_0 = prove
 (`!A:real^N^M B:real^Q^P. (matrix_max_element_abs_compare A B) = &0 <=>
                           A = mat 0 /\ B = mat 0`,
  REPEAT GEN_TAC THEN 
  SIMP_TAC[matrix_max_element_abs_compare;real_max] THEN
  COND_CASES_TAC THEN
  ASM_MESON_TAC [REAL_ARITH `&0 <= A /\ A <= B /\ B = &0 ==> A = &0`;
                  REAL_ARITH `~(A <= B) ==> B <= A`;
                 MATRIX_ABS_MAX_POS_LE;MATRIX_ABS_MAX_EQ_0]);;
 
let MATRIX_ABS_MAX_POS_LT = prove
 (`!A:real^N^M. &0 < sup {abs (A$i$j) | i IN 1..dimindex (:M) /\ j IN 1..dimindex (:N)} <=> ~(A = mat 0)`,
  MESON_TAC[REAL_LT_LE; MATRIX_ABS_MAX_POS_LE; MATRIX_ABS_MAX_EQ_0]);;
  
let MATRIX_MAX_ELEMENT_ABS_POS_LE = prove
    (`!A:real^N^M B:real^Q^P.  
           &0 <= matrix_max_element_abs_compare A B`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sup {abs ((A:real^N^M)$i$j) | i IN 1..dimindex (:M) /\ j IN 1..dimindex (:N)}` THEN
    ASM_SIMP_TAC[matrix_max_element_abs_compare;
                 REAL_MAX_MAX;MATRIX_ABS_MAX_POS_LE]);;
 
let MATRIX_MAX_LELEMENT_ABS_LT = prove
    (`!A:real^N^M B:real^Q^P. ~(A = mat 0) ==>  
           &0 < matrix_max_element_abs_compare A B`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `sup {abs ((A:real^N^M)$i$j) | i IN 1..dimindex (:M) /\ j IN 1..dimindex (:N)}` THEN
    ASM_SIMP_TAC[matrix_max_element_abs_compare;
                 REAL_MAX_MAX;MATRIX_ABS_MAX_POS_LT]);;
                 
let MATRIX_MAX_RELEMENT_ABS_LT = prove
    (`!A:real^N^M B:real^Q^P. ~(B = mat 0) ==>  
           &0 < matrix_max_element_abs_compare A B`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `sup {abs ((B:real^Q^P)$i$j) | i IN 1..dimindex (:P) /\ j IN 1..dimindex (:Q)}` THEN
    ASM_SIMP_TAC[matrix_max_element_abs_compare;
                 REAL_MAX_MAX;MATRIX_ABS_MAX_POS_LT]);;
                 
let MATRIX_MAX_ELEMENT_ABS_LT = prove
    (`!A:real^N^M B:real^N^M. ~(A = B) ==>  
           &0 < matrix_max_element_abs_compare A B`,
    REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC
     [`A:real^N^M = mat 0`; `B:real^N^M = mat 0`] THEN
    ASM_MESON_TAC [MATRIX_MAX_LELEMENT_ABS_LT;
                   MATRIX_MAX_RELEMENT_ABS_LT]);; 
                   
let DET_BOUNDED_POS = prove 
(`!A:real^N^N B:real^N^N. ?k:real. &0 < k /\ abs(det (A) - det(B)) <= k * fnorm (A - B)`,
    let lem = prove
    (`!A:real^N^N B:real^N^N.
      sum {p | p permutes 1..dimindex (:N)}
      (\x. sum (1..dimindex (:N))
      (\i. matrix_max_element_abs_compare A B pow (dimindex (:N) - 1) *
           abs ((A - B)$i$x i))) <= 
      sum {p | p permutes 1..dimindex (:N)}
      (\x. sum (1..dimindex (:N))
      (\i. matrix_max_element_abs_compare A B pow (dimindex (:N) - 1) *
           fnorm (A - B)))`,
    REPEAT GEN_TAC THEN 
    ASSUME_TAC (SIMP_RULE [FINITE_NUMSEG] (ISPECL [`1..dimindex (:N)`] FINITE_PERMUTATIONS)) THEN 
    MATCH_MP_TAC SUM_SUM_LE THEN ASM_SIMP_TAC [FINITE_NUMSEG] THEN 
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN 
    SIMP_TAC [MATRIX_MAX_ELEMENT_ABS_POS_LE;
              REAL_POW_LE; COMPONENT_LE_FNORM]) in

    REPEAT GEN_TAC THEN 
    MAP_EVERY ASM_CASES_TAC [`A:real^N^N = mat 0`; `B:real^N^N = mat 0`] THENL
    [EXISTS_TAC `&1:real` THEN
    ASM_SIMP_TAC [MATRIX_SUB_REFL; DET_0; FNORM_0; REAL_ABS_0] THEN 
     REAL_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN 
    EXISTS_TAC `&(FACT (dimindex(:N))) * &(dimindex(:N)) * 
       (matrix_max_element_abs_compare (A:real^N^N) (B:real^N^N)) pow (dimindex(:N)-1)` THEN 
    ASM_SIMP_TAC [MESON [REAL_LT_MUL] `!c:real. &0 < a /\ &0 < b /\ &0 < c ==>
                             &0 < a * b * c`;
                  FACT_LT; DIMINDEX_GE_1; 
                  MATRIX_MAX_LELEMENT_ABS_LT;
                  MATRIX_MAX_RELEMENT_ABS_LT; REAL_POW_LT; REAL_OF_NUM_LT;
                  REAL_OF_NUM_LE; ARITH_RULE `1 <= x ==> 0 < x`;
                  REAL_ARITH `&1 <= x ==> &0 < x`] THEN
     W(MP_TAC o PART_MATCH lhand DET_SUB_LE o lhand o snd) THEN 
     MATCH_MP_TAC (REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
     W(MP_TAC o PART_MATCH lhand DET_SUB_LE1 o lhand o snd) THEN 
     MATCH_MP_TAC (REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
     SIMP_TAC [GSYM MATRIX_SUB_COMPONENT] THEN
     W(MP_TAC o PART_MATCH lhand lem o lhand o snd) THEN 
     MATCH_MP_TAC (REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
     SIMP_TAC [SUM_PERMUTES_SUM_CONST] THEN REAL_ARITH_TAC);;  
     
let DET_BOUNDED = prove 
(`!A:real^N^N B. abs(det (A) - det(B)) <= 
           &(FACT (dimindex(:N))) * &(dimindex(:N)) * 
            ((fnorm (A - B) + fnorm(B)) pow (dimindex(:N)-1)) * fnorm (A - B)`,
     let lem = prove
    (`!A:real^N^N B:real^N^N.
      sum {p | p permutes 1..dimindex (:N)}
      (\x. sum (1..dimindex (:N))
      (\i. ((fnorm (A - B) + fnorm(B)) pow (dimindex(:N)-1)) * abs ((A - B)$i$x i))) <= 
      sum {p | p permutes 1..dimindex (:N)}
      (\x. sum (1..dimindex (:N))
      (\i. ((fnorm (A - B) + fnorm(B)) pow (dimindex(:N)-1)) * fnorm (A - B)))`,
    REPEAT GEN_TAC THEN 
    ASSUME_TAC (SIMP_RULE [FINITE_NUMSEG] (ISPECL [`1..dimindex (:N)`] FINITE_PERMUTATIONS)) THEN 
    MATCH_MP_TAC SUM_SUM_LE THEN ASM_SIMP_TAC [FINITE_NUMSEG] THEN 
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN 
    SIMP_TAC [REAL_LE_ADD; FNORM_POS_LE;
              REAL_POW_LE; COMPONENT_LE_FNORM]) in
              
     REPEAT GEN_TAC THEN
     W(MP_TAC o PART_MATCH lhand DET_SUB_LE o lhand o snd) THEN 
     MATCH_MP_TAC (REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
     W(MP_TAC o PART_MATCH lhand DET_SUB_LE2 o lhand o snd) THEN 
     MATCH_MP_TAC (REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
     SIMP_TAC [GSYM MATRIX_SUB_COMPONENT] THEN      
     W(MP_TAC o PART_MATCH lhand lem o lhand o snd) THEN 
     MATCH_MP_TAC (REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
     SIMP_TAC [SUM_PERMUTES_SUM_CONST] THEN REAL_ARITH_TAC);;
        
let MATRIX_CONTINUOUS_WITHIN_DIST = prove
(`!f x:real^N^M s. f matrix_continuous (matrix_at x within s) <=> 
                ((\a:real^N^M. lift_lift (matrix_dist (f(a), f x))) ->-> mat 0) (matrix_at x within s)`,
    SIMP_TAC [MATRIX_CONTINUOUS_WITHIN; MATRIX_LIM_WITHIN] THEN 
    SIMP_TAC [matrix_dist; MATRIX_SUB_RZERO; FNORM_REAL] THEN 
    SIMP_TAC [LIFT2_COMPONENT] THEN 
    SIMP_TAC [MESON [REAL_ABS_REFL] 
          `!x.  &0 <= x ==>  abs x = x`; FNORM_POS_LE]);;
        
let MATRIX_CONTINUOUS_AT_DIST = prove
(`!f x:real^N^M. f matrix_continuous (matrix_at x) <=> 
                ((\a:real^N^M. lift_lift (matrix_dist (f(a), f x))) ->-> mat 0) (matrix_at x)`,
    SIMP_TAC [MATRIX_CONTINUOUS_AT; MATRIX_LIM_AT] THEN 
    SIMP_TAC [matrix_dist; MATRIX_SUB_RZERO; FNORM_REAL] THEN 
    SIMP_TAC [LIFT2_COMPONENT] THEN 
    SIMP_TAC [MESON [REAL_ABS_REFL] 
          `!x.  &0 <= x ==>  abs x = x`; FNORM_POS_LE]);;
          
let MATRIX_LIM_WITHIN_COMPARE_LIFT2 = prove
(`!f:real^N^M->real g a:real^N^M s. (!x. &0 <= f(x) /\ f(x) <= g(x)) /\  
        ((\x. lift_lift (g(x))) ->-> mat 0) (matrix_at a within s) ==> 
        ((\x. lift_lift (f(x))) ->-> mat 0) (matrix_at a within s)`,
        SIMP_TAC [MATRIX_LIM_WITHIN] THEN 
        SIMP_TAC [matrix_dist; MATRIX_SUB_RZERO; FNORM_REAL] THEN 
        SIMP_TAC [LIFT2_COMPONENT] THEN REPEAT STRIP_TAC THEN 
        FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC [] THEN 
        STRIP_TAC THEN POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
        ASM_MESON_TAC [ REAL_ARITH `&0 <= f /\ f <= g ==> &0 <= g`;
                       MESON [REAL_ABS_REFL] 
                       `!x.  &0 <= x ==>  abs x = x`;
                       REAL_LET_TRANS]);;

let MATRIX_LIM_AT_COMPARE_LIFT2 = prove
(`!f:real^N^M->real g a:real^N^M. (!x. &0 <= f(x) /\ f(x) <= g(x)) /\  
        ((\x. lift_lift (g(x))) ->-> mat 0) (matrix_at a) ==> 
        ((\x. lift_lift (f(x))) ->-> mat 0) (matrix_at a)`,
        SIMP_TAC [MATRIX_LIM_AT] THEN 
        SIMP_TAC [matrix_dist; MATRIX_SUB_RZERO; FNORM_REAL] THEN 
        SIMP_TAC [LIFT2_COMPONENT] THEN REPEAT STRIP_TAC THEN 
        FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC [] THEN 
        STRIP_TAC THEN POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
        ASM_MESON_TAC [ REAL_ARITH `&0 <= f /\ f <= g ==> &0 <= g`;
                       MESON [REAL_ABS_REFL] 
                       `!x.  &0 <= x ==>  abs x = x`;
                       REAL_LET_TRANS]);;
                       
let MATRIX_CONTINUOUS_AT_BALL = prove
 (`!f x. f matrix_continuous (matrix_at x) <=>
                !e. &0 < e
                    ==> ?d. &0 < d /\
                    IMAGE f (matrix_ball(x,d)) SUBSET matrix_ball(f x,e)`,
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_MATRIX_BALL; matrix_continuous_at] THEN
  MESON_TAC[MATRIX_DIST_SYM]);;

let MATRIX_LIM_LIFT2_POW = prove
 (`!net:(A)net f l n.
        ((\a. lift_lift(f a)) ->-> lift_lift l) net
        ==> ((\a. lift_lift(f(a) pow n)) ->-> lift_lift(l pow n)) net`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[real_pow; MATRIX_LIM_CONST; LIFT2_CMUL] THEN
  MATCH_MP_TAC MATRIX_LIM_CMUL1 THEN ASM_REWRITE_TAC[o_DEF]);;
     
let MATRIX_LIM_LIFT2_FNORM = prove
    (`!x:real^N^M. ((\a. lift_lift (fnorm (a - x))) ->-> mat 0) (matrix_at x)`,
     SIMP_TAC[MATRIX_LIM_AT] THEN REPEAT STRIP_TAC THEN
     SIMP_TAC[GSYM LIFT2_NUM;MATRIX_DIST_LIFT2] THEN SIMP_TAC[matrix_dist] THEN
     SIMP_TAC[REAL_SUB_RZERO] THEN 
     SIMP_TAC [MESON [REAL_ABS_REFL] 
          `!x.    &0 <= x ==>  abs x = x`; FNORM_POS_LE] THEN
     ASM_MESON_TAC[]);;
                       
let DET_CONTINUOUS_AT = prove 
    (`!x:real^N^N. 
    (\A:real^N^N. lift_lift (det A)) matrix_continuous (matrix_at x)`,
     SIMP_TAC [MATRIX_CONTINUOUS_AT_DIST] THEN 
     SIMP_TAC[matrix_dist] THEN
     SIMP_TAC[GSYM LIFT2_SUB;FNORM_REAL;LIFT2_COMPONENT] THEN 
     GEN_TAC THEN MATCH_MP_TAC MATRIX_LIM_AT_COMPARE_LIFT2 THEN
     EXISTS_TAC `\a:real^N^N. &(FACT (dimindex(:N))) * &(dimindex(:N)) * 
            ((fnorm (a - x) + fnorm(x)) pow (dimindex(:N)-1)) * fnorm (a - x)` THEN
     SIMP_TAC [REAL_ABS_POS; DET_BOUNDED] THEN SIMP_TAC [LIFT2_CMUL] THEN 
     ONCE_REWRITE_TAC [GSYM LIFT2_CMUL] THEN SIMP_TAC[MATRIX_CMUL_ASSOC] THEN 
     ONCE_REWRITE_TAC [
       CMATRIX_ARITH `mat 0:real^1^1 =  (&(FACT (dimindex (:N))) * &(dimindex (:N))) %% mat 0`] THEN 
     MATCH_MP_TAC MATRIX_LIM_CMUL THEN 
     ONCE_REWRITE_TAC [
       CMATRIX_ARITH `mat 0:real^1^1 = ((&0 + fnorm (x:real^N^N)) pow (dimindex (:N) - 1)) %% mat 0`] THEN
     SIMP_TAC[LIFT2_CMUL] THEN
     MATCH_MP_TAC MATRIX_LIM_CMUL1 THEN
     SIMP_TAC[MATRIX_LIM_LIFT2_FNORM; o_DEF] THEN
     MATCH_MP_TAC MATRIX_LIM_LIFT2_POW THEN
     SIMP_TAC[LIFT2_ADD] THEN MATCH_MP_TAC MATRIX_LIM_ADD THEN
     SIMP_TAC[MATRIX_LIM_CONST;MATRIX_LIM_LIFT2_FNORM;LIFT2_NUM]);;

let MATRIX_CONTINUOUS_WITHIN_COMPOSE = prove
 (`!f g x s. f matrix_continuous (matrix_at x within s) /\
             g matrix_continuous (matrix_at (f x) within IMAGE f s)
             ==> (g o f) matrix_continuous (matrix_at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_continuous_within; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;
     
let MATRIX_CONTINUOUS_AT_COMPOSE = prove
 (`!f g x. f matrix_continuous (matrix_at x) /\ g matrix_continuous (matrix_at (f x))
           ==> (g o f) matrix_continuous (matrix_at x)`,
  ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN
  MESON_TAC[MATRIX_CONTINUOUS_WITHIN_COMPOSE; IN_IMAGE;
            MATRIX_CONTINUOUS_WITHIN_SUBSET;SUBSET_UNIV; IN_UNIV]);;
            
let MATRIX_CONTINUOUS_ON_COMPARISON = prove
 (`!f:real^N^M->real^Q^P g:real^N^M->real^N^M s.
        g matrix_continuous_on s /\
        (!x y. x IN s /\ y IN s ==> matrix_dist(f x,f y) <= matrix_dist(g x,g y))
        ==> f matrix_continuous_on s`,
  REWRITE_TAC[matrix_continuous_on] THEN MESON_TAC[REAL_LET_TRANS]);;
  
let MATRIX_CONTINUOUS_MSUM = prove
 (`!net f s. FINITE s /\ (!a. a IN s ==> (f a) matrix_continuous net)
             ==> (\x. msum s (\a. f a x)) matrix_continuous net`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; MSUM_CLAUSES;
           MATRIX_CONTINUOUS_CONST; MATRIX_CONTINUOUS_ADD; ETA_AX]);;
           
let MATRIX_LIM_MUL = prove
 (`!net:(A)net f:A->real^N^M  g:A->real^S^N a b. 
    (f ->-> a) net /\ (g ->-> b) net ==> 
    (((\x.  (f x) ** (g x))) ->->  (a ** b)) net`,
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[MATRIX_LIM_COMPONENTWISE_REAL] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [matrix_mul; CART_EQ; LAMBDA_BETA] THEN 
  MATCH_MP_TAC LIMIT_REAL_SUM THEN 
  SIMP_TAC [FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN 
  MATCH_MP_TAC LIMIT_REAL_MUL THEN ASM_SIMP_TAC[]);;
           
let MATRIX_CONTINUOUS_MUL = prove
 (`!net f:real^Q^P->real^N^M g:real^Q^P->real^S^N.
   f matrix_continuous net /\ g matrix_continuous net ==>
   (\x. (f x) ** (g x)) matrix_continuous net`,
   REWRITE_TAC [matrix_continuous; MATRIX_LIM_MUL]);;
   
let MATRIX_CONTINUOUS_POW = prove
 (`!net f:real^Q^P->real^N^N n.
        f matrix_continuous net
        ==> (\x. (f x) matrix_pow n) matrix_continuous net`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[matrix_pow; MATRIX_CONTINUOUS_CONST] THEN
  MATCH_MP_TAC MATRIX_CONTINUOUS_MUL THEN ASM_MESON_TAC[]);;
  
let MATRIX_CONTINUOUS_EXP_PARTIAL_SUM = prove
 (`!n x:real^N^N. (\z. msum(0..n) (\i. (&1 / &(FACT i)) %% (z matrix_pow i))) 
       matrix_continuous (matrix_at x)`,
    REPEAT GEN_TAC THEN MATCH_MP_TAC MATRIX_CONTINUOUS_MSUM THEN
    SIMP_TAC [FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN 
    MATCH_MP_TAC MATRIX_CONTINUOUS_CMUL THEN 
    MATCH_MP_TAC MATRIX_CONTINUOUS_POW THEN  
    REWRITE_TAC[MATRIX_CONTINUOUS_AT_ID]);;
    
let MATRIX_CONTINUOUS_EXP_PARTIAL_SUM_FINITE = prove
 (`!x:real^N^N s. FINITE s ==> (\z. msum s (\i. (&1 / &(FACT i)) %% (z matrix_pow i))) 
       matrix_continuous (matrix_at x)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_CONTINUOUS_MSUM THEN
    ASM_SIMP_TAC [FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN 
    MATCH_MP_TAC MATRIX_CONTINUOUS_CMUL THEN 
    MATCH_MP_TAC MATRIX_CONTINUOUS_POW THEN  
    REWRITE_TAC[MATRIX_CONTINUOUS_AT_ID]);;
    
let MATRIX_UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS = prove
 (`!f s. f matrix_uniformly_continuous_on s ==> f matrix_continuous_on s`,
  REWRITE_TAC[matrix_uniformly_continuous_on; matrix_continuous_on] THEN MESON_TAC[]);;
  
(* ------------------------------------------------------------------------- *)
(* Connectedness.                                                            *)
(* ------------------------------------------------------------------------- *)
(*
let matrix_connected = new_definition
  `matrix_connected s <=>
      ~(?e1 e2. matrix_open e1 /\ matrix_open e2 /\ s SUBSET (e1 UNION e2) /\
                (e1 INTER e2 INTER s = {}) /\
                ~(e1 INTER s = {}) /\ ~(e2 INTER s = {}))`;;
                
let CONNECTED_IN_MATRIX_SPACE = prove
 (`!s:real^N^M->bool. connected_in matrix_space s <=> matrix_connected s`,
  REWRITE_TAC[CONNECTED_IN; matrix_connected] THEN
  SIMP_TAC[TOPSPACE_MATRIX_SPACE; GSYM MATRIX_OPEN_IN; SUBSET_UNIV; INTER_UNIV]);;
  
let MATRIX_CONNECTED_CLOPEN = prove
 (`!s. matrix_connected s <=>
        !t. open_in (subtopology matrix_space s) t /\
            closed_in (subtopology matrix_space s) t ==> t = {} \/ t = s`,
  REWRITE_TAC[GSYM CONNECTED_IN_MATRIX_SPACE; connected_in] THEN
  REWRITE_TAC[TOPSPACE_MATRIX_SPACE; SUBSET_UNIV] THEN
  REWRITE_TAC[CONNECTED_SPACE_CLOPEN_IN; TOPSPACE_MATRIX_SPACE_SUBTOPOLOGY]);;
  
let MATRIX_CONNECTED_IFF_CONNECTABLE_POINTS = prove
 (`!s:real^N^M->bool.
        matrix_connected s <=>
        !a b. a IN s /\ b IN s
              ==> ?t. matrix_connected t /\ t SUBSET s /\ a IN t /\ b IN t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM CONNECTED_IN_MATRIX_SPACE] THEN
  GEN_REWRITE_TAC LAND_CONV [connected_in] THEN
  REWRITE_TAC[CONNECTED_SPACE_SUBCONNECTED; TOPSPACE_MATRIX_SPACE; SUBSET_UNIV;
              TOPSPACE_MATRIX_SPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; GSYM CONJ_ASSOC]);;
  
let MATRIX_CONNECTED_EMPTY = prove
 (`matrix_connected {}`,
  REWRITE_TAC[matrix_connected; INTER_EMPTY]);;
  
let MATRIX_CONNECTED_SING = prove
 (`!a. matrix_connected{a}`,
  REWRITE_TAC[matrix_connected] THEN SET_TAC[]);;
*)

let MATRIX_CONTINUOUS_MAP_COMPONENTWISE_REAL = prove
 (`!top (f:A->real^N^M).
        continuous_map (top,matrix_space) f <=>
        !i j. (1 <= i /\ i <= dimindex(:M)) /\ (1 <= j /\ j <= dimindex(:N))
            ==> continuous_map (top,euclideanreal) (\x. f x$i$j)`,
  SIMP_TAC[CONTINUOUS_MAP_ATPOINTOF; MATRIX_LIMIT_COMPONENTWISE_REAL] THEN
  MESON_TAC[]);;

(*  
let MATRIX_CONNECTED_SEGMENT = prove
 (`(!a b:real^N^M. matrix_connected(matrix_segment[a,b])) /\
   (!a b:real^N^M. matrix_connected(matrix_segment(a,b)))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `b:real^N^M = a` THEN
  ASM_SIMP_TAC[MATRIX_SEGMENT_REFL; MATRIX_CONNECTED_EMPTY; 
               MATRIX_CONNECTED_SING] THEN
  GEN_REWRITE_TAC RAND_CONV [SET_RULE `s = {x | x IN s}`] THEN
  ASM_REWRITE_TAC[GSYM CONNECTED_IN_MATRIX_SPACE; IN_MATRIX_SEGMENT; SET_RULE
   `{x | ?u. P u /\ Q u /\ x = f u} = IMAGE f {u | P u /\ Q u}`] THEN
  MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
  EXISTS_TAC `euclideanreal` THEN
  REWRITE_TAC[GSYM real_interval; CONNECTED_IN_EUCLIDEANREAL_INTERVAL] THEN
  REWRITE_TAC[MATRIX_CONTINUOUS_MAP_COMPONENTWISE_REAL] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL THEN
  TRY(MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB) THEN
  REWRITE_TAC[CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; IN_UNIV]);;
  
let MATRIX_CONNECTED_UNIV = prove
 (`matrix_connected(:real^N^M)`,
  ONCE_REWRITE_TAC[MATRIX_CONNECTED_IFF_CONNECTABLE_POINTS] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N^M`; `b:real^N^M`] THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV] THEN
  EXISTS_TAC `matrix_segment[a:real^N^M,b]` THEN
  ASM_REWRITE_TAC[MATRIX_CONNECTED_SEGMENT; ENDS_IN_MATRIX_SEGMENT]);;
*)
  
let MATRIX_LIMIT_POINT_UNION = prove
 (`!s t x:real^N^M. x matrix_limit_point_of (s UNION t) <=>
                  x matrix_limit_point_of s \/ x matrix_limit_point_of t`,
  REWRITE_TAC[MATRIX_LIMIT_POINT_IN_DERIVED_SET; DERIVED_SET_OF_UNION; IN_UNION]);;
  
let FINITE_MATRIX_SET_AVOID = prove
 (`!a:real^N^M s. FINITE s
                ==> ?d. &0 < d /\ !x. x IN s /\ ~(x = a) ==> d <= matrix_dist(a,x)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN
  CONJ_TAC THENL [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N^M`; `s:real^N^M->bool`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `x:real^N^M = a` THEN REWRITE_TAC[IN_INSERT] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `min d (matrix_dist(a:real^N^M,x))` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; GSYM MATRIX_DIST_NZ; REAL_MIN_LE] THEN
  ASM_MESON_TAC[REAL_LE_REFL]);;
  
let MATRIX_LIMIT_POINT_FINITE = prove
 (`!s a. FINITE s ==> ~(a matrix_limit_point_of s)`,
  REWRITE_TAC[MATRIX_LIMPT_APPROACHABLE; GSYM REAL_NOT_LE] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM; REAL_NOT_LE;
    REAL_NOT_LT; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN
  MESON_TAC[FINITE_MATRIX_SET_AVOID; MATRIX_DIST_SYM]);;
  
let MATRIX_LIMPT_INSERT = prove
 (`!s x y:real^N^M. x matrix_limit_point_of (y INSERT s) <=> x matrix_limit_point_of s`,
  ONCE_REWRITE_TAC[SET_RULE `y INSERT s = {y} UNION s`] THEN
  REWRITE_TAC[MATRIX_LIMIT_POINT_UNION] THEN
  SIMP_TAC[FINITE_SING; MATRIX_LIMIT_POINT_FINITE]);;
  
let MATRIX_LIMPT_EMPTY = prove
 (`!x. ~(x matrix_limit_point_of {})`,
  REWRITE_TAC[MATRIX_LIMPT_APPROACHABLE; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LT_01]);;
  
let MATRIX_CLOSED_SING = prove
 (`!a:real^N^M. matrix_closed {a}`,
  REWRITE_TAC[MATRIX_CLOSED_LIMPT; MATRIX_LIMPT_INSERT; MATRIX_LIMPT_EMPTY]);;
  
let MATRIX_CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT = prove
 (`!f:real^N^M->real^Q^P s a.
        f matrix_continuous_on s
        ==> closed_in (subtopology matrix_space s) {x | x IN s /\ f x = a}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{x | x IN s /\ f(x) = a} = {x | x IN s /\ f(x) IN {a}}`] THEN
  MATCH_MP_TAC MATRIX_CONTINUOUS_CLOSED_IN_PREIMAGE THEN
  ASM_REWRITE_TAC[MATRIX_CLOSED_SING]);;
  
let MATRIX_CLOSED_INTERVAL_LEFT = prove
 (`!b:real^N^M.
     matrix_closed {x:real^N^M | !i j. (1 <= i /\ i <= dimindex(:M)) /\ 
                         (1 <= j /\ j <= dimindex(:N))
                       ==> x$i$j <= b$i$j}`,
  REWRITE_TAC[MATRIX_CLOSED_LIMPT; MATRIX_LIMPT_APPROACHABLE; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x:real^N^M)$i$j - (b:real^N^M)$i$j`) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N^M` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[matrix_dist; REAL_NOT_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((z - x :real^N^M)$i$j)` THEN
  ASM_SIMP_TAC[COMPONENT_LE_FNORM] THEN
  ASM_SIMP_TAC[MATRIX_SUB_COMPONENT] THEN
  ASM_SIMP_TAC[REAL_ARITH `z <= b /\ b < x ==> x - b <= abs(z - x)`]);;
  
(*
let MATRIX_CLOSED_HALFSPACE_LE = prove
 (`!a:real^N^M b. matrix_closed {x | a mip x <= b}`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(:real^N^M)` MATRIX_CONTINUOUS_ON_LIFT2_MIP) THEN
  REWRITE_TAC[MATRIX_CONTINUOUS_ON_CLOSED; GSYM 
              MATRIX_CLOSED_IN; SUBTOPOLOGY_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE lift_lift {r | ?x:real^N^M. (a mip x = r) /\ r <= b}`) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN
    REWRITE_TAC[o_DEF] THEN MESON_TAC[LIFT2_DROP]] THEN
  REWRITE_TAC[MATRIX_CLOSED_IN_CLOSED] THEN
  EXISTS_TAC `{x | !i j. (1 <= i /\ i <= dimindex(:1)) /\ 
                         (1 <= j /\ j <= dimindex(:1))
                       ==> (x:real^1^1)$i$j <= (lift_lift b)$i$j}` THEN
  REWRITE_TAC[MATRIX_CLOSED_INTERVAL_LEFT] THEN
  SIMP_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_ELIM_THM; IN_INTER;
    MAT_COMPONENT; DIMINDEX_1; LAMBDA_BETA; o_THM] THEN
  SIMP_TAC[ARITH_RULE `1 <= i /\ i <= 1 <=> (i = 1)`] THEN
  REWRITE_TAC[GSYM drop_drop; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  MESON_TAC[LIFT2_DROP]);;
  
let MATRIX_CLOSED_HALFSPACE_GE = prove
 (`!a:real^N^M b. matrix_closed {x | a mip x >= b}`,
  REWRITE_TAC[REAL_ARITH `a >= b <=> --a <= --b`] THEN
  REWRITE_TAC[GSYM MIP_LNEG; MATRIX_CLOSED_HALFSPACE_LE]);;
  
let MATRIX_OPEN_HALFSPACE_LT = prove
 (`!a b. matrix_open {x | a mip x < b}`,
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  REWRITE_TAC[SET_RULE `{x | ~p x} = UNIV DIFF {x | p x}`] THEN
  REWRITE_TAC[GSYM matrix_closed; GSYM real_ge; MATRIX_CLOSED_HALFSPACE_GE]);;
  
let MATRIX_OPEN_HALFSPACE_GT = prove
 (`!a b. matrix_open {x | a mip x > b}`,
  REWRITE_TAC[REAL_ARITH `x > y <=> ~(x <= y)`] THEN
  REWRITE_TAC[SET_RULE `{x | ~p x} = UNIV DIFF {x | p x}`] THEN
  REWRITE_TAC[GSYM matrix_closed; MATRIX_CLOSED_HALFSPACE_LE]);;

let MATRIX_CONNECTED_IVT_HYPERPLANE = prove
 (`!s x y:real^N^M a b.
        matrix_connected s /\
        x IN s /\ y IN s /\ a mip x <= b /\ b <= a mip y
        ==> ?z. z IN s /\ a mip z = b`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [matrix_connected]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPECL
   [`{x:real^N^M | a mip x < b}`; `{x:real^N^M | a mip x > b}`]) THEN
  REWRITE_TAC[MATRIX_OPEN_HALFSPACE_LT; MATRIX_OPEN_HALFSPACE_GT] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY; SUBSET;
              IN_UNION; REAL_LT_LE; real_gt] THEN
  ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LE_ANTISYM]);;
  
let MATRIX_CONNECTED_IVT_COMPONENT = prove
 (`!s x y:real^N^M a i j.
        matrix_connected s /\ x IN s /\ y IN s /\
        (1 <= i /\ i <= dimindex(:M)) /\
        (1 <= j /\ j <= dimindex(:N)) /\ x$i$j <= a /\ a <= y$i$j
        ==> ?z. z IN s /\ z$i$j = a`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`s:real^N^M->bool`; `x:real^N^M`; `y:real^N^M`; `(mbasis i j):real^N^M`;
    `a:real`] MATRIX_CONNECTED_IVT_HYPERPLANE) THEN
  ASM_SIMP_TAC[MIP_BASIS]);;
*)

let MATRIX_CONTINUOUS_ON_R11_EQ_REAL = prove
 (`!s f:real^1^1->real^1^1. 
  f matrix_continuous_on s <=> 
    (\x. drop_drop (f (lift_lift x))) real_continuous_on {drop_drop x | x IN s}`,
  SIMP_TAC [matrix_continuous_on; real_continuous_on] THEN REPEAT GEN_TAC THEN 
  EQ_TAC THENL 
  [DISCH_THEN(fun th -> STRIP_TAC THEN STRIP_TAC THEN MP_TAC th) THEN 
   DISCH_THEN (MP_TAC o SPEC `lift_lift (x:real)`) THEN
   DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE [DROP2_SET]) THEN 
   ASM_SIMP_TAC [LIFT_DROP2] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN 
   DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN 
   ASM_SIMP_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN 
   STRIP_TAC THEN ASM_SIMP_TAC [] THEN X_GEN_TAC `m:real` THEN 
   FIRST_X_ASSUM (MP_TAC o SPEC `lift_lift (m:real)`) THEN 
   SIMP_TAC [LIFT_DROP2; MATRIX_DIST_LIFT2; matrix_dist] THEN 
   MESON_TAC [FNORM_REAL;DROP2_SUB; drop_drop];
   DISCH_THEN(fun th -> STRIP_TAC THEN STRIP_TAC THEN MP_TAC th) THEN 
   DISCH_THEN (MP_TAC o SPEC `drop_drop (x:real^1^1)`) THEN 
   DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE [GSYM DROP2_SET]) THEN 
   ASM_SIMP_TAC [] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN 
   DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN 
   ASM_SIMP_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN 
   STRIP_TAC THEN ASM_SIMP_TAC [] THEN X_GEN_TAC `m:real^1^1` THEN 
   FIRST_X_ASSUM (MP_TAC o SPEC `drop_drop (m:real^1^1)`) THEN 
   SIMP_TAC [GSYM DROP2_SET] THEN 
   SIMP_TAC [LIFT_DROP2; MATRIX_DIST_LIFT2; matrix_dist] THEN 
   MESON_TAC [FNORM_REAL;DROP2_SUB; drop_drop]]);;

let REAL_IVT = prove
(`!f:real->real a b y. 
   a <= b /\ f real_continuous_on real_interval[a,b] /\
        min (f a) (f b) <= y /\ y <= max (f a) (f b)
        ==> ?x. x IN real_interval [a,b] /\ f x = y`,
  REPEAT STRIP_TAC THEN 
  ASM_CASES_TAC `(f:real->real) a <= f b` THENL
  [MATCH_MP_TAC REAL_IVT_INCREASING THEN 
   ASM_SIMP_TAC [] THEN ASM_ARITH_TAC;
   MATCH_MP_TAC REAL_IVT_DECREASING THEN 
   ASM_SIMP_TAC [] THEN ASM_ARITH_TAC]);;
  
let REAL_CONTINUOUS_CONST_UNIQUE = prove
   (`!f:real->real A B c.  (!x. f x = A \/ f x = B) /\ (?x1. f x1 = A) /\
            (!a. f real_continuous (atreal a))
             ==> f(c) = A`,
   let lem = prove
   (`!f:real->real A B.  (!x. f x = A \/ f x = B) /\ (?x1. f x1 = A) /\
             (?x2. f x2 = B) /\ 
             (!a. f real_continuous (atreal a))
             ==> A = B`,
  ONCE_REWRITE_TAC [GSYM WITHINREAL_UNIV] THEN  
  REPEAT STRIP_TAC THEN 
  MP_TAC (SPECL [`f:real->real`;`min x1 x2:real`;`max x1 x2:real`;`(A + B) / &2 :real `] REAL_IVT) THEN ANTS_TAC THENL [REPEAT CONJ_TAC; ALL_TAC] THENL
  [REAL_ARITH_TAC; 
   MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN 
   SIMP_TAC [SUBSET_UNIV; REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN 
   ASM_SIMP_TAC [IN_UNIV]; 
   ASM_ARITH_TAC; 
   ASM_ARITH_TAC; 
   STRIP_TAC THEN 
   UNDISCH_TAC `!x. (f:real->real) x = A \/ f x = B` THEN 
   DISCH_THEN (MP_TAC o SPEC `x:real`) THEN 
   ASM_ARITH_TAC]) in
   MESON_TAC [lem]);;
   
let DET_EXP_MATRIX_CONTINUOUS_AT = prove
    (`!A:real^N^N x:real^1^1. 
    (\a:real^1^1. lift_lift(det (matrix_exp (drop_drop a %% A)))) 
                  matrix_continuous (matrix_at x)`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `(\a:real^1^1. lift_lift (det (matrix_exp (drop_drop a %% A)))) = 
            (\B:real^N^N. lift_lift (det B)) o (\z:real^1^1. matrix_exp (drop_drop z %% (A:real^N^N)))` SUBST1_TAC THENL
    [SIMP_TAC[o_DEF];ALL_TAC] THEN
    MATCH_MP_TAC MATRIX_CONTINUOUS_AT_COMPOSE THEN
    SIMP_TAC [DET_CONTINUOUS_AT;CONTINUOUS_AT_MATRIX_EXP]);;
    
let DET_EXP_REAL_CONTINUOUS_AT = prove
    (`!A:real^N^N x:real. 
    (\a. (det (matrix_exp (a %% A)))) 
                  real_continuous (atreal x)`,
    let matrix_continuous_at_real = SIMP_RULE [IN_UNIV; DROP2_UNIV; MATRIX_WITHIN_UNIV; WITHINREAL_UNIV] 
    (ISPEC `(:real^1^1)` 
    (SIMP_RULE [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
    MATRIX_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] 
    MATRIX_CONTINUOUS_ON_R11_EQ_REAL)) in
    let th1 = SIMP_RULE[LIFT_DROP2] (SIMP_RULE [matrix_continuous_at_real] 
              DET_EXP_MATRIX_CONTINUOUS_AT) in 
    SIMP_TAC[th1]);;

let INFMSUM_SUB = prove
    (`!s f:num->real^N^M g.
          msummable s f /\ msummable s g ==> 
            infmsum s (\n. (f(n) - g(n))) =  infmsum s f - infmsum s g`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INFMSUM_UNIQUE THEN
    MATCH_MP_TAC MSERIES_SUB THEN ASM_SIMP_TAC[MSUMS_INFSUM]);;

let SERIES_FNORMCONV_IMP_CONV = prove
    (`!s f:num->real^N^M.
          real_summable s (\x. fnorm (f(x))) ==> msummable s f`,
     SIMP_TAC[REAL_SUMMABLE_CAUCHY;MSUMMABLE_CAUCHY] THEN
     MESON_TAC[REAL_LET_TRANS;MSUM_FNORM;FINITE_INTER;FINITE_NUMSEG;
               REAL_ABS_REFL;SUM_POS_LE;FNORM_POS_LE]);;

let INFMSUM_FNORM = prove               
    (`!s f:num->real^N^M.
          real_summable s (\x. fnorm (f(x))) ==> 
              fnorm(infmsum s f) <=  real_infsum s (\x. fnorm (f(x)))`,
     let lem1 = REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS in
     let lem = ONCE_REWRITE_RULE 
           [TAUT `p ==> q ==> r <=> q ==> p ==> r`] lem1 in
     let fnorm_lem = SIMP_RULE [FINITE_NUMSEG;FINITE_INTER] (ISPECL [`f:num->real^N^M`;`s INTER (0..n)`] MSUM_FNORM) in         
     REPEAT STRIP_TAC THEN          
     MATCH_MP_TAC(ISPEC `sequentially` MATRIX_LIM_FNORM_UBOUND) THEN
     EXISTS_TAC `\n. msum(s INTER (0..n)) (f:num->real^N^M)` THEN
     REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
     SIMP_TAC[GSYM msums] THEN
     ASM_SIMP_TAC[MSUMS_INFSUM;SERIES_FNORMCONV_IMP_CONV] THEN
     EXISTS_TAC `N:num` THEN REPEAT STRIP_TAC THEN
     W(MP_TAC o PART_MATCH lhand fnorm_lem o lhand o snd) THEN 
     MATCH_MP_TAC lem THEN MATCH_MP_TAC REAL_PARTIAL_SUMS_LE_INFSUM THEN
     ASM_SIMP_TAC[FNORM_POS_LE]);;

let REAL_SUMMABLE_FNORM_EXP = prove
    (`!A:real^N^N n:num. 
    real_summable (from n) (\n. fnorm(&1 / &(FACT n) %% A matrix_pow n))`,
    REPEAT GEN_TAC THEN
    ONCE_SIMP_TAC[ISPECL [`SUC n`;`n:num`;`f:num->real`]
                         REAL_SUMMABLE_FROM_ELSEWHERE_EQ] THEN
    MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `(\n. abs (&1 / &(FACT n)) * fnorm (A:real^N^N) pow n)` THEN
    SIMP_TAC[REAL_ABS_MUL;REAL_ABS_ABS;REAL_ABS_FNORM;FNORM_MUL] THEN
    ONCE_REWRITE_TAC[CONJ_ACI] THEN CONJ_TAC THENL
    [SIMP_TAC[from;IN_ELIM_THM] THEN
     EXISTS_TAC `N:num` THEN REPEAT STRIP_TAC THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN
     ASM_MESON_TAC[ARITH_RULE `~(SUC n = 0) /\ SUC n <= m ==> 1 <= m`;
                  FNORM_MATRIX_POW_LE;REAL_ABS_POS;NOT_SUC]; ALL_TAC] THEN
    SIMP_TAC[REAL_SUMMABLE_FROM_ELSEWHERE_EQ] THEN
    SIMP_TAC[REAL_ABS_DIV;REAL_ABS_1;FACT_LT;
             REAL_ARITH `0 < x ==> abs (&x) = &x`;
             REAL_ARITH `&1 / b * a = a / b`] THEN
    SIMP_TAC[REAL_SUMMABLE_COMPLEX;o_DEF;CX_DIV;CX_POW] THEN
    SIMP_TAC[SIMP_RULE [cexp;SUMS_INFSUM;SUMMABLE_FROM_ELSEWHERE_EQ] CEXP_CONVERGES]);;

let REAL_SUMMABLE_FNORM_EXP_SUB = prove
    (`!A:real^N^N B n:num. 
     real_summable (from n) 
                   (\n. fnorm((&1 / &(FACT n) %% A matrix_pow n)
                        - (&1 / &(FACT n) %% B matrix_pow n)))`,
     REPEAT GEN_TAC THEN
     MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
     EXISTS_TAC `(\n. fnorm(&1 / &(FACT n) %% (A:real^N^N) matrix_pow n)
                      +  fnorm(&1 / &(FACT n) %% (B:real^N^N) matrix_pow n))` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_SUMMABLE_ADD THEN
      SIMP_TAC[REAL_SUMMABLE_FNORM_EXP];ALL_TAC] THEN
     SIMP_TAC[REAL_ABS_FNORM;MATRIX_SUB] THEN
     MESON_TAC[FNORM_TRIANGLE;FNORM_NEG]);;
    
let MSUMMABLE_EXP = prove    
    (`!A:real^N^N n:num. msummable (from n) (\n. &1 / &(FACT n) %% A matrix_pow n)`,
    SIMP_TAC[REAL_SUMMABLE_FNORM_EXP;SERIES_FNORMCONV_IMP_CONV]);;
    
let SERIES_MLINEAR = prove
 (`!f h l s. (f msums l) s /\ mlinear h ==> ((\n. h(f n)) msums h l) s`,
  SIMP_TAC[msums; MATRIX_LIM_LINEAR; FINITE_INTER; FINITE_NUMSEG;
           GSYM(REWRITE_RULE[o_DEF] MLINEAR_MSUM)]);;    

let MSUMMABLE_RESTRICT = prove
 (`!f:num->real^N^M k.
        msummable (:num) (\n. if n IN k then f(n) else mat 0) <=>
        msummable k f`,
  REWRITE_TAC[msummable; MSERIES_RESTRICT]);;
           
(* ------------------------------------------------------------------------- *)
(* Similar combining theorems for infmsum.                                    *)
(* ------------------------------------------------------------------------- *)

let INFMSUM_MLINEAR = prove
 (`!f h s. msummable s f /\ mlinear h
           ==> infmsum s (\n. h(f n)) = h(infmsum s f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INFMSUM_UNIQUE THEN
  MATCH_MP_TAC SERIES_MLINEAR THEN ASM_REWRITE_TAC[MSUMS_INFSUM]);;

let INFMSUM_0 = prove
 (`infmsum s (\i. mat 0) = mat 0`,
  MATCH_MP_TAC INFMSUM_UNIQUE THEN REWRITE_TAC[MSERIES_0]);;

let INFMSUM_ADD = prove
 (`!x y s. msummable s x /\ msummable s y
           ==> infmsum s (\i. x i + y i) = infmsum s x + infmsum s y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INFMSUM_UNIQUE THEN
  MATCH_MP_TAC MSERIES_ADD THEN ASM_REWRITE_TAC[MSUMS_INFSUM]);;

let INFMSUM_SUB = prove
 (`!x y s. msummable s x /\ msummable s y
           ==> infmsum s (\i. x i - y i) = infmsum s x - infmsum s y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INFMSUM_UNIQUE THEN
  MATCH_MP_TAC MSERIES_SUB THEN ASM_REWRITE_TAC[MSUMS_INFSUM]);;

let INFMSUM_CMUL = prove
 (`!s x c. msummable s x ==> infmsum s (\n. c %% x n) = c %% infmsum s x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INFMSUM_UNIQUE THEN
  MATCH_MP_TAC MSERIES_CMUL THEN ASM_REWRITE_TAC[MSUMS_INFSUM]);;

let INFMSUM_NEG = prove
 (`!s x. msummable s x ==> infmsum s (\n. --(x n)) = --(infmsum s x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INFMSUM_UNIQUE THEN
  MATCH_MP_TAC MSERIES_NEG THEN ASM_REWRITE_TAC[MSUMS_INFSUM]);;

let INFMSUM_EQ = prove
 (`!f g k. msummable k f /\ msummable k g /\ (!x. x IN k ==> f x = g x)
           ==> infmsum k f = infmsum k g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[infmsum] THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[MSUMS_EQ; MSUMS_INFSUM]);;

let INFMSUM_RESTRICT = prove
 (`!k a:num->real^N^M.
        infmsum (:num) (\n. if n IN k then a n else mat 0) = infmsum k a`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:num->real^N^M`; `k:num->bool`] MSUMMABLE_RESTRICT) THEN
  ASM_CASES_TAC `msummable k (a:num->real^N^M)` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC INFMSUM_UNIQUE THEN
    ASM_REWRITE_TAC[MSERIES_RESTRICT; MSUMS_INFSUM];
    RULE_ASSUM_TAC(REWRITE_RULE[msummable; NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[infmsum]]);;
    
let INFMSUM_EVEN = prove
 (`!f:num->real^N^M n.
        infmsum (from n) f =
        infmsum (from (2 * n)) (\i. if EVEN i then f(i DIV 2) else mat 0)`,
  REWRITE_TAC[infmsum; GSYM MSERIES_EVEN]);;

let INFMSUM_ODD = prove
 (`!f:num->real^N^M n.
        infmsum (from n) f =
        infmsum (from (2 * n + 1)) (\i. if ODD i then f(i DIV 2) else mat 0)`,
  REWRITE_TAC[infmsum; GSYM MSERIES_ODD]);;

(* ------------------------------------------------------------------------- *)
(* The continuous function like determinant, transp.                         *)
(* ------------------------------------------------------------------------- *)

let DET_CONTINUOUS_ON = prove
    (`!s. (\A:real^N^N. lift_lift (det A)) matrix_continuous_on s`,
     SIMP_TAC[MATRIX_CONTINUOUS_AT_IMP_CONTINUOUS_ON;DET_CONTINUOUS_AT]);;
     
let TRANSP_CONTINUOUS_AT = prove
    (`!x:real^N^M. transp matrix_continuous (matrix_at x)`,
     GEN_TAC THEN MATCH_MP_TAC MLINEAR_CONTINUOUS_AT THEN
     SIMP_TAC[mlinear;TRANSP_MATRIX_ADD;TRANSP_MATRIX_CMUL]);;    

let TRANSP_CONTINUOUS_ON = prove
    (`!s. transp matrix_continuous_on s`,
     SIMP_TAC[MATRIX_CONTINUOUS_AT_IMP_CONTINUOUS_ON;TRANSP_CONTINUOUS_AT]);; 

let MATRIX_CLOSED_DET_CONSTANT = prove
    (`!a:real. matrix_closed {(A:real^N^N) | det A = a}`,
    GEN_TAC THEN
    MP_TAC(ISPECL [`(\A:real^N^N. lift_lift (det A))`;`(:real^N^N)`;`lift_lift(a:real)`] MATRIX_CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT) THEN
    SIMP_TAC[DET_CONTINUOUS_ON;SUBTOPOLOGY_UNIV;IN_UNIV;GSYM MATRIX_CLOSED_IN;LIFT2_EQ]);;
     
let MATRIX_CLOSED_ORTHOGONAL_MATRIX = prove
    (`!A:real^N^N. matrix_closed {A:real^N^N | orthogonal_matrix A}`,
    let lem1 = prove    
    (`!x:real^N^N. 
       (\A:real^N^N. transp (A) ** A - mat 1) matrix_continuous (matrix_at x)`,
    GEN_TAC THEN MATCH_MP_TAC MATRIX_CONTINUOUS_SUB THEN
    SIMP_TAC[MATRIX_CONTINUOUS_CONST] THEN
    MATCH_MP_TAC MATRIX_CONTINUOUS_MUL THEN
    SIMP_TAC[TRANSP_CONTINUOUS_AT;MATRIX_CONTINUOUS_AT_ID]) in
    let lem2 = prove  
    (`!s. (\A:real^N^N. transp (A) ** A - mat 1) matrix_continuous_on s`,
    SIMP_TAC[MATRIX_CONTINUOUS_AT_IMP_CONTINUOUS_ON;lem1]) in
    GEN_TAC THEN
    MP_TAC(ISPECL [`(\A:real^N^N. transp (A) ** A - mat 1)`;`(:real^N^N)`;`(mat 0):real^N^N`] MATRIX_CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT) THEN
    SIMP_TAC[lem2;SUBTOPOLOGY_UNIV;IN_UNIV;GSYM MATRIX_CLOSED_IN;ORTHOGONAL_MATRIX;MATRIX_SUB_EQ]);;

(* ------------------------------------------------------------------------- *)
(* general linear group                                                      *)
(* ------------------------------------------------------------------------- *)


make_overloadable "general_linear_group" `:A`;;

overload_interface ("general_linear_group", `real_general_linear_group:real^N^N->(real^N^N)group`);;

overload_interface ("general_linear_group", `complex_general_linear_group:complex^N^N->(complex^N^N)group`);;

let real_general_linear_group = new_definition
    `real_general_linear_group (a:real^N^N) = group ({A:real^N^N | invertible A}, mat 1:real^N^N, matrix_inv, matrix_mul)`;;
    
let complex_general_linear_group = new_definition
    `complex_general_linear_group (a:complex^N^N) = group ({A:complex^N^N | cinvertible A}, cmat 1:complex^N^N, cmatrix_inv, cmatrix_mul)`;;
    
let general_linear_group = prove
    (`(!a:real^N^N. real_general_linear_group a = group ({A:real^N^N | invertible A}, mat 1:real^N^N, matrix_inv, matrix_mul)) /\
      (!a:complex^N^N. complex_general_linear_group a = group ({A:complex^N^N | cinvertible A}, cmat 1:complex^N^N, cmatrix_inv, cmatrix_mul))`,
    SIMP_TAC[real_general_linear_group;complex_general_linear_group]);;

let REAL_GENERAL_LINEAR_GROUP = prove
    (`(!a:real^N^N. group_carrier(general_linear_group a) = {A:real^N^N | invertible A})    /\
    (!a:real^N^N. group_id(general_linear_group a) = mat 1:real^N^N) /\
    (!a:real^N^N. group_inv(general_linear_group a) = matrix_inv) /\
    (!a:real^N^N. group_mul(general_linear_group a) = matrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl real_general_linear_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM real_general_linear_group] THEN SIMP_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[INVERTIBLE_I;INVERTIBLE_MATRIX_INV;
             MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RID;MATRIX_INV;
             INVERTIBLE_MATRIX_MUL] THEN
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);; 
    
let REAL_GENERAL_LINEAR_OPEN_IN_MATRIX_SPACE = prove
    (`!g:real^N^N. open_in matrix_space (group_carrier (general_linear_group g))`,
    GEN_TAC THEN 
    REWRITE_TAC[GSYM MATRIX_OPEN_IN;REAL_GENERAL_LINEAR_GROUP] THEN 
    REWRITE_TAC [SET_RULE `{A | invertible A} = (:real^N^N) DIFF {A | ~(invertible A)}`;GSYM matrix_closed] THEN
    REWRITE_TAC[GSYM DET_EQ_0;MATRIX_CLOSED_DET_CONSTANT]);;

let COMPLEX_GENERAL_LINEAR_GROUP = prove
    (`(!a:complex^N^N. group_carrier(general_linear_group a) = {A:complex^N^N | cinvertible A})    /\
    (!a:complex^N^N. group_id(general_linear_group a) = cmat 1:complex^N^N) /\
    (!a:complex^N^N. group_inv(general_linear_group a) = cmatrix_inv) /\
    (!a:complex^N^N. group_mul(general_linear_group a) = cmatrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl complex_general_linear_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM complex_general_linear_group] THEN SIMP_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[CINVERTIBLE_I;CINVERTIBLE_MATRIX_INV_IMP;
             CMATRIX_MUL_ASSOC;CMATRIX_MUL_LID;CMATRIX_MUL_RID;CMATRIX_INV;
             CINVERTIBLE_MATRIX_MUL] THEN
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);; 
    
let GENERAL_LINEAR_GROUP = prove
    (`(!a:real^N^N. group_carrier(general_linear_group a) = {A:real^N^N | invertible A})    /\
    (!a:real^N^N. group_id(general_linear_group a) = mat 1:real^N^N) /\
    (!a:real^N^N. group_inv(general_linear_group a) = matrix_inv) /\
    (!a:real^N^N. group_mul(general_linear_group a) = matrix_mul) /\
    (!a:complex^N^N. group_carrier(general_linear_group a) = {A:complex^N^N | cinvertible A})    /\
    (!a:complex^N^N. group_id(general_linear_group a) = cmat 1:complex^N^N) /\
    (!a:complex^N^N. group_inv(general_linear_group a) = cmatrix_inv) /\
    (!a:complex^N^N. group_mul(general_linear_group a) = cmatrix_mul)`,
    SIMP_TAC[REAL_GENERAL_LINEAR_GROUP;COMPLEX_GENERAL_LINEAR_GROUP]);;

(* ------------------------------------------------------------------------- *)
(* topological group                                                         *)
(* ------------------------------------------------------------------------- *)  

let HAUSDORFF_SPACE_MATRIX_SPACE = prove
 (`hausdorff_space (matrix_space:(real^N^M)topology)`,
  REWRITE_TAC[GSYM MTOPOLOGY_MATRIX_SPACE_METRIC; HAUSDORFF_SPACE_MTOPOLOGY]);;
  
let HAUSDORFF_SPACE_GLG = prove
    (`!a:real^N^N. hausdorff_space (subtopology matrix_space (group_carrier (general_linear_group a)))`,
    SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY;HAUSDORFF_SPACE_MATRIX_SPACE]);; 
    
(* ------------------------------------------------------------------------- *)
(* matrix lie group                                                        *)
(* ------------------------------------------------------------------------- *)
  
let ismlg_real = define
    `ismlg_real (s:real^N^N->bool) <=>
        s subgroup_of (group ({A:real^N^N | invertible A}, mat 1:real^N^N, matrix_inv, matrix_mul))/\
        (!x:num->real^N^N l:real^N^N. (!n. x(n) IN s) /\ (x ->-> l) sequentially ==> (l IN s \/ ~(invertible l)))`;;
        
let ismlg_complex = define
     `ismlg_complex (s:complex^N^N->bool) <=>
     s subgroup_of (group ({A:complex^N^N | cinvertible A}, cmat 1:complex^N^N, cmatrix_inv, cmatrix_mul)) /\
     (!x:num->complex^N^N l. (!n. x(n) IN s) /\ ((x ->-> l) sequentially) ==> (l IN s \/ ~(cinvertible l)))`;;
    
let ismlg = define
    `ismlg (s:complex^N^N->bool) <=>
    if IMAGE (Cx_matrix o Re_matrix) s = s
    then ismlg_real (IMAGE Re_matrix s)
    else ismlg_complex s`;;
    
let IMAGE_CX_MATRIX_RE_MATRIX_IMAGE = prove
    (`!t:real^N^M->bool. 
        IMAGE (Cx_matrix o Re_matrix) (IMAGE Cx_matrix t) = 
        IMAGE Cx_matrix t`,
    SIMP_TAC[GSYM IMAGE_o] THEN
    SIMP_TAC[o_DEF;RE_MATRIX_CX_MATRIX;ETA_AX]);;
    
let IMAGE_RE_MATRIX_CX_MATRIX = prove
    (`!t:real^N^M->bool. IMAGE (Re_matrix) (IMAGE Cx_matrix t)  = t`,
    SIMP_TAC[GSYM IMAGE_o] THEN
    SIMP_TAC[o_DEF;RE_MATRIX_CX_MATRIX;GSYM I_DEF;IMAGE_I]);;
    
let CX_INVERTIBLE = prove
    (`!s:complex^N^M->bool. 
    IMAGE (Cx_matrix o Re_matrix) s = s /\ 
    (!x. x IN IMAGE Re_matrix s ==> invertible x)
    ==> (!x. x IN s ==> cinvertible x)`,
    SIMP_TAC[IN_IMAGE;GSYM LEFT_FORALL_IMP_THM;EXTENSION;o_DEF] THEN
    GEN_TAC THEN 
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ONCE_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`Re_matrix (x':complex^N^M)`;`(x':complex^N^M)`]) THEN
    ASM_SIMP_TAC[invertible;cinvertible] THEN
    SIMP_TAC[EXISTS_CMATRIX;CMATRIX_MUL;CMATRIX_EQ_ALT;RE_MATRIX;IM_MATRIX;RE_MATRIX_CX_MATRIX;IM_MATRIX_CX_MATRIX;CMAT] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`A':real^M^N`;`mat 0 :real^M^N`] THEN
    ASM_SIMP_TAC[MATRIX_MUL_LZERO;MATRIX_MUL_RZERO;MATRIX_SUB_RZERO;MATRIX_ADD_LID;MATRIX_MUL_RID]);;
    
let RE_CINVERTIBLE = prove
    (`!s:real^N^M->bool. 
    (!x. x IN IMAGE Cx_matrix s ==> cinvertible x)
    ==> (!x. x IN s ==> invertible x)`,
    SIMP_TAC[IN_IMAGE;GSYM LEFT_FORALL_IMP_THM;EXTENSION] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`Cx_matrix (x:real^N^M)`;`(x:real^N^M)`]) THEN
    ASM_SIMP_TAC[invertible;cinvertible] THEN
    SIMP_TAC[EXISTS_CMATRIX;CMATRIX_MUL;CMATRIX_EQ_ALT;RE_MATRIX;IM_MATRIX;RE_MATRIX_CX_MATRIX;IM_MATRIX_CX_MATRIX;CMAT] THEN
    SIMP_TAC[MATRIX_MUL_LZERO;MATRIX_MUL_RZERO;MATRIX_SUB_RZERO;MATRIX_ADD_LID;MATRIX_ADD_RID] THEN
    MESON_TAC[]);;
    
let CX_MAT = prove
    (`!s:complex^N^M->bool. 
    IMAGE (Cx_matrix o Re_matrix) s = s /\
    (mat 1) IN IMAGE Re_matrix s
    ==> (cmat 1) IN s`,
    SIMP_TAC[IN_IMAGE;GSYM LEFT_FORALL_IMP_THM;EXTENSION;o_DEF] THEN
    GEN_TAC THEN 
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ONCE_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `x:complex^N^M` THEN ASM_SIMP_TAC[CMAT]);;
    
let RE_CMAT = prove
    (`!s:real^N^M->bool. (cmat 1) IN IMAGE Cx_matrix s
    ==> (mat 1) IN s`,
    SIMP_TAC[IN_IMAGE;GSYM LEFT_FORALL_IMP_THM;EXTENSION] THEN
    SIMP_TAC[CMAT;CMATRIX_EQ_ALT;RE_MATRIX_CX_MATRIX;IM_MATRIX_CX_MATRIX]);;
    
let CX_MATRIX_INV = prove
    (`!s:complex^N^N->bool. 
    IMAGE (Cx_matrix o Re_matrix) s = s /\
    IMAGE Re_matrix s SUBSET {A | invertible A} /\
    (!x. x IN IMAGE Re_matrix s ==> (matrix_inv x) IN IMAGE Re_matrix s)
    ==> (!x. x IN s ==> (cmatrix_inv x) IN s)`,
    SIMP_TAC[IN_IMAGE;GSYM LEFT_FORALL_IMP_THM;EXTENSION;o_DEF;SUBSET;IN_ELIM_THM] THEN
    GEN_TAC THEN 
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ONCE_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`Re_matrix (x':complex^N^N)`;`(x':complex^N^N)`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `A:complex^N^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `A:complex^N^N` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC CMATRIX_INV_UNIQUE THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`Re_matrix (x':complex^N^N)`;`(x':complex^N^N)`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN    
    SIMP_TAC[CMATRIX_MUL;CMATRIX_EQ_ALT;RE_MATRIX;IM_MATRIX;RE_MATRIX_CX_MATRIX;IM_MATRIX_CX_MATRIX;CMAT] THEN
    ASM_SIMP_TAC[MATRIX_MUL_LZERO;MATRIX_MUL_RZERO;MATRIX_SUB_RZERO;MATRIX_ADD_LID;MATRIX_MUL_RID;MATRIX_INV]);;
    
let RE_CMATRIX_INV = prove
    (`!s:real^N^N->bool. 
    IMAGE Cx_matrix s SUBSET {A | cinvertible A} /\
    (!x. x IN IMAGE Cx_matrix s ==> (cmatrix_inv x) IN IMAGE Cx_matrix s)
    ==> (!x. x IN s ==> (matrix_inv x) IN s)`,
    SIMP_TAC[IN_IMAGE;GSYM LEFT_FORALL_IMP_THM;EXTENSION;SUBSET;IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`Cx_matrix (x:real^N^N)`;`(x:real^N^N)`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `A:real^N^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `matrix_inv x = A:real^N^N` SUBST1_TAC THENL
    [MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`Cx_matrix (x:real^N^N)`;`(x:real^N^N)`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN 
    DISCH_THEN(MP_TAC o MATCH_MP CMATRIX_INV) THEN
    ASM_SIMP_TAC[CMATRIX_MUL;CMATRIX_EQ_ALT;RE_MATRIX;IM_MATRIX;RE_MATRIX_CX_MATRIX;IM_MATRIX_CX_MATRIX;CMAT] THEN
    SIMP_TAC[MATRIX_MUL_LZERO;MATRIX_MUL_RZERO;MATRIX_SUB_RZERO;MATRIX_ADD_LID;MATRIX_ADD_RID];ALL_TAC] THEN
    ASM_SIMP_TAC[]);;
      
let CX_MATRIX_MUL = prove
    (`!s:complex^N^N->bool. 
    IMAGE (Cx_matrix o Re_matrix) s = s /\
    (!x y. x IN IMAGE Re_matrix s /\ y IN IMAGE Re_matrix s
      ==> x ** y IN IMAGE Re_matrix s)
    ==> (!x y. x IN s /\ y IN s ==> x ** y IN s)`,
    SIMP_TAC[IN_IMAGE;GSYM LEFT_FORALL_IMP_THM;EXTENSION;o_DEF;LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
    GEN_TAC THEN 
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ONCE_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`Re_matrix (x':complex^N^N)`;`Re_matrix (x'':complex^N^N)`;`(x':complex^N^N)`;`(x'':complex^N^N)`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `A:complex^N^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `A:complex^N^N` THEN ASM_SIMP_TAC[] THEN 
    SIMP_TAC[CMATRIX_MUL;CMATRIX_EQ_ALT;RE_MATRIX;IM_MATRIX;RE_MATRIX_CX_MATRIX;IM_MATRIX_CX_MATRIX] THEN
    SIMP_TAC[MATRIX_MUL_LZERO;MATRIX_MUL_RZERO;MATRIX_SUB_RZERO;MATRIX_ADD_LID]);;
    
let RE_CMATRIX_MUL = prove
    (`!s:real^N^N->bool.
    (!x y. x IN IMAGE Cx_matrix s /\ y IN IMAGE Cx_matrix s
      ==> x ** y IN IMAGE Cx_matrix s)
    ==> (!x y. x IN s /\ y IN s ==> x ** y IN s)`,
    SIMP_TAC[IN_IMAGE;GSYM LEFT_FORALL_IMP_THM;EXTENSION;LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`Cx_matrix (x:real^N^N)`;`Cx_matrix (y:real^N^N)`;`(x:real^N^N)`;`(y:real^N^N)`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN
    SIMP_TAC[CMATRIX_MUL;CMATRIX_EQ_ALT;RE_MATRIX;IM_MATRIX;RE_MATRIX_CX_MATRIX;IM_MATRIX_CX_MATRIX] THEN
    SIMP_TAC[MATRIX_MUL_LZERO;MATRIX_MUL_RZERO;MATRIX_SUB_RZERO;MATRIX_ADD_LID] THEN
    MESON_TAC[]);;
    
let mlg_tybij_th = prove
    (`?s:complex^N^N->bool. ismlg s`,
    EXISTS_TAC `IMAGE Cx_matrix {A:real^N^N | invertible A}` THEN
    SIMP_TAC[ismlg;IMAGE_CX_MATRIX_RE_MATRIX_IMAGE;IMAGE_RE_MATRIX_CX_MATRIX] THEN
    SIMP_TAC[ismlg_real] THEN
    CONJ_TAC THENL 
    [SIMP_TAC[GSYM GENERAL_LINEAR_GROUP;CARRIER_SUBGROUP_OF;
              GSYM general_linear_group];
    SET_TAC[]]);;

let mlg_tybij =
    new_type_definition "mlg" ("mlg","mlg_set") mlg_tybij_th;;

let ISMLG_MLG_SET = prove
    (`!G:(N)mlg. ismlg (mlg_set G)`,
    SIMP_TAC[mlg_tybij]);;
 
let MLG_EQ = prove
 (`!G H:(N)mlg. G = H <=> mlg_set G = mlg_set H`,
  MESON_TAC[CONJUNCT1 mlg_tybij]);;
  
let MLG_SUBGROUP_OF_GLG = prove  
    (`(!G:(N)mlg a. (mlg_set G) subgroup_of (general_linear_group a)) /\
    (!G:(N)mlg a. IMAGE (Cx_matrix o Re_matrix) (mlg_set G) = (mlg_set G) 
    ==> (IMAGE Re_matrix (mlg_set G)) subgroup_of (general_linear_group a))`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC (ISPEC `G:(N)mlg` ISMLG_MLG_SET) THEN
    SIMP_TAC[ismlg;ismlg_complex;ismlg_real] THEN
    COND_CASES_TAC THENL
    [FIRST_ASSUM (SUBST1_TAC o SYM) THEN
     INTRO_TAC "sub conv" THEN ASM_SIMP_TAC[] THEN
     USE_THEN "sub" MP_TAC THEN
     SIMP_TAC[GSYM IMAGE_o;GSYM general_linear_group] THEN
     SIMP_TAC[o_DEF;RE_MATRIX_CX_MATRIX;GSYM I_DEF;ETA_AX] THEN
     SIMP_TAC[subgroup_of;GENERAL_LINEAR_GROUP] THEN
     ASM_SIMP_TAC[CX_MAT;CX_MATRIX_INV;CX_MATRIX_MUL] THEN
     SIMP_TAC[SUBSET;IN_ELIM_THM] THEN
     ASM_MESON_TAC[CX_INVERTIBLE];ALL_TAC] THEN
     ASM_MESON_TAC[GSYM general_linear_group]);; 
 
let mlg_group = new_definition
    `(mlg_group:(N)mlg->(complex^N^N)group) G =
    group(mlg_set G, cmat 1:complex^N^N, cmatrix_inv, cmatrix_mul)`;;
    
let MLG_GROUP = prove
    (`(!G:(N)mlg. group_carrier(mlg_group G) = mlg_set G) /\
     (!G:(N)mlg. group_id(mlg_group G) = cmat 1) /\
     (!G:(N)mlg. group_inv(mlg_group G) = cmatrix_inv) /\
     (!G:(N)mlg. group_mul(mlg_group G) = cmatrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl mlg_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM mlg_group] THEN
    SIMP_TAC[SIMP_RULE [subgroup_of;GENERAL_LINEAR_GROUP] MLG_SUBGROUP_OF_GLG;CMATRIX_MUL_ASSOC;CMATRIX_MUL_LID;CMATRIX_MUL_RID] THEN
    ANTS_TAC THENL
    [MESON_TAC[SIMP_RULE [subgroup_of;GENERAL_LINEAR_GROUP;SUBSET] MLG_SUBGROUP_OF_GLG;CMATRIX_INV;IN_ELIM_THM];ALL_TAC] THEN
    SIMP_TAC[group_carrier;group_id;group_inv;group_mul]);;
    
let group_rtoc = new_definition
    `group_rtoc (G:(real^N^N)group) = group(IMAGE Cx_matrix (group_carrier G),cmat 1:complex^N^N, cmatrix_inv, cmatrix_mul)`;;

let GROUP_RTOC = prove
    (`!G:(real^N^N)group a. 
    group_carrier G subgroup_of general_linear_group a /\
    group_id G = mat 1 /\ group_inv G = matrix_inv /\ group_mul G = matrix_mul ==>
    (group_carrier(group_rtoc G) = IMAGE Cx_matrix (group_carrier G) /\
     group_id(group_rtoc G) = cmat 1 /\
     group_inv(group_rtoc G) = cmatrix_inv /\
     group_mul(group_rtoc G) = cmatrix_mul)`,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl group_rtoc)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM group_rtoc] THEN
    SIMP_TAC[CMATRIX_MUL_ASSOC;CMATRIX_MUL_LID;CMATRIX_MUL_RID] THEN
    ANTS_TAC THENL
    [MP_TAC (ISPEC `IMAGE Cx_matrix (group_carrier (G:(real^N^N)group))` CX_MAT) THEN
    MP_TAC (ISPEC `IMAGE Cx_matrix (group_carrier (G:(real^N^N)group))` CX_MATRIX_INV) THEN
    MP_TAC (ISPEC `IMAGE Cx_matrix (group_carrier (G:(real^N^N)group))` CX_MATRIX_MUL) THEN
    MP_TAC (ISPEC `IMAGE Cx_matrix (group_carrier (G:(real^N^N)group))` CX_INVERTIBLE) THEN
    SIMP_TAC[GSYM IMP_CONJ;GSYM CONJ_ASSOC] THEN
    SIMP_TAC[IMAGE_CX_MATRIX_RE_MATRIX_IMAGE;IMAGE_RE_MATRIX_CX_MATRIX] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [subgroup_of]) THEN
    ASM_SIMP_TAC[GENERAL_LINEAR_GROUP;CMATRIX_INV;SUBSET;IN_ELIM_THM];ALL_TAC] THEN
    SIMP_TAC[group_carrier;group_id;group_inv;group_mul]);;
    
let group_ctor = new_definition
    `group_ctor (G:(complex^N^N)group) = group(IMAGE Re_matrix (group_carrier G),mat 1:real^N^N, matrix_inv, matrix_mul)`;;
    
let GROUP_CTOR = prove
    (`!G:(complex^N^N)group a. 
    IMAGE (Cx_matrix o Re_matrix) (group_carrier G) = (group_carrier G) /\
    group_carrier G subgroup_of general_linear_group a /\
    group_id G = cmat 1 /\ group_inv G = cmatrix_inv /\ group_mul G = cmatrix_mul ==>
    (group_carrier(group_ctor G) = IMAGE Re_matrix (group_carrier G) /\
     group_id(group_ctor G) = mat 1 /\
     group_inv(group_ctor G) = matrix_inv /\
     group_mul(group_ctor G) = matrix_mul)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl group_ctor)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM group_ctor] THEN
    SIMP_TAC[MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RID] THEN
    ANTS_TAC THENL
    [MP_TAC (ISPEC `IMAGE Re_matrix (group_carrier (G:(complex^N^N)group))` RE_CMAT) THEN
    MP_TAC (ISPEC `IMAGE Re_matrix (group_carrier (G:(complex^N^N)group))` RE_CMATRIX_INV) THEN
    MP_TAC (ISPEC `IMAGE Re_matrix (group_carrier (G:(complex^N^N)group))` RE_CMATRIX_MUL) THEN
    MP_TAC (ISPEC `IMAGE Re_matrix (group_carrier (G:(complex^N^N)group))` RE_CINVERTIBLE) THEN
    SIMP_TAC[GSYM IMP_CONJ;GSYM CONJ_ASSOC;GSYM IMAGE_o] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [subgroup_of]) THEN
    ASM_SIMP_TAC[GENERAL_LINEAR_GROUP;MATRIX_INV;SUBSET;IN_ELIM_THM];ALL_TAC] THEN
    SIMP_TAC[group_carrier;group_id;group_inv;group_mul]);;

make_overloadable "group_mlg" `:A`;;

overload_interface("group_mlg",`real_group_mlg:(real^N^N)group->(N)mlg`);;
overload_interface("group_mlg",`complex_group_mlg:(complex^N^N)group->(N)mlg`);;
    
let real_group_mlg = new_definition
    `(real_group_mlg:(real^N^N)group->(N)mlg) G = mlg(IMAGE Cx_matrix (group_carrier G))`;;
    
let complex_group_mlg = new_definition
    `(complex_group_mlg:(complex^N^N)group->(N)mlg) G = mlg(group_carrier G)`;;

let group_mlg = prove
 (`(!G:(real^N^N)group. real_group_mlg G = mlg(IMAGE Cx_matrix (group_carrier G))) /\
 (!G:(complex^N^N)group. complex_group_mlg G = mlg(group_carrier G))`,
  REWRITE_TAC[real_group_mlg; complex_group_mlg]);; 
  
let MLG_GROUP_BIJ = prove
    (`(!G. group_mlg(mlg_group G) = G) /\
    (!G:(complex^N^N)group. ismlg(group_carrier G) /\ group_id G = cmat 1 /\ group_inv G = cmatrix_inv /\ group_mul G = cmatrix_mul <=> mlg_group(group_mlg G) = G) /\
    (!G:(real^N^N)group. ismlg_real(group_carrier G) /\ group_id G = mat 1 /\ group_inv G = matrix_inv /\ group_mul G = matrix_mul ==> mlg_group(group_mlg G) = group_rtoc G)`,
    SIMP_TAC[GROUPS_EQ;MLG_GROUP;group_mlg;mlg_tybij] THEN
    SIMP_TAC[EQ_SYM_EQ] THEN
    SIMP_TAC[ismlg_real;SIMP_RULE [general_linear_group] GROUP_RTOC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (fst(EQ_IMP_RULE(ISPEC `IMAGE Cx_matrix (group_carrier (G:(real^N^N)group))` (CONJUNCT2 mlg_tybij)))) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ismlg;IMAGE_CX_MATRIX_RE_MATRIX_IMAGE;IMAGE_RE_MATRIX_CX_MATRIX;ismlg_real];ALL_TAC] THEN
    SIMP_TAC[]);;

let IMAGE_RE_INVERTIBLE_IMP = prove 
    (`IMAGE (Cx_matrix o Re_matrix) {A:complex^N^N | cinvertible A} = {A | cinvertible A} ==> IMAGE Re_matrix {A:complex^N^N | cinvertible A} = {A | invertible A}`,
    SIMP_TAC[EXTENSION;IN_ELIM_THM;IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Cx_matrix (x:real^N^N)`) THEN
    SIMP_TAC[invertible;cinvertible] THEN
    SIMP_TAC[EXISTS_CMATRIX;CMATRIX_MUL;CMATRIX_EQ_ALT;RE_MATRIX;IM_MATRIX;RE_MATRIX_CX_MATRIX;IM_MATRIX_CX_MATRIX;CMAT;o_DEF] THEN
    SIMP_TAC[MATRIX_MUL_LZERO;MATRIX_MUL_RZERO;MATRIX_SUB_RZERO;MATRIX_ADD_LID;MATRIX_ADD_RID] THEN
    STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
    [EXISTS_TAC `x':real^N^N`;
     MAP_EVERY EXISTS_TAC [`A':real^N^N`;`mat 0 :real^N^N`]] THEN
    ASM_SIMP_TAC[MATRIX_MUL_LZERO;MATRIX_MUL_RZERO]);;
    
let GENERAL_LINEAR_GROUP_ISMLG = prove
    (`(!g:complex^N^N. ismlg (group_carrier (general_linear_group g))) /\
      (!g:real^N^N. ismlg (IMAGE Cx_matrix (group_carrier (general_linear_group g))))`,
    SIMP_TAC[ismlg;ismlg_complex;ismlg_real;general_linear_group;CARRIER_SUBGROUP_OF;IMAGE_CX_MATRIX_RE_MATRIX_IMAGE;IMAGE_RE_MATRIX_CX_MATRIX] THEN
    SIMP_TAC[GSYM general_linear_group;GENERAL_LINEAR_GROUP] THEN
    COND_CASES_TAC THENL [ALL_TAC;SET_TAC[]] THEN
    ASM_SIMP_TAC[IMAGE_RE_INVERTIBLE_IMP;IN_ELIM_THM] THEN
    SIMP_TAC[GSYM GENERAL_LINEAR_GROUP;CARRIER_SUBGROUP_OF] THEN
    SET_TAC[]);;

let MLG_GROUP_EQ_GLG = prove
    (`(!G:(N)mlg a. 
      (mlg_set G = group_carrier (general_linear_group a)) <=>
      mlg_group G = (general_linear_group a)) /\
      (!G:(N)mlg a. 
      (mlg_set G = IMAGE Cx_matrix (group_carrier (general_linear_group a))) <=>
      mlg_group G = group_rtoc(general_linear_group a))`,
    CONJ_TAC THENL [REWRITE_TAC[GROUPS_EQ;GENERAL_LINEAR_GROUP;MLG_GROUP];ALL_TAC] THEN
    REPEAT GEN_TAC THEN
      MP_TAC (ISPECL [`general_linear_group (a:real^N^N)`;`a:real^N^N`] GROUP_RTOC) THEN
      SIMP_TAC[CARRIER_SUBGROUP_OF;GENERAL_LINEAR_GROUP;GROUPS_EQ;MLG_GROUP]);;
      
let MLG_SET_EQ_GLG = prove
    (`(!a:complex^N^N. mlg_set (group_mlg(general_linear_group a)) = group_carrier (general_linear_group a)) /\
    (!a:real^N^N. mlg_set (group_mlg(general_linear_group a)) = IMAGE Cx_matrix (group_carrier (general_linear_group a)))`,
    SIMP_TAC[GENERAL_LINEAR_GROUP_ISMLG;GSYM mlg_tybij;group_mlg]);;

let MLG_INJ_GLG = prove
    (`(!a:complex^N^N. mlg_group(group_mlg (general_linear_group a)) = general_linear_group a) /\
    (!a:real^N^N. mlg_group(group_mlg (general_linear_group a)) = group_rtoc(general_linear_group a))`,
    CONJ_TAC THENL 
    [SIMP_TAC[GSYM MLG_GROUP_BIJ;GENERAL_LINEAR_GROUP_ISMLG;GENERAL_LINEAR_GROUP];ALL_TAC] THEN
    GEN_TAC THEN
    MATCH_MP_TAC (CONJUNCT2(CONJUNCT2 MLG_GROUP_BIJ)) THEN
    MP_TAC GENERAL_LINEAR_GROUP_ISMLG THEN
    SIMP_TAC[ismlg;IMAGE_CX_MATRIX_RE_MATRIX_IMAGE;IMAGE_RE_MATRIX_CX_MATRIX] THEN
    SIMP_TAC[GENERAL_LINEAR_GROUP]);;

    
(* ------------------------------------------------------------------------- *)
(* special linear group                                                      *)
(* ------------------------------------------------------------------------- *)
make_overloadable "special_linear_group" `:A`;;

overload_interface ("special_linear_group", `real_special_linear_group:real^N^N->(real^N^N)group`);;

(*
overload_interface ("special_linear_group", `complex_special_linear_group:complex^N^N->(complex^N^N)group`);;
*)

let real_special_linear_group = new_definition
    `real_special_linear_group (a:real^N^N) = group ({A:real^N^N | invertible A /\ det(A) = &1}, mat 1:real^N^N, matrix_inv, matrix_mul)`;;
    
let special_linear_group = prove
    (`!a:real^N^N. real_special_linear_group a = group ({A:real^N^N | invertible A /\ det(A) = &1}, mat 1:real^N^N, matrix_inv, matrix_mul)`,
    SIMP_TAC[real_special_linear_group]);;
 
let REAL_SPECIAL_LINEAR_GROUP = prove
    (`(!a:real^N^N. group_carrier(special_linear_group a) = 
                 {A:real^N^N | invertible A /\ det(A) = &1}) /\
    (!a:real^N^N. group_id(special_linear_group a) = mat 1:real^N^N) /\
    (!a:real^N^N. group_inv(special_linear_group a) = matrix_inv) /\
    (!a:real^N^N. group_mul(special_linear_group a) = matrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl real_special_linear_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM real_special_linear_group] THEN SIMP_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[INVERTIBLE_I;DET_I;INVERTIBLE_MATRIX_INV;DET_MATRIX_INV;REAL_INV_1;
              MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RID;
              MATRIX_INV;DET_MUL;REAL_MUL_LID;INVERTIBLE_MATRIX_MUL] THEN
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);;  
 
let SPECIAL_LINEAR_GROUP = prove
    (`(!a:real^N^N. group_carrier(special_linear_group a) = {A:real^N^N | invertible A /\ det(A) = &1})    /\
    (!a:real^N^N. group_id(special_linear_group a) = mat 1:real^N^N) /\
    (!a:real^N^N. group_inv(special_linear_group a) = matrix_inv) /\
    (!a:real^N^N. group_mul(special_linear_group a) = matrix_mul)`,
    SIMP_TAC[REAL_SPECIAL_LINEAR_GROUP]);; 
 
let LINEAR_SPECIAL_SUBGROUP_OF_GENERAL = prove
    (`!g:real^N^N. (group_carrier (special_linear_group g)) subgroup_of (general_linear_group g)`,
    SIMP_TAC[subgroup_of;SPECIAL_LINEAR_GROUP;GENERAL_LINEAR_GROUP;
             SUBSET;IN_ELIM_THM;INVERTIBLE_I;DET_I;
             INVERTIBLE_MATRIX_INV;DET_MATRIX_INV;REAL_INV_1;
             DET_MUL;REAL_MUL_LID;INVERTIBLE_MATRIX_MUL]);;
    
let SPECIAL_LINEAR_GROUP_ISMLG = prove
    (`!g:real^N^N. ismlg (IMAGE Cx_matrix (group_carrier (special_linear_group g)))`,
    GEN_TAC THEN SIMP_TAC[ismlg;ismlg_complex;ismlg_real;special_linear_group;IMAGE_CX_MATRIX_RE_MATRIX_IMAGE;IMAGE_RE_MATRIX_CX_MATRIX] THEN
    SIMP_TAC[GSYM general_linear_group;GSYM special_linear_group] THEN
    SIMP_TAC[LINEAR_SPECIAL_SUBGROUP_OF_GENERAL;SPECIAL_LINEAR_GROUP] THEN
    SIMP_TAC[INVERTIBLE_DET_NZ;REAL_ARITH `~(x = &0) /\ (x = &1) <=> (x = &1)`;IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC (SPEC `&1` MATRIX_CLOSED_DET_CONSTANT) THEN
    SIMP_TAC[MATRIX_CLOSED_SEQUENTIAL_LIMITS] THEN
    DISCH_THEN(MP_TAC o ISPECL [`x:num -> real^N^N`; `l:real^N^N`]) THEN
    ASM_SIMP_TAC[IN_ELIM_THM]);;
    
let MLG_GROUP_EQ_SLG = prove
    (`!G:(N)mlg a. 
      (mlg_set G = IMAGE Cx_matrix (group_carrier (special_linear_group a))) <=>
      mlg_group G = group_rtoc(special_linear_group a)`,
    REPEAT GEN_TAC THEN
      MP_TAC (ISPECL [`special_linear_group (a:real^N^N)`;`a:real^N^N`] GROUP_RTOC) THEN
      SIMP_TAC[LINEAR_SPECIAL_SUBGROUP_OF_GENERAL;SPECIAL_LINEAR_GROUP;GROUPS_EQ;MLG_GROUP]);; 
    
let MLG_SET_EQ_SLG = prove
    (`!a:real^N^N. mlg_set (group_mlg (special_linear_group a)) = IMAGE Cx_matrix (group_carrier (special_linear_group a))`,
    SIMP_TAC[SPECIAL_LINEAR_GROUP_ISMLG;GSYM mlg_tybij;group_mlg]);;
    
let MLG_INJ_SLG = prove
    (`(!a:real^N^N. mlg_group(group_mlg (special_linear_group a)) = group_rtoc(special_linear_group a))`,
    GEN_TAC THEN
    MATCH_MP_TAC (CONJUNCT2(CONJUNCT2 MLG_GROUP_BIJ)) THEN
    MP_TAC SPECIAL_LINEAR_GROUP_ISMLG THEN
    SIMP_TAC[ismlg;IMAGE_CX_MATRIX_RE_MATRIX_IMAGE;IMAGE_RE_MATRIX_CX_MATRIX] THEN
    SIMP_TAC[SPECIAL_LINEAR_GROUP]);;    
    
(* ------------------------------------------------------------------------- *)
(* orthogonal group                                                          *)
(* ------------------------------------------------------------------------- *)

make_overloadable "orthogonal_group" `:A`;;

overload_interface ("orthogonal_group", `real_orthogonal_group:real^N^N->(real^N^N)group`);;

let real_orthogonal_group = new_definition
    `real_orthogonal_group (a:real^N^N) = group ({A:real^N^N | orthogonal_matrix A}, mat 1:real^N^N, matrix_inv, matrix_mul)`;; 
    
let orthogonal_group = prove
    (`!a. real_orthogonal_group a = group ({A:real^N^N | orthogonal_matrix A}, mat 1:real^N^N, matrix_inv, matrix_mul)`,
    SIMP_TAC[real_orthogonal_group]);;

let REAL_ORTHOGONAL_GROUP = prove
    (`(!a:real^N^N. group_carrier(orthogonal_group a) = {A:real^N^N | orthogonal_matrix A}) /\
   (!a:real^N^N. group_id(orthogonal_group a) = mat 1:real^N^N) /\
   (!a:real^N^N. group_inv(orthogonal_group a) = matrix_inv) /\
   (!a:real^N^N. group_mul(orthogonal_group a) = matrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl real_orthogonal_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM real_orthogonal_group] THEN ANTS_TAC THENL
    [SIMP_TAC[IN_ELIM_THM] THEN
     SIMP_TAC[ORTHOGONAL_MATRIX_ID;ORTHOGONAL_MATRIX_INV_EQ;ORTHOGONAL_MATRIX_MUL;
              MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RID;
              ORTHOGONAL_MATRIX_IMP_INVERTIBLE;MATRIX_INV];ALL_TAC] THEN
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);;
    
let ORTHOGONAL_GROUP = prove
    (`(!a:real^N^N. group_carrier(orthogonal_group a) = {A:real^N^N | orthogonal_matrix A}) /\
   (!a:real^N^N. group_id(orthogonal_group a) = mat 1:real^N^N) /\
   (!a:real^N^N. group_inv(orthogonal_group a) = matrix_inv) /\
   (!a:real^N^N. group_mul(orthogonal_group a) = matrix_mul)`,
   SIMP_TAC[REAL_ORTHOGONAL_GROUP]);;
   
let ORTHOGONAL_SUBGROUP_OF_GENERAL = prove
    (`!g:real^N^N. (group_carrier (orthogonal_group g)) subgroup_of (general_linear_group g)`,
    SIMP_TAC[subgroup_of;ORTHOGONAL_GROUP;GENERAL_LINEAR_GROUP;
             SUBSET;IN_ELIM_THM;ORTHOGONAL_MATRIX_ID;
             ORTHOGONAL_MATRIX_INV_EQ;ORTHOGONAL_MATRIX_MUL;
             ORTHOGONAL_MATRIX_IMP_INVERTIBLE]);;
             
let ORTHOGONAL_GROUP_ISMLG = prove
    (`!g:real^N^N. ismlg (IMAGE Cx_matrix (group_carrier (orthogonal_group g)))`,
    GEN_TAC THEN SIMP_TAC[ismlg;ismlg_complex;ismlg_real;orthogonal_group;IMAGE_CX_MATRIX_RE_MATRIX_IMAGE;IMAGE_RE_MATRIX_CX_MATRIX] THEN
    SIMP_TAC[GSYM general_linear_group;GSYM orthogonal_group] THEN
    SIMP_TAC[ORTHOGONAL_SUBGROUP_OF_GENERAL;ORTHOGONAL_GROUP] THEN
    MESON_TAC[TAUT `(P ==> Q) ==> (P ==> (Q \/ R))`;
              MATRIX_CLOSED_ORTHOGONAL_MATRIX;MATRIX_CLOSED_SEQUENTIAL_LIMITS]);;
              
let MLG_GROUP_EQ_OG = prove
    (`!G:(N)mlg a:real^N^N. 
      (mlg_set G = IMAGE Cx_matrix (group_carrier (orthogonal_group a))) <=>
      mlg_group G = group_rtoc(orthogonal_group a)`,
    REPEAT GEN_TAC THEN
      MP_TAC (ISPECL [`orthogonal_group (a:real^N^N)`;`a:real^N^N`] GROUP_RTOC) THEN
      SIMP_TAC[ORTHOGONAL_SUBGROUP_OF_GENERAL;ORTHOGONAL_GROUP;GROUPS_EQ;MLG_GROUP]);;
    
let MLG_SET_EQ_OG = prove
    (`!a:real^N^N. mlg_set (group_mlg (orthogonal_group a)) = IMAGE Cx_matrix (group_carrier (orthogonal_group a))`,
    SIMP_TAC[ORTHOGONAL_GROUP_ISMLG;GSYM mlg_tybij;group_mlg]);;
    
let MLG_INJ_OG = prove
    (`(!a:real^N^N. mlg_group(group_mlg (orthogonal_group a)) = group_rtoc(orthogonal_group a))`,
    GEN_TAC THEN
    MATCH_MP_TAC (CONJUNCT2(CONJUNCT2 MLG_GROUP_BIJ)) THEN
    MP_TAC ORTHOGONAL_GROUP_ISMLG THEN
    SIMP_TAC[ismlg;IMAGE_CX_MATRIX_RE_MATRIX_IMAGE;IMAGE_RE_MATRIX_CX_MATRIX] THEN
    SIMP_TAC[ORTHOGONAL_GROUP]);;

(* ------------------------------------------------------------------------- *)
(* rotation group                                                            *)
(* ------------------------------------------------------------------------- *)
  
make_overloadable "rotation_group" `:A`;;

overload_interface ("rotation_group", `real_rotation_group:real^N^N->(real^N^N)group`);;
  
let real_rotation_group = new_definition
    `real_rotation_group (a:real^N^N) = group ({A:real^N^N | orthogonal_matrix A /\ det(A) = &1},mat 1:real^N^N, matrix_inv, matrix_mul)`;; 
    
let rotation_group = prove
    (`!a. real_rotation_group a = group ({A:real^N^N | orthogonal_matrix A /\ det(A) = &1},mat 1:real^N^N, matrix_inv, matrix_mul)`,
    SIMP_TAC[real_rotation_group]);;
 
let REAL_ROTATION_GROUP = prove
    (`(!a:real^N^N. group_carrier(rotation_group a) = 
     {A:real^N^N | orthogonal_matrix A  /\ det(A) = &1}) /\
    (!a:real^N^N. group_id(rotation_group a) = mat 1:real^N^N) /\
    (!a:real^N^N. group_inv(rotation_group a) = matrix_inv) /\
    (!a:real^N^N. group_mul(rotation_group a) = matrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl real_rotation_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM real_rotation_group] THEN ANTS_TAC THENL
    [SIMP_TAC[IN_ELIM_THM] THEN
     SIMP_TAC[ORTHOGONAL_MATRIX_ID;DET_I;
              ORTHOGONAL_MATRIX_INV_EQ;DET_MATRIX_INV;REAL_INV_1;
              ORTHOGONAL_MATRIX_MUL;DET_MUL;REAL_MUL_LID;
              MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RID;
              ORTHOGONAL_MATRIX_IMP_INVERTIBLE;MATRIX_INV];ALL_TAC] THEN
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);;
   
let ROTATION_GROUP = prove
    (`(!a:real^N^N. group_carrier(rotation_group a) = 
     {A:real^N^N | orthogonal_matrix A  /\ det(A) = &1}) /\
    (!a:real^N^N. group_id(rotation_group a) = mat 1:real^N^N) /\
    (!a:real^N^N. group_inv(rotation_group a) = matrix_inv) /\
    (!a:real^N^N. group_mul(rotation_group a) = matrix_mul)`,
    SIMP_TAC[REAL_ROTATION_GROUP]);;

let ROTATION_SUBGROUP_OF_GENERAL = prove
    (`!g:real^N^N. (group_carrier (rotation_group g)) subgroup_of (general_linear_group g)`,
    SIMP_TAC[subgroup_of;ROTATION_GROUP;GENERAL_LINEAR_GROUP;
             SUBSET;IN_ELIM_THM;ORTHOGONAL_MATRIX_ID;DET_I;
             ORTHOGONAL_MATRIX_INV_EQ;DET_MATRIX_INV;REAL_INV_1;
             ORTHOGONAL_MATRIX_MUL;DET_MUL;REAL_MUL_LID;
             ORTHOGONAL_MATRIX_IMP_INVERTIBLE]);;
             
let ROTATION_GROUP_ISMLG = prove
    (`!g:real^N^N. ismlg (IMAGE Cx_matrix (group_carrier (rotation_group g)))`,
    GEN_TAC THEN SIMP_TAC[ismlg;ismlg_complex;ismlg_real;rotation_group;IMAGE_CX_MATRIX_RE_MATRIX_IMAGE;IMAGE_RE_MATRIX_CX_MATRIX] THEN
    SIMP_TAC[GSYM general_linear_group;GSYM rotation_group] THEN
    SIMP_TAC[ROTATION_SUBGROUP_OF_GENERAL;ROTATION_GROUP] THEN
    MP_TAC(REWRITE_RULE [INTER;IN_ELIM_THM] (ISPECL [`{A:real^N^N | orthogonal_matrix A}`;`{A:real^N^N | det A = &1}`] MATRIX_CLOSED_INTER)) THEN
    SIMP_TAC[MATRIX_CLOSED_ORTHOGONAL_MATRIX;MATRIX_CLOSED_DET_CONSTANT;MATRIX_CLOSED_SEQUENTIAL_LIMITS] THEN SET_TAC[]);;
    
let MLG_GROUP_EQ_SOG = prove
    (`!G:(N)mlg a:real^N^N. 
      (mlg_set G = IMAGE Cx_matrix (group_carrier (rotation_group a))) <=>
      mlg_group G = group_rtoc(rotation_group a)`,
    REPEAT GEN_TAC THEN
      MP_TAC (ISPECL [`rotation_group (a:real^N^N)`;`a:real^N^N`] GROUP_RTOC) THEN
      SIMP_TAC[ROTATION_SUBGROUP_OF_GENERAL;ROTATION_GROUP;GROUPS_EQ;MLG_GROUP]);;
    
let MLG_SET_EQ_SOG = prove
    (`!a:real^N^N. mlg_set (group_mlg (rotation_group a)) = IMAGE Cx_matrix (group_carrier (rotation_group a))`,
    SIMP_TAC[ROTATION_GROUP_ISMLG;GSYM mlg_tybij;group_mlg]);;
    
let MLG_INJ_SOG = prove
    (`(!a:real^N^N. mlg_group(group_mlg (rotation_group a)) = group_rtoc(rotation_group a))`,
    GEN_TAC THEN
    MATCH_MP_TAC (CONJUNCT2(CONJUNCT2 MLG_GROUP_BIJ)) THEN
    MP_TAC ROTATION_GROUP_ISMLG THEN
    SIMP_TAC[ismlg;IMAGE_CX_MATRIX_RE_MATRIX_IMAGE;IMAGE_RE_MATRIX_CX_MATRIX] THEN
    SIMP_TAC[ROTATION_GROUP]);;
    
(* ------------------------------------------------------------------------- *)
(* Compactness in matrix space                                                            *)
(* ------------------------------------------------------------------------- *)

let MATRIX_CLOSED_ROTATION_MATRIX = prove
    (`matrix_closed {A:real^N^N | rotation_matrix A}`,
    MP_TAC(REWRITE_RULE [INTER;IN_ELIM_THM] (ISPECL [`{A:real^N^N | orthogonal_matrix A}`;`{A:real^N^N | det A = &1}`] MATRIX_CLOSED_INTER)) THEN
    SIMP_TAC[rotation_matrix;MATRIX_CLOSED_ORTHOGONAL_MATRIX;MATRIX_CLOSED_DET_CONSTANT]);;

let MATRIX_BOUNDED_ORTHOGONAL_MATRIX = prove
    (`matrix_bounded {A:real^N^N | orthogonal_matrix A}`,
    SIMP_TAC[matrix_bounded;IN_ELIM_THM;ORTHOGONAL_MATRIX;TRACE_I;fnorm] THEN
    EXISTS_TAC `sqrt (&(dimindex (:N)))` THEN 
    SIMP_TAC[REAL_LE_REFL]);;
    
let MATRIX_BOUNDED_ROTATION_MATRIX = prove
    (`matrix_bounded {A:real^N^N | rotation_matrix A}`,
    SIMP_TAC[matrix_bounded;IN_ELIM_THM;rotation_matrix;ORTHOGONAL_MATRIX;TRACE_I;fnorm] THEN
    EXISTS_TAC `sqrt (&(dimindex (:N)))` THEN SIMP_TAC[REAL_LE_REFL]);;

let MATRIX_COMPACT_ORTHOGONAL_GROUP = prove
    (`!g:real^N^N. matrix_compact (group_carrier (orthogonal_group g))`,
    SIMP_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED;ORTHOGONAL_GROUP] THEN
    SIMP_TAC[MATRIX_BOUNDED_ORTHOGONAL_MATRIX;MATRIX_CLOSED_ORTHOGONAL_MATRIX]);;
    
let MATRIX_COMPACT_ROTATION_GROUP = prove
    (`!g:real^N^N. matrix_compact (group_carrier (rotation_group g))`,
    SIMP_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED;ROTATION_GROUP] THEN
    SIMP_TAC[MATRIX_BOUNDED_ROTATION_MATRIX;GSYM rotation_matrix;MATRIX_CLOSED_ROTATION_MATRIX]);;

let NOT_MATRIX_COMPACT_GENERAL_LINEAR_GROUP = prove    
    (`!g:real^N^N. ~(matrix_compact (group_carrier (general_linear_group g)))`,
    let lem = MESON [SQRT_POS_LT;REAL_OF_NUM_LT;DIMINDEX_GE_1;ARITH_RULE `1 <= k ==> 0 < k`] `&0 < sqrt (&(dimindex (:N)))` in
    SIMP_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED;GENERAL_LINEAR_GROUP] THEN
    SIMP_TAC[DE_MORGAN_THM;INVERTIBLE_DET_NZ] THEN DISJ2_TAC THEN
    SIMP_TAC[SET_RULE `UNIV DIFF {x | ~(P x)} = {x | P x}`;matrix_closed] THEN
    SIMP_TAC[matrix_open;IN_ELIM_THM] THEN
    SIMP_TAC[NOT_FORALL_THM;TAUT `~(P ==> Q) <=> (P /\ ~Q)`;NOT_EXISTS_THM;DE_MORGAN_THM] THEN
    EXISTS_TAC `(mat 0):real^N^N` THEN
    SIMP_TAC[DET_0;MATRIX_DIST_0] THEN GEN_TAC THEN
    ASM_CASES_TAC `&0 < e` THEN ASM_SIMP_TAC[] THEN
    EXISTS_TAC `(e * inv(&2 * sqrt (&(dimindex (:N))))) %% (mat 1):real^N^N` THEN
    SIMP_TAC[FNORM_MUL;FNORM_MAT;DET_CMUL;DET_I;REAL_MUL_RID;REAL_MUL_LID] THEN
    CONJ_TAC THENL
    [ASM_SIMP_TAC[REAL_ABS_MUL;REAL_INV_MUL;REAL_ARITH `&0 < e  ==> abs(e) = e`;lem;GSYM REAL_MUL_ASSOC;REAL_MUL_LINV;REAL_LT_IMP_NZ;REAL_LT_INV;REAL_ARITH `&0 < &2`;REAL_MUL_RID] THEN ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ENTIRE;DE_MORGAN_THM;REAL_ARITH `&0 < e ==> ~(e = &0)`;REAL_INV_EQ_0;lem;REAL_ARITH `~(&2 = &0)`;REAL_POW_NZ]);;

let MATRIX_COMPACT_SPECIAL_LINEAR_GROUP_1_GEN = prove
    (`!g:real^N^N. dimindex(:N) = 1 ==> (matrix_compact (group_carrier (special_linear_group g)))`,
    SIMP_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED;SPECIAL_LINEAR_GROUP] THEN
    SIMP_TAC[INVERTIBLE_DET_NZ;REAL_ARITH `~(k = &0) /\ k = &1 <=> k = &1`;MATRIX_CLOSED_DET_CONSTANT] THEN
    SIMP_TAC[matrix_bounded;IN_ELIM_THM;DET_1_GEN;fnorm;trace;SUM_1;matrix_mul;TRANSP_COMPONENT;LAMBDA_BETA;DIMINDEX_GE_1;LE_REFL] THEN
    STRIP_TAC THEN EXISTS_TAC `&1` THEN
    SIMP_TAC[REAL_MUL_RID;SQRT_1;REAL_LE_REFL]);;
    
let MATRIX_COMPACT_SPECIAL_LINEAR_GROUP_1 = prove
    (`!g:real^1^1. matrix_compact (group_carrier (special_linear_group g))`,
    SIMP_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED;SPECIAL_LINEAR_GROUP] THEN
    SIMP_TAC[INVERTIBLE_DET_NZ;REAL_ARITH `~(k = &0) /\ k = &1 <=> k = &1`;MATRIX_CLOSED_DET_CONSTANT] THEN
    SIMP_TAC[matrix_bounded;IN_ELIM_THM;DET_1;FNORM_REAL] THEN
    EXISTS_TAC `&1` THEN SIMP_TAC[REAL_ABS_1;REAL_LE_REFL]);;

let NOT_MATRIX_COMPACT_SPECIAL_LINEAR_GROUP_GE_1 = prove
    (`!g:real^N^N. 1 < dimindex(:N) ==> ~(matrix_compact (group_carrier (special_linear_group g)))`,
    SIMP_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED;SPECIAL_LINEAR_GROUP] THEN
    SIMP_TAC[INVERTIBLE_DET_NZ;REAL_ARITH `~(k = &0) /\ k = &1 <=> k = &1`;MATRIX_CLOSED_DET_CONSTANT] THEN
    SIMP_TAC[matrix_bounded;IN_ELIM_THM] THEN
    SIMP_TAC[NOT_EXISTS_THM;NOT_FORALL_THM;TAUT `~(P ==> Q) <=> (P /\ ~Q)`;REAL_NOT_LE] THEN
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `a = --(&1)` THENL
    [EXISTS_TAC `(mat 1):real^N^N` THEN SIMP_TAC[DET_I] THEN
     MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&0` THEN
     ASM_SIMP_TAC[REAL_ARITH `--(&1) < &0`;FNORM_POS_LE];ALL_TAC] THEN
    EXISTS_TAC `(lambda i j. if i = j then if i = 1 then (a + &1) else if i = 2 then inv(a + &1) else &1 else &0):real^N^N` THEN
    CONJ_TAC THENL
    [MP_TAC (ISPEC `(lambda i j. if i = j then if i = 1 then (a + &1) else if i = 2 then inv(a + &1) else &1 else &0):real^N^N` DET_LOWERTRIANGULAR) THEN 
     SIMP_TAC[LAMBDA_BETA;LT_IMP_NE] THEN STRIP_TAC THEN
     ASM_SIMP_TAC[PRODUCT_CLAUSES_LEFT;DIMINDEX_GE_1;ARITH_RULE `1 < k ==> 2 <= k`;ARITH_RULE `1 + 1 = 2 /\ ~(2 = 1) /\ (1 + 1) + 1 = 3`] THEN
     ASM_SIMP_TAC[REAL_MUL_ASSOC;REAL_MUL_RINV;REAL_ARITH `~(a = -- &1) ==> ~((a + &1) = &0)`;REAL_MUL_LID] THEN
     MATCH_MP_TAC PRODUCT_EQ_1_NUMSEG THEN
     SIMP_TAC[] THEN ARITH_TAC;ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `abs(a + &1)` THEN
    MP_TAC (ISPECL [`(lambda i j. if i = j then if i = 1 then (a + &1) else if i = 2 then inv(a + &1) else &1 else &0):real^N^N`;`1`;`1`] COMPONENT_LE_FNORM) THEN
    SIMP_TAC[LAMBDA_BETA;DIMINDEX_GE_1;LE_REFL] THEN
    STRIP_TAC THEN ARITH_TAC);;

(*
let TRANSP_HOMO_TRANS = prove
    (`!x R:real^N^N. transp(homo_trans x R) = homo_trans (vec 0) (transp R) + (lambda i j. if i = dimindex (:N) + 1 /\ ~(j = dimindex (:N) + 1)
              then x$j else &0)`,
    SIMP_TAC[CART_EQ;LAMBDA_BETA;TRANSP_COMPONENT;HOMO_TRANS_COMPONENT;DIMINDEX_1;DIMINDEX_FINITE_SUM;MATRIX_ADD_COMPONENT;VEC_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THENL[ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;ALL_TAC]) THEN ARITH_TAC);;

let TRANSP_HOMO_TRANS_MUL_TRANS = prove
    (`!x1 x2:real^N R1 R2:real^N^N. transp(homo_trans x1 R1) ** (homo_trans x2 R2) = homo_trans (transp(R1) ** x2) (transp(R1) ** R2) + (lambda i j. if i = dimindex (:N) + 1 /\ ~(j = dimindex (:N) + 1)
              then (x1 ** R2)$j
              else if i = dimindex (:N) + 1 /\ j = dimindex (:N) + 1            then x1 dot x2 else &0)`,
    SIMP_TAC[TRANSP_HOMO_TRANS;MATRIX_ADD_RDISTRIB;HOMO_TRANS_MUL_TRANS;VECTOR_ADD_LID;CMATRIX_ARITH `(a:real^N^N) + b = a + c <=> b = c`] THEN
    SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_1;DIMINDEX_FINITE_SUM;matrix_mul;vector_matrix_mul;HOMO_TRANS_COMPONENT;ARITH_RULE `i <= N + 1 /\ ~(i = (N + 1)) ==> i <= N`] THEN
    SIMP_TAC[COND_LMUL;COND_RMUL;COND_LMUL_0;dot] THEN
    REPEAT STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THENL [ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET;IN_NUMSEG;ARITH_RULE `(1 <= k /\ k <= N + 1) /\ ~(k = N + 1) <=> 1 <= k /\ k <= N`] THEN
    SIMP_TAC[GSYM IN_NUMSEG;SET_RULE `{k | k IN s} = s`;REAL_MUL_SYM];ALL_TAC]) THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    SIMP_TAC[GSYM IMP_CONJ;ARITH_RULE `~(i = N + 1 /\ ~(i' = N + 1)) /\ ~(i = N + 1 /\ i' = N + 1) <=> ~(i = N + 1)`;SUM_0]);;

let NOT_MATRIX_COMPACT_EUCLIDEAN_GROUP = prove
    (`!x R:real^N^N. ~(matrix_compact (group_carrier (euclidean_group x R)))`,
    SIMP_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED;EUCLIDEAN_GROUP] THEN
    SIMP_TAC[MATRIX_CLOSED_HOMO_TRANS_ALT] THEN
    SIMP_TAC[matrix_bounded;IN_ELIM_THM;IN_UNIV] THEN
    SIMP_TAC[NOT_EXISTS_THM;NOT_FORALL_THM;TAUT `~(P ==> Q) <=> (P /\ ~Q)`;REAL_NOT_LE;LEFT_AND_EXISTS_THM;GSYM CONJ_ASSOC] THEN
    GEN_TAC THEN 
    MAP_EVERY EXISTS_TAC [`homo_trans (a % (basis 1):real^N) (mat 1)`;`(a % (basis 1):real^N)`;`(mat 1):real^N^N`] THEN
    SIMP_TAC[ORTHOGONAL_MATRIX_ID;fnorm;TRANSP_HOMO_TRANS_MUL_TRANS;TRANSP_MAT;MATRIX_MUL_LID;TRACE_ADD;TRACE_I;TRACE_HOMO_TRANS;DOT_LMUL;DOT_RMUL] THEN
    SIMP_TAC[DOT_BASIS;BASIS_COMPONENT;DIMINDEX_GE_1;LE_REFL;REAL_MUL_RID;trace;LAMBDA_BETA;DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    SIMP_TAC[GSYM SUM_RESTRICT_SET;TAUT `P /\ ~P <=> F`;IN_NUMSEG;ARITH_RULE `((1 <= i /\ i <= k + 1) /\ i = k + 1) <=> i = k + 1`;SET_RULE `{i | i = k} = {k}`;SUM_SING] THEN
    MATCH_MP_TAC REAL_LT_RSQRT THEN
    SIMP_TAC[REAL_POW_2] THEN ARITH_TAC);;

let NOT_MATRIX_COMPACT_SPECIAL_EUCLIDEAN_GROUP = prove
    (`!x R:real^N^N. ~(matrix_compact (group_carrier (special_euclidean_group x R)))`,
    SIMP_TAC[MATRIX_COMPACT_EQ_BOUNDED_CLOSED;SPECIAL_EUCLIDEAN_GROUP] THEN
    SIMP_TAC[DE_MORGAN_THM] THEN DISJ1_TAC THEN
    SIMP_TAC[matrix_bounded;IN_ELIM_THM;IN_UNIV;DET_HOMO_TRANS_EQ] THEN
    SIMP_TAC[NOT_EXISTS_THM;NOT_FORALL_THM;TAUT `~(P ==> Q) <=> (P /\ ~Q)`;REAL_NOT_LE;LEFT_AND_EXISTS_THM;GSYM CONJ_ASSOC] THEN
    GEN_TAC THEN 
    MAP_EVERY EXISTS_TAC [`homo_trans (a % (basis 1):real^N) (mat 1)`;`(a % (basis 1):real^N)`;`(mat 1):real^N^N`] THEN
    SIMP_TAC[DET_I;ORTHOGONAL_MATRIX_ID;fnorm;TRANSP_HOMO_TRANS_MUL_TRANS;TRANSP_MAT;MATRIX_MUL_LID;TRACE_ADD;TRACE_I;TRACE_HOMO_TRANS;DOT_LMUL;DOT_RMUL] THEN
    SIMP_TAC[DOT_BASIS;BASIS_COMPONENT;DIMINDEX_GE_1;LE_REFL;REAL_MUL_RID;trace;LAMBDA_BETA;DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    SIMP_TAC[GSYM SUM_RESTRICT_SET;TAUT `P /\ ~P <=> F`;IN_NUMSEG;ARITH_RULE `((1 <= i /\ i <= k + 1) /\ i = k + 1) <=> i = k + 1`;SET_RULE `{i | i = k} = {k}`;SUM_SING] THEN
    MATCH_MP_TAC REAL_LT_RSQRT THEN
    SIMP_TAC[REAL_POW_2] THEN ARITH_TAC);;
*)

(* ------------------------------------------------------------------------- *)
(* Paths and arcs.                                                           *)
(* ------------------------------------------------------------------------- *)

let matrix_path = new_definition
 `!g:real^1^1->real^N^M. matrix_path g <=> g matrix_continuous_on matrix_interval[mat 0,mat 1]`;;

let matrix_pathstart = new_definition
 `matrix_pathstart (g:real^1^1->real^N^M) = g(mat 0)`;;

let matrix_pathfinish = new_definition
 `matrix_pathfinish (g:real^1^1->real^N^M) = g(mat 1)`;;

let matrix_path_image = new_definition
 `matrix_path_image (g:real^1^1->real^N^M) = IMAGE g (matrix_interval[mat 0,mat 1])`;;

let matrix_reversepath = new_definition
 `matrix_reversepath (g:real^1^1->real^N^M) = \x. g(mat 1 - x)`;;

let matrix_simple_path = new_definition
 `matrix_simple_path (g:real^1^1->real^N^M) <=>
        matrix_path g /\
        !x y. x IN matrix_interval[mat 0,mat 1] /\
              y IN matrix_interval[mat 0,mat 1] /\
              g x = g y
              ==> x = y \/ x = mat 0 /\ y = mat 1 \/ x = mat 1 /\ y = mat 0`;;

let matrix_arc = new_definition
 `matrix_arc (g:real^1^1->real^N^M) <=>
        matrix_path g /\
        !x y. x IN matrix_interval [mat 0,mat 1] /\
              y IN matrix_interval [mat 0,mat 1] /\
              g x = g y
              ==> x = y`;;
              
(* ------------------------------------------------------------------------- *)
(* Relate to topological general case.                                       *)
(* ------------------------------------------------------------------------- *)
let REAL_INTERVAL_MATRIX_INTERVAL = prove
 (`real_interval[a,b] = IMAGE drop_drop (matrix_interval[lift_lift a,lift_lift b]) /\
   real_interval(a,b) = IMAGE drop_drop (matrix_interval(lift_lift a,lift_lift b))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_MATRIX_INTERVAL_1; IN_REAL_INTERVAL] THEN
  REWRITE_TAC[EXISTS_LIFT2; LIFT2_DROP; UNWIND_THM1]);;

let MATRIX_INTERVAL_REAL_INTERVAL = prove
 (`matrix_interval[a,b] = IMAGE lift_lift (real_interval[drop_drop a,drop_drop b]) /\
   matrix_interval(a,b) = IMAGE lift_lift (real_interval(drop_drop a,drop_drop b))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_MATRIX_INTERVAL_1; IN_REAL_INTERVAL] THEN
  REWRITE_TAC[EXISTS_DROP2; LIFT2_DROP; UNWIND_THM1]);;

let DROP2_IN_REAL_INTERVAL = prove
 (`(!a b x. drop_drop x IN real_interval[a,b] <=> x IN matrix_interval[lift_lift a,lift_lift b]) /\
   (!a b x. drop_drop x IN real_interval(a,b) <=> x IN matrix_interval(lift_lift a,lift_lift b))`,
  REWRITE_TAC[REAL_INTERVAL_MATRIX_INTERVAL; IN_IMAGE] THEN MESON_TAC[LIFT2_DROP]);;

let LIFT2_IN_MATRIX_INTERVAL = prove
 (`(!a b x. lift_lift x IN matrix_interval[a,b] <=> x IN real_interval[drop_drop a,drop_drop b]) /\
   (!a b x. lift_lift x IN matrix_interval(a,b) <=> x IN real_interval(drop_drop a,drop_drop b))`,
  REWRITE_TAC[FORALL_DROP2; DROP2_IN_REAL_INTERVAL; LIFT2_DROP]);;

let IMAGE_LIFT2_REAL_INTERVAL = prove
 (`IMAGE lift_lift (real_interval[a,b]) = matrix_interval[lift_lift a,lift_lift b] /\
   IMAGE lift_lift (real_interval(a,b)) = matrix_interval(lift_lift a,lift_lift b)`,
  REWRITE_TAC[REAL_INTERVAL_MATRIX_INTERVAL; GSYM IMAGE_o; o_DEF; LIFT2_DROP] THEN
  SET_TAC[]);;

let IMAGE_DROP2_MATRIX_INTERVAL = prove
 (`IMAGE drop_drop (matrix_interval[a,b]) = real_interval[drop_drop a,drop_drop b] /\
   IMAGE drop_drop (matrix_interval(a,b)) = real_interval(drop_drop a,drop_drop b)`,
  REWRITE_TAC[MATRIX_INTERVAL_REAL_INTERVAL; GSYM IMAGE_o; o_DEF; LIFT2_DROP] THEN
  SET_TAC[]);;
  
let IMAGE_LIFT2_DROP = prove
 (`(!s. IMAGE (lift_lift o drop_drop) s = s) /\ (!s. IMAGE (drop_drop o lift_lift) s = s)`,
  REWRITE_TAC[o_DEF; LIFT2_DROP] THEN SET_TAC[]);;

let CONTINUOUS_MAP_EQ_LIFT2 = prove
 (`!top f:A->real.
        continuous_map(top,euclideanreal) f <=>
        continuous_map(top,matrix_space) (lift_lift o f)`,
  REWRITE_TAC[CONTINUOUS_MAP_ATPOINTOF; LIMIT_EQ_LIFT2; o_THM]);;

let CONTINUOUS_MAP_EQ_DROP2 = prove
 (`!top f:A->real^1^1.
        continuous_map(top,matrix_space) f <=>
        continuous_map(top,euclideanreal) (drop_drop o f)`,
  REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT2; o_DEF; LIFT2_DROP; ETA_AX]);;
  
let CONTINUOUS_MAP_LIFT2 = prove
 (`continuous_map (euclideanreal,matrix_space) lift_lift`,
  REWRITE_TAC[CONTINUOUS_MAP_EQ_DROP2; o_DEF; LIFT2_DROP; CONTINUOUS_MAP_ID]);;

let CONTINUOUS_MAP_DROP2 = prove
 (`continuous_map (matrix_space,euclideanreal) drop_drop`,
  REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT2; o_DEF; LIFT2_DROP; CONTINUOUS_MAP_ID]);;
  
let PATH_IN_MATRIX_SPACE = prove
 (`!s:real^N^M->bool g.
        path_in (subtopology matrix_space s) g <=>
        matrix_path (g o drop_drop) /\ matrix_path_image (g o drop_drop) SUBSET s`,
  REWRITE_TAC[path_in; matrix_path; GSYM CONTINUOUS_MAP_MATRIX_SPACE] THEN
  REWRITE_TAC[matrix_path_image; MATRIX_INTERVAL_REAL_INTERVAL; DROP2_MAT] THEN
  REWRITE_TAC[GSYM IMAGE_o; GSYM o_ASSOC] THEN
  ONCE_REWRITE_TAC[IMAGE_o] THEN
  REWRITE_TAC[IMAGE_LIFT2_DROP; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    SUBGOAL_THEN `g:real->real^N^M = (g o drop_drop) o lift_lift` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT2_DROP]; ALL_TAC]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    CONTINUOUS_MAP_COMPOSE)) THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY;
           CONTINUOUS_MAP_LIFT2; CONTINUOUS_MAP_DROP2] THEN
  REWRITE_TAC[TOPSPACE_MATRIX_SPACE_SUBTOPOLOGY; SUBSET_REFL;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_DEF; LIFT2_DROP]);;

let PATH_MATRIX_SPACE = prove
 (`!s g:real^1^1->real^N^M.
        matrix_path g /\ matrix_path_image g SUBSET s <=>
        path_in (subtopology matrix_space s) (g o lift_lift)`,
  REWRITE_TAC[PATH_IN_MATRIX_SPACE] THEN
  REWRITE_TAC[o_DEF; LIFT2_DROP; ETA_AX]);;

let MATRIX_PATH_PATH_IN = prove
 (`!g:real^1^1->real^N^M. matrix_path g <=> path_in matrix_space (g o lift_lift)`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
  REWRITE_TAC[GSYM PATH_MATRIX_SPACE; SUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Invariance theorems.                                                      *)
(* ------------------------------------------------------------------------- *)

let MATRIX_CONTINUOUS_ON_EQ = prove
 (`!f:real^N^M->real^P^Q g s. (!x. x IN s ==> f(x) = g(x)) /\ f matrix_continuous_on s
           ==> g matrix_continuous_on s`,
  SIMP_TAC[matrix_continuous_on; IMP_CONJ]);;

let MATRIX_PATH_EQ = prove
 (`!p q. (!t. t IN matrix_interval[mat 0,mat 1] ==> p t = q t) /\
        matrix_path p ==> matrix_path q`,
  REWRITE_TAC[matrix_path; MATRIX_CONTINUOUS_ON_EQ]);;

let MATRIX_PATH_CONTINUOUS_IMAGE = prove
 (`!f:real^N^M->real^P^Q g.
     matrix_path g /\ f matrix_continuous_on matrix_path_image g ==> matrix_path(f o g)`,
  REWRITE_TAC[matrix_path;matrix_path_image;MATRIX_CONTINUOUS_ON_COMPOSE]);;

let MATRIX_PATH_TRANSLATION_EQ = prove
 (`!a g:real^1^1->real^N^M. 
        matrix_path((\x. a + x) o g) <=> matrix_path g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_path] THEN EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `(g:real^1^1->real^N^M) = (\x. --a + x) o (\x. a + x) o g`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN CMATRIX_ARITH_TAC; ALL_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MATRIX_CONTINUOUS_ON_COMPOSE THEN
  ASM_SIMP_TAC[MATRIX_CONTINUOUS_ON_ADD; MATRIX_CONTINUOUS_ON_ID; MATRIX_CONTINUOUS_ON_CONST]);;

add_translation_invariants [MATRIX_PATH_TRANSLATION_EQ];;

let MATRIX_PATH_MLINEAR_IMAGE_EQ = prove
 (`!f:real^N^M->real^P^Q g.
        mlinear f /\ (!x y. f x = f y ==> x = y)
        ==> (matrix_path(f o g) <=> matrix_path g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:real^P^Q->real^N^M` STRIP_ASSUME_TAC o
        MATCH_MP MLINEAR_INJECTIVE_LEFT_INVERSE) THEN
  REWRITE_TAC[matrix_path] THEN EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `g:real^1^1->real^N^M = h o (f:real^N^M->real^P^Q) o g`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[o_ASSOC; I_O_ID]; ALL_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MATRIX_CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MLINEAR_CONTINUOUS_ON]);;

add_linear_invariants [MATRIX_PATH_MLINEAR_IMAGE_EQ];;

let MATRIX_PATHSTART_TRANSLATION = prove
 (`!a g:real^1^1->real^N^M. matrix_pathstart((\x. a + x) o g) = a + matrix_pathstart g`,
  REWRITE_TAC[matrix_pathstart; o_THM]);;

add_translation_invariants [MATRIX_PATHSTART_TRANSLATION];;

let MATRIX_PATHSTART_MLINEAR_IMAGE_EQ = prove
 (`!f g. mlinear f ==> matrix_pathstart(f o g) = f(matrix_pathstart g)`,
  REWRITE_TAC[matrix_pathstart; o_THM]);;

add_linear_invariants [MATRIX_PATHSTART_MLINEAR_IMAGE_EQ];;

let MATRIX_PATHFINISH_TRANSLATION = prove
 (`!a g:real^1^1->real^N^M. matrix_pathfinish((\x. a + x) o g) = a + matrix_pathfinish g`,
  REWRITE_TAC[matrix_pathfinish; o_THM]);;

add_translation_invariants [MATRIX_PATHFINISH_TRANSLATION];;

let MATRIX_PATHFINISH_MLINEAR_IMAGE = prove
 (`!f g. mlinear f ==> matrix_pathfinish(f o g) = f(matrix_pathfinish g)`,
  REWRITE_TAC[matrix_pathfinish; o_THM]);;

add_linear_invariants [MATRIX_PATHFINISH_MLINEAR_IMAGE];;

let MATRIX_PATH_IMAGE_TRANSLATION = prove
 (`!a g:real^1^1->real^N^M. matrix_path_image((\x. a + x) o g) = IMAGE (\x. a + x) (matrix_path_image g)`,
  REWRITE_TAC[matrix_path_image; IMAGE_o]);;

add_translation_invariants [MATRIX_PATH_IMAGE_TRANSLATION];;

let MATRIX_PATH_IMAGE_MLINEAR_IMAGE = prove
 (`!f g. mlinear f ==> matrix_path_image(f o g) = IMAGE f (matrix_path_image g)`,
  REWRITE_TAC[matrix_path_image; IMAGE_o]);;

add_linear_invariants [MATRIX_PATH_IMAGE_MLINEAR_IMAGE];;

let MATRIX_REVERSEPATH_TRANSLATION = prove
 (`!a g:real^1^1->real^N^M. matrix_reversepath((\x. a + x) o g) = (\x. a + x) o matrix_reversepath g`,
  REWRITE_TAC[FUN_EQ_THM; matrix_reversepath; o_THM]);;

add_translation_invariants [MATRIX_REVERSEPATH_TRANSLATION];;

let MATRIX_REVERSEPATH_MLINEAR_IMAGE = prove
 (`!f g. mlinear f ==> matrix_reversepath(f o g) = f o matrix_reversepath g`,
  REWRITE_TAC[FUN_EQ_THM; matrix_reversepath; o_THM]);;

add_linear_invariants [MATRIX_REVERSEPATH_MLINEAR_IMAGE];;

let MATRIX_SIMPLE_PATH_TRANSLATION_EQ = prove
 (`!a g:real^1^1->real^N^M. matrix_simple_path((\x. a + x) o g) <=> matrix_simple_path g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_simple_path; MATRIX_PATH_TRANSLATION_EQ] THEN
  REWRITE_TAC[o_THM; CMATRIX_ARITH `a + x:real^N^M = a + y <=> x = y`]);;

add_translation_invariants [MATRIX_SIMPLE_PATH_TRANSLATION_EQ];;

let MATRIX_SIMPLE_PATH_MLINEAR_IMAGE_EQ = prove
 (`!f:real^N^M->real^P^Q g.
        mlinear f /\ (!x y. f x = f y ==> x = y)
        ==> (matrix_simple_path(f o g) <=> matrix_simple_path g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[matrix_simple_path; MATRIX_PATH_TRANSLATION_EQ] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[MATRIX_PATH_MLINEAR_IMAGE_EQ]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]);;

add_linear_invariants [MATRIX_SIMPLE_PATH_MLINEAR_IMAGE_EQ];;

let MATRIX_ARC_TRANSLATION_EQ = prove
 (`!a g:real^1^1->real^N^M. matrix_arc((\x. a + x) o g) <=> matrix_arc g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_arc; MATRIX_PATH_TRANSLATION_EQ] THEN
  REWRITE_TAC[o_THM; CMATRIX_ARITH `a + x:real^N^M = a + y <=> x = y`]);;

add_translation_invariants [MATRIX_ARC_TRANSLATION_EQ];;

let MATRIX_ARC_MLINEAR_IMAGE_EQ = prove
 (`!f:real^N^M->real^P^Q g.
        mlinear f /\ (!x y. f x = f y ==> x = y)
        ==> (matrix_arc(f o g) <=> matrix_arc g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[matrix_arc; MATRIX_PATH_TRANSLATION_EQ] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[MATRIX_PATH_MLINEAR_IMAGE_EQ]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]);;

add_linear_invariants [MATRIX_ARC_MLINEAR_IMAGE_EQ];;

let MATRIX_SIMPLE_PATH_CONTINUOUS_IMAGE = prove
 (`!f g. matrix_simple_path g /\
         f matrix_continuous_on matrix_path_image g /\
         (!x y.
              x IN matrix_path_image g /\ y IN matrix_path_image g /\ f x = f y ==> x = y)
         ==> matrix_simple_path(f o g)`,
  REWRITE_TAC[matrix_simple_path; INJECTIVE_ON_ALT] THEN
  SIMP_TAC[MATRIX_PATH_CONTINUOUS_IMAGE] THEN
  REWRITE_TAC[matrix_path_image; o_THM] THEN SET_TAC[]);;

let MATRIX_ARC_CONTINUOUS_IMAGE = prove
 (`!f g:real^1^1->real^N^M.
        matrix_arc g /\
        f matrix_continuous_on matrix_path_image g /\
        (!x y. x IN matrix_path_image g /\ y IN matrix_path_image g /\ f x = f y ==> x = y)
        ==> matrix_arc(f o g)`,
  REWRITE_TAC[matrix_arc; INJECTIVE_ON_ALT] THEN SIMP_TAC[MATRIX_PATH_CONTINUOUS_IMAGE] THEN
  REWRITE_TAC[matrix_path_image; o_THM] THEN SET_TAC[]);;  

(* ------------------------------------------------------------------------- *)
(* Basic lemmas about matrix paths.                                                 *)
(* ------------------------------------------------------------------------- *)

let MATRIX_ARC_IMP_SIMPLE_PATH = prove
 (`!g. matrix_arc g ==> matrix_simple_path g`,
  REWRITE_TAC[matrix_arc; matrix_simple_path] THEN MESON_TAC[]);;

let MATRIX_ARC_IMP_PATH = prove
 (`!g. matrix_arc g ==> matrix_path g`,
  REWRITE_TAC[matrix_arc] THEN MESON_TAC[]);;

let MATRIX_SIMPLE_PATH_IMP_PATH = prove
 (`!g. matrix_simple_path g ==> matrix_path g`,
  REWRITE_TAC[matrix_simple_path] THEN MESON_TAC[]);;

let MATRIX_SIMPLE_PATH_CASES = prove
 (`!g:real^1^1->real^N^M. matrix_simple_path g ==> matrix_arc g \/ matrix_pathfinish g = matrix_pathstart g`,
  REWRITE_TAC[matrix_simple_path; matrix_arc; matrix_pathfinish; matrix_pathstart] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(g:real^1^1->real^N^M) (mat 0) = g(mat 1)` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`u:real^1^1`; `v:real^1^1`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^1^1`; `v:real^1^1`]) THEN
  ASM_MESON_TAC[]);;

let MATRIX_SIMPLE_PATH_IMP_ARC = prove
 (`!g:real^1^1->real^N^M.
        matrix_simple_path g /\ ~(matrix_pathfinish g = matrix_pathstart g) ==> matrix_arc g`,
  MESON_TAC[MATRIX_SIMPLE_PATH_CASES]);;

let MATRIX_ARC_DISTINCT_ENDS = prove
 (`!g:real^1^1->real^N^M. matrix_arc g ==> ~(matrix_pathfinish g = matrix_pathstart g)`,
  GEN_TAC THEN REWRITE_TAC[matrix_arc; matrix_pathfinish; matrix_pathstart] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> a /\ b /\ ~d ==> ~c`] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[GSYM DROP2_EQ; IN_MATRIX_INTERVAL_1; DROP2_MAT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let MATRIX_ARC_SIMPLE_PATH = prove
 (`!g:real^1^1->real^N^M.
        matrix_arc g <=> matrix_simple_path g /\ ~(matrix_pathfinish g = matrix_pathstart g)`,
  MESON_TAC[MATRIX_SIMPLE_PATH_CASES; MATRIX_ARC_IMP_SIMPLE_PATH; MATRIX_ARC_DISTINCT_ENDS]);;

let MATRIX_SIMPLE_PATH_EQ_ARC = prove
 (`!g. ~(matrix_pathstart g = matrix_pathfinish g) ==> (matrix_simple_path g <=> matrix_arc g)`,
  SIMP_TAC[MATRIX_ARC_SIMPLE_PATH]);;

let MATRIX_PATH_IMAGE_NONEMPTY = prove
 (`!g. ~(matrix_path_image g = {})`,
  REWRITE_TAC[matrix_path_image; IMAGE_EQ_EMPTY; MATRIX_INTERVAL_EQ_EMPTY] THEN
  SIMP_TAC[DIMINDEX_1;LE_ANTISYM;GSYM RIGHT_AND_EXISTS_THM; UNWIND_THM1; MAT_COMPONENT;
           ARITH; REAL_OF_NUM_LT]);;

let MATRIX_PATHSTART_IN_PATH_IMAGE = prove
 (`!g. (matrix_pathstart g) IN matrix_path_image g`,
  GEN_TAC THEN REWRITE_TAC[matrix_pathstart; matrix_path_image] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN
  REWRITE_TAC[IN_MATRIX_INTERVAL_1; DROP2_MAT; REAL_POS]);;

let MATRIX_PATHFINISH_IN_PATH_IMAGE = prove
 (`!g. (matrix_pathfinish g) IN matrix_path_image g`,
  GEN_TAC THEN REWRITE_TAC[matrix_pathfinish; matrix_path_image] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN
  REWRITE_TAC[IN_MATRIX_INTERVAL_1; DROP2_MAT] THEN REAL_ARITH_TAC);;
  
let MATRIX_CONNECTED_CONTINUOUS_IMAGE = prove
 (`!f:real^M^N->real^P^Q s.
        f matrix_continuous_on s /\ matrix_connected s ==> matrix_connected(IMAGE f s)`,
  REWRITE_TAC[GSYM CONNECTED_IN_MATRIX_SPACE; GSYM CONTINUOUS_MAP_MATRIX_SPACE] THEN
  MESON_TAC[CONNECTED_IN_CONTINUOUS_MAP_IMAGE; CONNECTED_IN_ABSOLUTE]);;

let MATRIX_CONVEX_CONTAINS_SEGMENT = prove
 (`!s. matrix_convex s <=> !a b. a IN s /\ b IN s ==> matrix_segment[a,b] SUBSET s`,
  REWRITE_TAC[MATRIX_CONVEX_ALT; matrix_segment; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;
  
let MATRIX_SEGMENT_SUBSET_CONVEX = prove
 (`!s a b:real^M^N.
        matrix_convex s /\ a IN s /\ b IN s ==> matrix_segment[a,b] SUBSET s`,
  MESON_TAC[MATRIX_CONVEX_CONTAINS_SEGMENT]);;
  
let MATRIX_CONVEX_CONNECTED = prove
 (`!s:real^M^N->bool. matrix_convex s ==> matrix_connected s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MATRIX_CONNECTED_IFF_CONNECTABLE_POINTS] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M^N`; `b:real^M^N`] THEN STRIP_TAC THEN
  EXISTS_TAC `matrix_segment[a:real^M^N,b]` THEN
  ASM_SIMP_TAC[MATRIX_CONNECTED_SEGMENT; ENDS_IN_MATRIX_SEGMENT; MATRIX_SEGMENT_SUBSET_CONVEX]);;
  
let is_matrix_interval = new_definition
  `is_matrix_interval(s:real^N^M->bool) <=>
        !a b x. a IN s /\ b IN s /\
                (!i j. (1 <= i /\ i <= dimindex (:M)) /\ 1 <= j /\ j <= dimindex (:N)
                     ==> (a$i$j <= x$i$j /\ x$i$j <= b$i$j) \/
                         (b$i$j <= x$i$j /\ x$i$j <= a$i$j))
                ==> x IN s`;;

let IS_MATRIX_INTERVAL_INTERVAL = prove
 (`!a:real^N^M b. is_matrix_interval(matrix_interval (a,b)) /\ is_matrix_interval(matrix_interval [a,b])`,
  REWRITE_TAC[is_matrix_interval; IN_MATRIX_INTERVAL] THEN
  MESON_TAC[REAL_LT_TRANS; REAL_LE_TRANS; REAL_LET_TRANS; REAL_LTE_TRANS]);;  
  
let IS_MATRIX_INTERVAL_CONVEX = prove
 (`!s:real^N^M->bool. is_matrix_interval s ==> matrix_convex s`,
  REWRITE_TAC[is_matrix_interval; matrix_convex] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`x:real^N^M`; `y:real^N^M`] THEN
  ASM_SIMP_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(SPECL [`(x:real^N^M)$i$j`; `(y:real^N^M)$i$j`] REAL_LE_TOTAL) THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&1 * a <= b /\ b <= &1 * c ==> a <= b /\ b <= c`) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[GSYM MATRIX_CMUL_COMPONENT;
               MATRIX_CMUL_ADD_RDISTRIB; MATRIX_ADD_COMPONENT] THEN
  ASM_SIMP_TAC[MATRIX_CMUL_COMPONENT; REAL_LE_LMUL;
               REAL_LE_LADD; REAL_LE_RADD]);;  
  
let MATRIX_CONVEX_INTERVAL = prove
 (`!a b:real^M^N. matrix_convex(matrix_interval [a,b]) /\ matrix_convex(matrix_interval (a,b))`,
  SIMP_TAC[IS_MATRIX_INTERVAL_CONVEX; IS_MATRIX_INTERVAL_INTERVAL]);;  
  
let MATRIX_CONNECTED_PATH_IMAGE = prove
 (`!g. matrix_path g ==> matrix_connected(matrix_path_image g)`,
  REWRITE_TAC[matrix_path; matrix_path_image] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MATRIX_CONNECTED_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[MATRIX_CONVEX_CONNECTED; MATRIX_CONVEX_INTERVAL]);;
  
let MATRIX_COMPACT_PATH_IMAGE = prove
 (`!g. matrix_path g ==> matrix_compact(matrix_path_image g)`,
  REWRITE_TAC[matrix_path; matrix_path_image] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MATRIX_COMPACT_CONTINUOUS_IMAGE THEN
  ASM_REWRITE_TAC[COMPACT_MATRIX_INTERVAL]);;

let MATRIX_BOUNDED_PATH_IMAGE = prove
 (`!g. matrix_path g ==> matrix_bounded(matrix_path_image g)`,
  MESON_TAC[MATRIX_COMPACT_PATH_IMAGE; MATRIX_COMPACT_IMP_BOUNDED]);;

let MATRIX_CLOSED_PATH_IMAGE = prove
 (`!g. matrix_path g ==> matrix_closed(matrix_path_image g)`,
  MESON_TAC[MATRIX_COMPACT_PATH_IMAGE; MATRIX_COMPACT_IMP_CLOSED]);;

let MATRIX_CONNECTED_SIMPLE_PATH_IMAGE = prove
 (`!g. matrix_simple_path g ==> matrix_connected(matrix_path_image g)`,
  MESON_TAC[MATRIX_CONNECTED_PATH_IMAGE; MATRIX_SIMPLE_PATH_IMP_PATH]);;

let MATRIX_COMPACT_SIMPLE_PATH_IMAGE = prove
 (`!g. matrix_simple_path g ==> matrix_compact(matrix_path_image g)`,
  MESON_TAC[MATRIX_COMPACT_PATH_IMAGE; MATRIX_SIMPLE_PATH_IMP_PATH]);;

let MATRIX_BOUNDED_SIMPLE_PATH_IMAGE = prove
 (`!g. matrix_simple_path g ==> matrix_bounded(matrix_path_image g)`,
  MESON_TAC[MATRIX_BOUNDED_PATH_IMAGE; MATRIX_SIMPLE_PATH_IMP_PATH]);;

let MATRIX_CLOSED_SIMPLE_PATH_IMAGE = prove
 (`!g. matrix_simple_path g ==> matrix_closed(matrix_path_image g)`,
  MESON_TAC[MATRIX_CLOSED_PATH_IMAGE; MATRIX_SIMPLE_PATH_IMP_PATH]);;

let MATRIX_CONNECTED_ARC_IMAGE = prove
 (`!g. matrix_arc g ==> matrix_connected(matrix_path_image g)`,
  MESON_TAC[MATRIX_CONNECTED_PATH_IMAGE; MATRIX_ARC_IMP_PATH]);;

let MATRIX_COMPACT_ARC_IMAGE = prove
 (`!g. matrix_arc g ==> matrix_compact(matrix_path_image g)`,
  MESON_TAC[MATRIX_COMPACT_PATH_IMAGE; MATRIX_ARC_IMP_PATH]);;

let MATRIX_BOUNDED_ARC_IMAGE = prove
 (`!g. matrix_arc g ==> matrix_bounded(matrix_path_image g)`,
  MESON_TAC[MATRIX_BOUNDED_PATH_IMAGE; MATRIX_ARC_IMP_PATH]);;

let MATRIX_CLOSED_ARC_IMAGE = prove
 (`!g. matrix_arc g ==> matrix_closed(matrix_path_image g)`,
  MESON_TAC[MATRIX_CLOSED_PATH_IMAGE; MATRIX_ARC_IMP_PATH]);;

let MATRIX_PATHSTART_COMPOSE = prove
 (`!f p. matrix_pathstart(f o p) = f(matrix_pathstart p)`,
  REWRITE_TAC[matrix_pathstart; o_THM]);;

let MATRIX_PATHFINISH_COMPOSE = prove
 (`!f p. matrix_pathfinish(f o p) = f(matrix_pathfinish p)`,
  REWRITE_TAC[matrix_pathfinish; o_THM]);;

let MATRIX_PATH_IMAGE_COMPOSE = prove
 (`!f p. matrix_path_image (f o p) = IMAGE f (matrix_path_image p)`,
  REWRITE_TAC[matrix_path_image; IMAGE_o]);;

let MATRIX_PATH_COMPOSE_REVERSEPATH = prove
 (`!f p. f o matrix_reversepath p = matrix_reversepath(f o p)`,
  REWRITE_TAC[matrix_reversepath; o_DEF; FUN_EQ_THM] THEN MESON_TAC[]);;  
  
(* ------------------------------------------------------------------------- *)
(* Path component, considered as a "joinability" relation (from Tom Hales).  *)
(* ------------------------------------------------------------------------- *)

let matrix_path_component = new_definition
 `matrix_path_component s x y <=>
        ?g. matrix_path g /\ matrix_path_image g SUBSET s /\
            matrix_pathstart g = x /\ matrix_pathfinish g = y`;;

let matrix_path_components = new_definition
 `matrix_path_components s = {matrix_path_component s x | x | x IN s}`;;

let PATH_COMPONENT_OF_MATRIX_SPACE = prove
 (`!s:real^N^M->bool.
        path_component_of (subtopology matrix_space s) = matrix_path_component s`,
  REWRITE_TAC[FUN_EQ_THM; matrix_path_component; path_component_of] THEN
  REWRITE_TAC[PATH_IN_MATRIX_SPACE; matrix_pathstart; matrix_pathfinish; GSYM DROP2_MAT] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[o_THM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1^1->real^N^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(g:real^1^1->real^N^M) o lift_lift` THEN
  ASM_REWRITE_TAC[o_DEF; LIFT2_DROP; ETA_AX]);;

let PATH_COMPONENTS_OF_MATRIX_SPACE = prove
 (`!s:real^N^M->bool.
        path_components_of (subtopology matrix_space s) = matrix_path_components s`,
  REWRITE_TAC[path_components_of; matrix_path_components] THEN
  REWRITE_TAC[TOPSPACE_MATRIX_SPACE_SUBTOPOLOGY; PATH_COMPONENT_OF_MATRIX_SPACE]);;

let MATRIX_PATH_COMPONENT_IN = prove
 (`!s x y. matrix_path_component s x y ==> x IN s /\ y IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM PATH_COMPONENT_OF_MATRIX_SPACE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP PATH_COMPONENT_IN_TOPSPACE) THEN
  REWRITE_TAC[TOPSPACE_MATRIX_SPACE_SUBTOPOLOGY]);;

let MATRIX_PATH_COMPONENT_REFL_EQ = prove
 (`!s x:real^N^M. matrix_path_component s x x <=> x IN s`,
  REWRITE_TAC[GSYM PATH_COMPONENT_OF_MATRIX_SPACE; PATH_COMPONENT_OF_REFL] THEN
  REWRITE_TAC[TOPSPACE_MATRIX_SPACE_SUBTOPOLOGY]);;

let MATRIX_PATH_COMPONENT_REFL = prove
 (`!s x:real^N^M. x IN s ==> matrix_path_component s x x`,
  REWRITE_TAC[MATRIX_PATH_COMPONENT_REFL_EQ]);;

let MATRIX_PATH_COMPONENT_SYM_EQ = prove
 (`!s x y. matrix_path_component s x y <=> matrix_path_component s y x`,
  REWRITE_TAC[GSYM PATH_COMPONENT_OF_MATRIX_SPACE] THEN
  MATCH_ACCEPT_TAC PATH_COMPONENT_OF_SYM);;

let MATRIX_PATH_COMPONENT_SYM = prove
 (`!s x y:real^N^M. matrix_path_component s x y ==> matrix_path_component s y x`,
  MESON_TAC[MATRIX_PATH_COMPONENT_SYM_EQ]);;

let MATRIX_PATH_COMPONENT_TRANS = prove
 (`!s x y:real^N^M.
      matrix_path_component s x y /\ matrix_path_component s y z ==> matrix_path_component s x z`,
  REWRITE_TAC[GSYM PATH_COMPONENT_OF_MATRIX_SPACE; PATH_COMPONENT_OF_TRANS]);;

let MATRIX_PATH_COMPONENT_OF_SUBSET = prove
 (`!s t x. s SUBSET t /\ matrix_path_component s x y ==> matrix_path_component t x y`,
  REWRITE_TAC[matrix_path_component] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Can also consider it as a set, as the name suggests.                      *)
(* ------------------------------------------------------------------------- *)

let MATRIX_PATH_COMPONENT_SET = prove
 (`!s x. matrix_path_component s x =
        { y | ?g. matrix_path g /\ matrix_path_image g SUBSET s /\
                matrix_pathstart g = x /\ matrix_pathfinish g = y }`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REWRITE_TAC[IN; matrix_path_component]);;

let MATRIX_PATH_COMPONENT_SUBSET = prove
 (`!s x. (matrix_path_component s x) SUBSET s`,
  REWRITE_TAC[SUBSET; IN] THEN MESON_TAC[MATRIX_PATH_COMPONENT_IN; IN]);;

let MATRIX_PATH_COMPONENT_EQ_EMPTY = prove
 (`!s x. matrix_path_component s x = {} <=> ~(x IN s)`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
  MESON_TAC[IN; MATRIX_PATH_COMPONENT_REFL; MATRIX_PATH_COMPONENT_IN]);;

let MATRIX_PATH_COMPONENT_EMPTY = prove
 (`!x. matrix_path_component {} x = {}`,
  REWRITE_TAC[MATRIX_PATH_COMPONENT_EQ_EMPTY; NOT_IN_EMPTY]);;

let UNIONS_MATRIX_PATH_COMPONENT = prove
 (`!s:real^N^M->bool. UNIONS {matrix_path_component s x |x| x IN s} = s`,
  GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM TOPSPACE_MATRIX_SPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[GSYM UNIONS_PATH_COMPONENTS_OF] THEN
  REWRITE_TAC[path_components_of; TOPSPACE_MATRIX_SPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[PATH_COMPONENT_OF_MATRIX_SPACE]);;
  
let MATRIX_PATH_COMPONENT_TRANSLATION = prove
 (`!a:real^M^N s x. matrix_path_component (IMAGE (\x. a + x) s) (a + x) =
                IMAGE (\x. a + x) (matrix_path_component s x)`,
  REWRITE_TAC[MATRIX_PATH_COMPONENT_SET] THEN MATRIX_GEOM_TRANSLATE_TAC[] THEN
  SIMP_TAC[GSYM SIMPLE_IMAGE_GEN] THEN REPEAT GEN_TAC THEN
  SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN 
  SIMP_TAC[SUBSET_IMAGE] THEN STRIP_TAC THENL 
  [EXISTS_TAC `(\x:real^M^N. (--a) + x) o (g:real^1^1->real^M^N)`;
   EXISTS_TAC `(\x:real^M^N. a + x) o (g:real^1^1->real^M^N)`] THEN
  ASM_SIMP_TAC[MATRIX_PATH_IMAGE_TRANSLATION;MATRIX_PATHFINISH_TRANSLATION;MATRIX_PATHSTART_TRANSLATION;MATRIX_PATH_TRANSLATION_EQ] THENL
  [ALL_TAC;EXISTS_TAC `matrix_path_image (g:real^1^1->real^M^N)`] THEN
  ASM_SIMP_TAC[MATRIX_ADD_ASSOC;MATRIX_ADD_LNEG;MATRIX_ADD_LID;GSYM I_DEF;IMAGE_I;GSYM IMAGE_o;o_DEF]);;

add_translation_invariants [MATRIX_PATH_COMPONENT_TRANSLATION];;

(*
let MATRIX_PATH_COMPONENT_LINEAR_IMAGE = prove
 (`!f s x:real^M^N. mlinear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
           ==> matrix_path_component (IMAGE f s) (f x) =
               IMAGE f (matrix_path_component s x)`,
  REWRITE_TAC[MATRIX_PATH_COMPONENT_SET] THEN
  GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [MATRIX_PATH_COMPONENT_LINEAR_IMAGE];;
*)
(* ------------------------------------------------------------------------- *)
(* Path connectedness of a matrix space.                                            *)
(* ------------------------------------------------------------------------- *)

let matrix_path_connected = new_definition
 `matrix_path_connected s <=>
        !x y. x IN s /\ y IN s
              ==> ?g. matrix_path g /\ (matrix_path_image g) SUBSET s /\ matrix_pathstart g = x /\ matrix_pathfinish g = y`;;

let MATRIX_PATH_CONNECTED_IFF_PATH_COMPONENT = prove
 (`!s. matrix_path_connected s <=> !x y. x IN s /\ y IN s ==> matrix_path_component s x y`,
  REWRITE_TAC[matrix_path_connected; matrix_path_component]);;

let PATH_CONNECTED_IN_MATRIX_SPACE = prove
 (`!s:real^M^N->bool. path_connected_in matrix_space s <=> matrix_path_connected s`,
  REWRITE_TAC[path_connected_in; PATH_CONNECTED_SPACE_IFF_PATH_COMPONENT] THEN
  REWRITE_TAC[PATH_COMPONENT_OF_MATRIX_SPACE; TOPSPACE_MATRIX_SPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[GSYM MATRIX_PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
  REWRITE_TAC[TOPSPACE_MATRIX_SPACE; SUBSET_UNIV]);;

let PATH_CONNECTED_SPACE_MATRIX_SPACE_SUBTOPOLOGY = prove
 (`!s:real^M^N->bool.
       path_connected_space(subtopology matrix_space s) <=> matrix_path_connected s`,
  REWRITE_TAC[GSYM PATH_CONNECTED_IN_TOPSPACE] THEN
  REWRITE_TAC[PATH_CONNECTED_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[PATH_CONNECTED_IN_MATRIX_SPACE] THEN
  REWRITE_TAC[TOPSPACE_MATRIX_SPACE_SUBTOPOLOGY; SUBSET_REFL]);;

let MATRIX_PATH_CONNECTED_IMP_PATH_COMPONENT = prove
 (`!s a b:real^M^N.
     matrix_path_connected s /\ a IN s /\ b IN s ==> matrix_path_component s a b`,
  MESON_TAC[MATRIX_PATH_CONNECTED_IFF_PATH_COMPONENT]);;

let MATRIX_PATH_CONNECTED_COMPONENT_SET = prove
 (`!s. matrix_path_connected s <=>
        !x. x IN s ==> matrix_path_component s x = s`,
  REWRITE_TAC[MATRIX_PATH_CONNECTED_IFF_PATH_COMPONENT; GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[MATRIX_PATH_COMPONENT_SUBSET] THEN SET_TAC[]);;

let MATRIX_PATH_COMPONENT_MONO = prove
 (`!s t x. s SUBSET t ==> (matrix_path_component s x) SUBSET (matrix_path_component t x)`,
  REWRITE_TAC[MATRIX_PATH_COMPONENT_SET] THEN SET_TAC[]);;

let MATRIX_PATH_COMPONENT_MAXIMAL = prove
 (`!s t x. x IN t /\ matrix_path_connected t /\ t SUBSET s
           ==> t SUBSET (matrix_path_component s x)`,
  REWRITE_TAC[matrix_path_connected; MATRIX_PATH_COMPONENT_SET; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let MATRIX_PATH_COMPONENT_EQ = prove
 (`!s x y. y IN matrix_path_component s x
           ==> matrix_path_component s y = matrix_path_component s x`,
  REWRITE_TAC[EXTENSION; IN] THEN
  MESON_TAC[MATRIX_PATH_COMPONENT_SYM; MATRIX_PATH_COMPONENT_TRANS]);;

let MATRIX_PATH_CONNECTED_PATH_IMAGE = prove
 (`!p:real^1^1->real^M^N. matrix_path p ==> matrix_path_connected(matrix_path_image p)`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_PATH_PATH_IN] THEN
  DISCH_THEN(MP_TAC o MATCH_MP PATH_CONNECTED_IN_PATH_IMAGE) THEN
  REWRITE_TAC[IMAGE_o; IMAGE_LIFT2_REAL_INTERVAL; LIFT_LIFT_NUM] THEN
  REWRITE_TAC[PATH_CONNECTED_IN_MATRIX_SPACE; matrix_path_image]);;

let MATRIX_PATHSTART_IN_PATH_IMAGE = prove
 (`!g. (matrix_pathstart g) IN matrix_path_image g`,
  GEN_TAC THEN REWRITE_TAC[matrix_pathstart; matrix_path_image] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN
  REWRITE_TAC[IN_MATRIX_INTERVAL_1; DROP2_MAT; REAL_POS]);;

let MATRIX_PATH_COMPONENT_PATH_IMAGE_PATHSTART = prove
 (`!p x:real^M^N.
        matrix_path p /\ x IN matrix_path_image p
        ==> matrix_path_component (matrix_path_image p) (matrix_pathstart p) x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MATRIX_PATH_CONNECTED_PATH_IMAGE) THEN
  REWRITE_TAC[MATRIX_PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[MATRIX_PATHSTART_IN_PATH_IMAGE]);;
  
let MATRIX_PATH_CONNECTED_PATH_COMPONENT = prove
 (`!s x:real^M^N. matrix_path_connected(matrix_path_component s x)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`subtopology matrix_space (s:real^M^N->bool)`; `x:real^M^N`]
        PATH_CONNECTED_IN_PATH_COMPONENT_OF) THEN
  REWRITE_TAC[PATH_CONNECTED_IN_SUBTOPOLOGY; PATH_CONNECTED_IN_MATRIX_SPACE] THEN
  SIMP_TAC[PATH_COMPONENT_OF_MATRIX_SPACE]);;

let MATRIX_PATH_COMPONENT = prove
 (`!s x y:real^M^N.
        matrix_path_component s x y <=>
        ?t. matrix_path_connected t /\ t SUBSET s /\ x IN t /\ y IN t`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `matrix_path_component s (x:real^M^N)` THEN
    REWRITE_TAC[MATRIX_PATH_CONNECTED_PATH_COMPONENT; MATRIX_PATH_COMPONENT_SUBSET] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MATRIX_PATH_COMPONENT_IN) THEN
    ASM_SIMP_TAC[IN; MATRIX_PATH_COMPONENT_REFL_EQ];
    REWRITE_TAC[matrix_path_component] THEN ASM_MESON_TAC[matrix_path_connected; SUBSET]]);;

let MATRIX_PATH_COMPONENT_PATH_COMPONENT = prove
 (`!s x:real^M^N.
        matrix_path_component (matrix_path_component s x) x = matrix_path_component s x`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(x:real^M^N) IN s` THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    SIMP_TAC[MATRIX_PATH_COMPONENT_MONO; MATRIX_PATH_COMPONENT_SUBSET] THEN
    MATCH_MP_TAC MATRIX_PATH_COMPONENT_MAXIMAL THEN
    REWRITE_TAC[SUBSET_REFL; MATRIX_PATH_CONNECTED_PATH_COMPONENT] THEN
    ASM_REWRITE_TAC[IN; MATRIX_PATH_COMPONENT_REFL_EQ];
    MATCH_MP_TAC(SET_RULE `s = {} /\ t = {} ==> s = t`) THEN
    ASM_REWRITE_TAC[MATRIX_PATH_COMPONENT_EQ_EMPTY] THEN
    ASM_MESON_TAC[SUBSET; MATRIX_PATH_COMPONENT_SUBSET]]);;

(*
let MATRIX_PATH_CONNECTED_LINEPATH = prove
 (`!s a b:real^M^N. matrix_segment[a,b] SUBSET s ==> matrix_path_component s a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[matrix_path_component] THEN
  EXISTS_TAC `linepath(a:real^M^N,b)` THEN
  ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_LINEPATH] THEN
  ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH]);;
*)

let MATRIX_PATH_COMPONENT_DISJOINT = prove
 (`!s a b. DISJOINT (matrix_path_component s a) (matrix_path_component s b) <=>
             ~(a IN matrix_path_component s b)`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN] THEN MESON_TAC[MATRIX_PATH_COMPONENT_SYM; MATRIX_PATH_COMPONENT_TRANS]);;

let MATRIX_PATH_COMPONENT_EQ_EQ = prove
 (`!s x y:real^M^N.
        matrix_path_component s x = matrix_path_component s y <=>
        ~(x IN s) /\ ~(y IN s) \/
        x IN s /\ y IN s /\ matrix_path_component s x y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(y:real^M^N) IN s` THENL
   [ASM_CASES_TAC `(x:real^M^N) IN s` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN
      ASM_MESON_TAC[MATRIX_PATH_COMPONENT_TRANS; MATRIX_PATH_COMPONENT_REFL;MATRIX_PATH_COMPONENT_SYM];
      ASM_MESON_TAC[MATRIX_PATH_COMPONENT_EQ_EMPTY]];
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM MATRIX_PATH_COMPONENT_EQ_EMPTY]) THEN
    ASM_REWRITE_TAC[MATRIX_PATH_COMPONENT_EQ_EMPTY] THEN
    ONCE_REWRITE_TAC[MATRIX_PATH_COMPONENT_SYM_EQ] THEN
    ASM_REWRITE_TAC[EMPTY] THEN ASM_MESON_TAC[MATRIX_PATH_COMPONENT_EQ_EMPTY]]);;

let MATRIX_PATH_COMPONENT_UNIQUE = prove
 (`!s c x:real^M^N.
        x IN c /\ c SUBSET s /\ matrix_path_connected c /\
        (!c'. x IN c' /\ c' SUBSET s /\ matrix_path_connected c'
              ==> c' SUBSET c)
        ==> matrix_path_component s x = c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[MATRIX_PATH_COMPONENT_SUBSET; MATRIX_PATH_CONNECTED_PATH_COMPONENT] THEN
    REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[MATRIX_PATH_COMPONENT_REFL_EQ] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC MATRIX_PATH_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]]);;

let MATRIX_PATH_COMPONENT_INTERMEDIATE_SUBSET = prove
 (`!t u a:real^M^N.
        matrix_path_component u a SUBSET t /\ t SUBSET u
        ==> matrix_path_component t a = matrix_path_component u a`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(a:real^M^N) IN u` THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_PATH_COMPONENT_UNIQUE THEN
    ASM_REWRITE_TAC[MATRIX_PATH_CONNECTED_PATH_COMPONENT] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MATRIX_PATH_COMPONENT_REFL; IN]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_PATH_COMPONENT_MAXIMAL THEN
    ASM SET_TAC[];
    ASM_MESON_TAC[MATRIX_PATH_COMPONENT_EQ_EMPTY; SUBSET]]);;

let COMPLEMENT_MATRIX_PATH_COMPONENT_UNIONS = prove
 (`!s x:real^M^N.
     s DIFF matrix_path_component s x =
     UNIONS({matrix_path_component s y | y | y IN s} DELETE (matrix_path_component s x))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM UNIONS_MATRIX_PATH_COMPONENT] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s DELETE a ==> DISJOINT a x)
     ==> UNIONS s DIFF a = UNIONS (s DELETE a)`) THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC; IN_DELETE] THEN
  SIMP_TAC[MATRIX_PATH_COMPONENT_DISJOINT; MATRIX_PATH_COMPONENT_EQ_EQ] THEN
  MESON_TAC[IN; SUBSET; MATRIX_PATH_COMPONENT_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Special case of straight-line paths.                                      *)
(* ------------------------------------------------------------------------- *)

let matrix_linepath = new_definition
 `matrix_linepath(a:real^N^M,b) = \x. (&1 - drop_drop x) %% a + drop_drop x %% b`;;

let MATRIX_LINEPATH_TRANSLATION = prove
 (`!a b c:real^N^M. matrix_linepath(a + b,a + c) = (\x. a + x) o matrix_linepath(b,c)`,
  REWRITE_TAC[matrix_linepath; o_THM; FUN_EQ_THM] THEN CMATRIX_ARITH_TAC);;

add_translation_invariants [MATRIX_LINEPATH_TRANSLATION];;

let MATRIX_LINEPATH_LINEAR_IMAGE = prove
 (`!f:real^N^M->real^P^Q. mlinear f ==> !b c. matrix_linepath(f b,f c) = f o matrix_linepath(b,c)`,
  REWRITE_TAC[matrix_linepath; o_THM; FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLINEAR_ADD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLINEAR_CMUL) THEN
  ASM_REWRITE_TAC[] THEN CMATRIX_ARITH_TAC);;

add_linear_invariants [MATRIX_LINEPATH_LINEAR_IMAGE];;

let MATRIX_PATHSTART_LINEPATH = prove
 (`!a b:real^N^M. matrix_pathstart(matrix_linepath(a,b)) = a`,
  REWRITE_TAC[matrix_linepath; matrix_pathstart; DROP2_MAT] THEN CMATRIX_ARITH_TAC);;

let MATRIX_PATHFINISH_LINEPATH = prove
 (`!a b:real^N^M. matrix_pathfinish(matrix_linepath(a,b)) = b`,
  REWRITE_TAC[matrix_linepath; matrix_pathfinish; DROP2_MAT] THEN CMATRIX_ARITH_TAC);;

let MATRIX_CONTINUOUS_LINEPATH_AT = prove
 (`!a b:real^N^M x. matrix_linepath(a,b) matrix_continuous (matrix_at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[matrix_linepath] THEN
  REWRITE_TAC[CMATRIX_ARITH `(&1 - u) %% (x:real^N^M) + y = x + u %% --x + y`] THEN
  MATCH_MP_TAC MATRIX_CONTINUOUS_ADD THEN REWRITE_TAC[MATRIX_CONTINUOUS_CONST] THEN
  MATCH_MP_TAC MATRIX_CONTINUOUS_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC MATRIX_CONTINUOUS_MMUL THEN
  REWRITE_TAC[o_DEF; LIFT2_DROP; MATRIX_CONTINUOUS_AT_ID]);;

let MATRIX_CONTINUOUS_ON_LINEPATH = prove
 (`!a b:real^N^M s. matrix_linepath(a,b) matrix_continuous_on s`,
  MESON_TAC[MATRIX_CONTINUOUS_AT_IMP_CONTINUOUS_ON; MATRIX_CONTINUOUS_LINEPATH_AT]);;

let MATRIX_PATH_LINEPATH = prove
 (`!a b:real^N^M. matrix_path(matrix_linepath(a,b))`,
  REWRITE_TAC[matrix_path; MATRIX_CONTINUOUS_ON_LINEPATH]);;

let MATRIX_PATH_IMAGE_LINEPATH = prove
 (`!a b:real^N^M. matrix_path_image(matrix_linepath (a,b)) = matrix_segment[a,b]`,
  REWRITE_TAC[matrix_segment; matrix_path_image; matrix_linepath] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_MATRIX_INTERVAL] THEN
  SIMP_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`; MAT_COMPONENT; ARITH] THEN
  REWRITE_TAC[EXISTS_LIFT2; GSYM drop_drop; LIFT2_DROP] THEN MESON_TAC[]);;

let MATRIX_REVERSEPATH_LINEPATH = prove
 (`!a b:real^N^M. matrix_reversepath(matrix_linepath(a,b)) = matrix_linepath(b,a)`,
  REWRITE_TAC[matrix_reversepath; matrix_linepath; DROP2_SUB; DROP2_MAT; FUN_EQ_THM] THEN
  CMATRIX_ARITH_TAC);;

let MATRIX_ARC_LINEPATH = prove
 (`!a b:real^N^M. ~(a = b) ==> matrix_arc(matrix_linepath(a,b))`,
  REWRITE_TAC[matrix_arc; MATRIX_PATH_LINEPATH] THEN REWRITE_TAC[matrix_linepath] THEN
  REWRITE_TAC[CMATRIX_ARITH
   `(&1 - x) %% a + x %% b:real^N^M = (&1 - y) %% a + y %% b <=>
    (x - y) %% (a - b) = mat 0`] THEN
  SIMP_TAC[MATRIX_CMUL_EQ_0; MATRIX_SUB_EQ; DROP2_EQ; REAL_SUB_0]);;

let MATRIX_SIMPLE_PATH_LINEPATH = prove
 (`!a b:real^N^M. ~(a = b) ==> matrix_simple_path(matrix_linepath(a,b))`,
  MESON_TAC[MATRIX_ARC_IMP_SIMPLE_PATH; MATRIX_ARC_LINEPATH]);;

let MATRIX_SIMPLE_PATH_LINEPATH_EQ = prove
 (`!a b:real^M^N. matrix_simple_path(matrix_linepath(a,b)) <=> ~(a = b)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[MATRIX_SIMPLE_PATH_LINEPATH] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[matrix_simple_path] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[matrix_linepath; GSYM MATRIX_CMUL_ADD_RDISTRIB] THEN
  DISCH_THEN(MP_TAC o SPECL [`lift_lift(&0)`; `lift_lift(&1 / &2)`]) THEN
  REWRITE_TAC[IN_MATRIX_INTERVAL_1; LIFT2_DROP; GSYM DROP2_EQ; DROP2_MAT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let MATRIX_ARC_LINEPATH_EQ = prove
 (`!a b:real^N^M. matrix_arc(matrix_linepath(a,b)) <=> ~(a = b)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[MATRIX_ARC_LINEPATH] THEN
  MESON_TAC[MATRIX_SIMPLE_PATH_LINEPATH_EQ; MATRIX_ARC_IMP_SIMPLE_PATH]);;

let MATRIX_LINEPATH_REFL = prove
 (`!a:real^N^M. matrix_linepath(a,a) = \x. a`,
  REWRITE_TAC[matrix_linepath; CMATRIX_ARITH `(&1 - u) %% x + u %% x:real^M^N = x`]);;

let MATRIX_PATH_IMAGE_CONST = prove
 (`!a:real^M^N. matrix_path_image (\x. a) = {a}`,
  REWRITE_TAC[GSYM MATRIX_LINEPATH_REFL; MATRIX_PATH_IMAGE_LINEPATH] THEN
  REWRITE_TAC[MATRIX_SEGMENT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Path-connectness of special matrix lie group                                      *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_MATRIX_EQ = prove
    (`!A:real^N^N. orthogonal_matrix A <=> matrix_inv A = transp A /\ invertible A`,
    GEN_TAC THEN EQ_TAC THENL
    [SIMP_TAC[ORTHOGONAL_MATRIX_INV;ORTHOGONAL_MATRIX_IMP_INVERTIBLE];
     REPEAT STRIP_TAC THEN REWRITE_TAC[orthogonal_matrix] THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[MATRIX_INV]]);;

let CMAT_IN_MLG_SET = prove
    (`!G:(N)mlg. (cmat 1) IN (mlg_set G)`,
    SIMP_TAC[GSYM MLG_GROUP;GROUP_ID]);;

let CMATRIX_INV_IN_MLG_SET = prove
    (`!G:(N)mlg x. x IN mlg_set G ==> cmatrix_inv x IN mlg_set G`,
    SIMP_TAC[GSYM MLG_GROUP;GROUP_INV]);;
    
let CMATRIX_MUL_IN_MLG_SET = prove
    (`!G:(N)mlg x y. x IN mlg_set G /\ y IN mlg_set G ==> (x ** y) IN mlg_set G`,
    SIMP_TAC[GSYM MLG_GROUP;GROUP_MUL]);;
    
let MAT_IN_MLG_SET = prove
    (`!G:(N)mlg. IMAGE (Cx_matrix o Re_matrix) (mlg_set G) = (mlg_set G) ==> (mat 1) IN (IMAGE Re_matrix (mlg_set G))`,
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPEC `G:(N)mlg` ISMLG_MLG_SET) THEN
    SIMP_TAC[ismlg;ismlg_complex;ismlg_real] THEN
    ASM_SIMP_TAC[subgroup_of;GSYM general_linear_group;GENERAL_LINEAR_GROUP]);;

let MATRIX_INV_IN_MLG_SET = prove
    (`!G:(N)mlg x. IMAGE (Cx_matrix o Re_matrix) (mlg_set G) = (mlg_set G) /\ x IN (IMAGE Re_matrix (mlg_set G)) ==> matrix_inv x IN (IMAGE Re_matrix (mlg_set G))`,
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPEC `G:(N)mlg` ISMLG_MLG_SET) THEN
    SIMP_TAC[ismlg;ismlg_complex;ismlg_real] THEN
    ASM_SIMP_TAC[subgroup_of;GSYM general_linear_group;GENERAL_LINEAR_GROUP]);;
    
let MATRIX_INV_IN_MLG_SET_EQ = prove
    (`!G:(N)mlg x. IMAGE (Cx_matrix o Re_matrix) (mlg_set G) = (mlg_set G) ==> (x IN (IMAGE Re_matrix (mlg_set G)) <=> matrix_inv x IN (IMAGE Re_matrix (mlg_set G)))`,
    MESON_TAC[MATRIX_INV_IN_MLG_SET;MATRIX_INV_INV]);;
    
let MATRIX_MUL_IN_MLG_SET = prove
    (`!G:(N)mlg x y. IMAGE (Cx_matrix o Re_matrix) (mlg_set G) = (mlg_set G) /\ x IN (IMAGE Re_matrix (mlg_set G)) /\ y IN (IMAGE Re_matrix (mlg_set G)) ==> (x ** y) IN (IMAGE Re_matrix (mlg_set G))`,
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPEC `G:(N)mlg` ISMLG_MLG_SET) THEN
    SIMP_TAC[ismlg;ismlg_complex;ismlg_real] THEN
    ASM_SIMP_TAC[subgroup_of;GSYM general_linear_group;GENERAL_LINEAR_GROUP]);;

let MATRIX_CONTINUOUS_COMPONENTWISE_LIFT2 = prove
 (`!net f:A->real^N^M.
        f matrix_continuous net <=>
        !i j. (1 <= i /\ i <= dimindex(:M)) /\ (1 <= j /\ j <= dimindex(:N))
            ==> (\x. lift_lift((f x)$i$j)) matrix_continuous net`,
  REWRITE_TAC[matrix_continuous; GSYM MATRIX_LIM_COMPONENTWISE_LIFT2]);;    

let MATRIX_INV_CONTINUOUS_ON_INVERTIBLE = prove
    (` matrix_inv matrix_continuous_on {A:real^N^N | invertible A}`,
    let lem = MESON [GSYM REAL_LT_RMUL_EQ] `!z x y. &0 < z ==> (x < y <=> x * z < y * z)` in
    let lem2 = MESON [GSYM REAL_LE_RMUL_EQ] `!z x y. &0 < z ==> (x <= y <=> x * z <= y * z)` in
    SIMP_TAC[matrix_continuous_on;matrix_dist;IN_ELIM_THM] THEN
    X_GEN_TAC `A:real^N^N` THEN REPEAT STRIP_TAC THEN 
    EXISTS_TAC `e * inv((e + fnorm (matrix_inv A)) * (fnorm (matrix_inv (A:real^N^N))))` THEN
    SUBGOAL_THEN `&0 < fnorm (matrix_inv (A:real^N^N))` ASSUME_TAC THENL
    [SIMP_TAC[FNORM_POS_LT;MATRIX_INV_EQ_0] THEN
     UNDISCH_TAC `invertible (A:real^N^N)` THEN
     CONV_TAC CONTRAPOS_CONV THEN
     SIMP_TAC[INVERTIBLE_DET_NZ;DET_0];ALL_TAC] THEN
    CONJ_TAC THENL 
    [ASM_MESON_TAC[REAL_LT_MUL;REAL_LT_INV;REAL_LT_ADD];ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(fnorm(matrix_inv A:real^N^N) * fnorm(matrix_inv A) * fnorm(x' - A)) * inv(&1 - fnorm(matrix_inv A) * fnorm(x' - A))` THEN
    SUBGOAL_THEN `&0 < &1 - fnorm(matrix_inv A:real^N^N) * fnorm(x' - A)` ASSUME_TAC THENL 
    [SIMP_TAC[REAL_SUB_LT] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
     ASM_SIMP_TAC[ISPECL [`inv(fnorm(matrix_inv A:real^N^N))`;`fnorm(x' - A:real^N^N) * fnorm(matrix_inv A:real^N^N)`] lem;REAL_LT_INV;REAL_MUL_RINV;REAL_MUL_RID;GSYM REAL_MUL_ASSOC;REAL_LT_IMP_NZ] THEN
     MATCH_MP_TAC REAL_LT_TRANS THEN
     EXISTS_TAC `e * inv((e + fnorm (matrix_inv A)) * (fnorm (matrix_inv (A:real^N^N))))` THEN
     ASM_SIMP_TAC[REAL_INV_MUL;REAL_MUL_ASSOC] THEN
     MATCH_MP_TAC REAL_LT_RMUL THEN
     ASM_SIMP_TAC[ISPECL [`e + fnorm(matrix_inv A:real^N^N)`;`e * inv (e + fnorm (matrix_inv A:real^N^N))`] lem;REAL_LT_ADD;REAL_MUL_LINV;GSYM REAL_MUL_ASSOC;REAL_LT_IMP_NZ;REAL_LT_INV] THEN
     ASM_SIMP_TAC[REAL_ARITH `&0 < x /\ &0 < y ==> x < x + y`;REAL_MUL_LID;REAL_MUL_RID];ALL_TAC] THEN
    CONJ_TAC THENL
    [ASM_SIMP_TAC[ISPECL [`&1 - fnorm(matrix_inv A:real^N^N) * fnorm(x' - A)`;`fnorm (matrix_inv x' - matrix_inv A:real^N^N)`] lem2;REAL_MUL_LINV;GSYM REAL_MUL_ASSOC;REAL_LT_IMP_NZ] THEN
     REWRITE_TAC[REAL_ARITH `a * (&1 - b * c) <= b * b * c * &1 <=> a <= a * (c * b) + b * c * b`] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `fnorm ((matrix_inv x' - matrix_inv A:real^N^N) **  (x' - A) **  (matrix_inv A) + (matrix_inv A) ** (x' - A) ** (matrix_inv A))` THEN
     CONJ_TAC THENL
     [ASM_SIMP_TAC[MATRIX_SUB_LDISTRIB;MATRIX_SUB_RDISTRIB;MATRIX_INV;MATRIX_SUB_ADD] THEN
      ASM_SIMP_TAC[MATRIX_MUL_ASSOC;MATRIX_INV;MATRIX_MUL_RID;MATRIX_MUL_LID] THEN
      SIMP_TAC[FNORM_SUB_SYM;REAL_LE_REFL];ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `fnorm ((matrix_inv x' - matrix_inv A:real^N^N) **  (x' - A) **  (matrix_inv A)) + fnorm ((matrix_inv A) ** (x' - A) ** (matrix_inv A))` THEN
     SIMP_TAC[FNORM_TRIANGLE] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
     CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `fnorm (matrix_inv x' - matrix_inv A:real^N^N) *  fnorm ((x' - A) **  (matrix_inv A))`;
      EXISTS_TAC `fnorm (matrix_inv A:real^N^N) * fnorm ((x' - A) ** (matrix_inv A))`] THEN
     SIMP_TAC[FNORM_SUBMULT] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
     SIMP_TAC[FNORM_POS_LE;FNORM_SUBMULT];ALL_TAC] THEN
    ASM_SIMP_TAC[ISPECL [`&1 - fnorm(matrix_inv A:real^N^N) * fnorm(x' - A)`;`(fnorm (matrix_inv A) * fnorm (matrix_inv A:real^N^N) * fnorm (x' - A)) * inv (&1 - fnorm (matrix_inv A) * fnorm (x' - A))`] lem;REAL_MUL_LINV;GSYM REAL_MUL_ASSOC;REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[REAL_ARITH `a * a * b * &1 < e * (&1 - a * b) <=> b * ((e + a) * a) < e`] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    SUBGOAL_THEN `&0 < (e + fnorm (matrix_inv A:real^N^N)) * fnorm (matrix_inv A)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_ADD];ALL_TAC] THEN
    ASM_SIMP_TAC[ISPECL [`(e + fnorm (matrix_inv A:real^N^N)) * fnorm (matrix_inv A)`;`fnorm (x' - A:real^N^N)`] lem;GSYM REAL_MUL_ASSOC;REAL_MUL_LINV;REAL_LT_IMP_NZ;REAL_MUL_RID]);;

let MATRIX_INV_CONTINUOUS_ON_MLG_SET = prove
    (`!G:(N)mlg. IMAGE (Cx_matrix o Re_matrix) (mlg_set G) = (mlg_set G) ==> matrix_inv matrix_continuous_on (IMAGE Re_matrix (mlg_set G))`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `group_carrier(general_linear_group (g:real^N^N))` THEN
    ASM_SIMP_TAC[(REWRITE_RULE [subgroup_of] MLG_SUBGROUP_OF_GLG);GENERAL_LINEAR_GROUP;MATRIX_INV_CONTINUOUS_ON_INVERTIBLE]);;

let MATRIX_PATH_IMAGE_MATRIX_INV = prove
    (`!G:(N)mlg g. 
    IMAGE (Cx_matrix o Re_matrix) (mlg_set G) = (mlg_set G) /\
    matrix_path_image g SUBSET (IMAGE Re_matrix (mlg_set G))
    ==> matrix_path_image (matrix_inv o g) SUBSET (IMAGE Re_matrix (mlg_set G))`,
    SIMP_TAC[MATRIX_PATH_IMAGE_COMPOSE] THEN
    SIMP_TAC[SUBSET;IN_IMAGE] THEN
    ONCE_REWRITE_TAC [GSYM MATRIX_INV_EQ] THEN
    SIMP_TAC[MATRIX_INV_INV;UNWIND_THM1] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `matrix_inv x:real^N^N`) THEN
    ASM_SIMP_TAC[MATRIX_INV_EQ] THEN
    ASM_SIMP_TAC[GSYM MATRIX_INV_IN_MLG_SET_EQ;GSYM IN_IMAGE]);;

let MATRIX_PATH_IMAGE_MATRIX_MUL = prove
    (`!G:(N)mlg g1 g2. 
    IMAGE (Cx_matrix o Re_matrix) (mlg_set G) = (mlg_set G) /\
    matrix_path_image g1 SUBSET (IMAGE Re_matrix (mlg_set G)) /\
    matrix_path_image g2 SUBSET (IMAGE Re_matrix (mlg_set G)) 
    ==> matrix_path_image (\x. g1 x ** g2 x) SUBSET (IMAGE Re_matrix (mlg_set G))`,
    SIMP_TAC[matrix_path_image;SUBSET;IN_IMAGE;LEFT_IMP_EXISTS_THM] THEN
    SIMP_TAC[GSYM IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_MUL_IN_MLG_SET THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(g2:real^1^1->real^N^N) x'`;`x':real^1^1`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(g1:real^1^1->real^N^N) x'`;`x':real^1^1`]) THEN ASM_SIMP_TAC[]);; 

let MATRIX_PATH_COMPONENT_SUBGROUP_OF_MLG = prove
    (`!G:(N)mlg. IMAGE (Cx_matrix o Re_matrix) (mlg_set G) = (mlg_set G) ==> (matrix_path_component ((IMAGE Re_matrix (mlg_set G))) (mat 1)) subgroup_of group_ctor(mlg_group G)`,
    REPEAT STRIP_TAC THEN 
    MP_TAC (ISPEC `mlg_group (G:(N)mlg)` GROUP_CTOR) THEN
    ASM_SIMP_TAC[MLG_GROUP;MLG_SUBGROUP_OF_GLG] THEN
    SIMP_TAC[subgroup_of;MLG_GROUP] THEN
    STRIP_TAC THEN
    SIMP_TAC[MATRIX_PATH_COMPONENT_SUBSET] THEN
    CONJ_TAC THENL
    [SIMP_TAC[MATRIX_PATH_COMPONENT_SET;IN_ELIM_THM] THEN
     EXISTS_TAC `matrix_linepath(mat 1,mat 1):real^1^1->real^N^N` THEN
     SIMP_TAC[MATRIX_PATH_LINEPATH;MATRIX_PATHSTART_LINEPATH;MATRIX_PATHFINISH_LINEPATH] THEN
     SIMP_TAC[MATRIX_LINEPATH_REFL;MATRIX_PATH_IMAGE_CONST] THEN
     SIMP_TAC[SING_SUBSET;GSYM MLG_GROUP;GROUP_ID];ALL_TAC] THEN
    CONJ_TAC THENL
    [SIMP_TAC[MATRIX_PATH_COMPONENT_SET;IN_ELIM_THM] THEN
     REPEAT STRIP_TAC THEN
     EXISTS_TAC `matrix_inv o (g:real^1^1->real^N^N)` THEN
     ASM_SIMP_TAC[MATRIX_PATHSTART_COMPOSE;MATRIX_PATHFINISH_COMPOSE;MATRIX_INV_I;MATRIX_PATH_IMAGE_MATRIX_INV] THEN
     MATCH_MP_TAC MATRIX_PATH_CONTINUOUS_IMAGE THEN
     ASM_SIMP_TAC[] THEN
     MATCH_MP_TAC MATRIX_CONTINUOUS_ON_SUBSET THEN
     EXISTS_TAC `IMAGE Re_matrix (mlg_set (G:(N)mlg))` THEN
     ASM_SIMP_TAC[MATRIX_INV_CONTINUOUS_ON_MLG_SET];ALL_TAC] THEN
    SIMP_TAC[MATRIX_PATH_COMPONENT_SET;IN_ELIM_THM] THEN
    SIMP_TAC[matrix_path;matrix_pathstart;matrix_pathfinish;MATRIX_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `(\x. ((g:real^1^1->real^N^N) x) ** ((g':real^1^1->real^N^N) x))` THEN
    ASM_SIMP_TAC[MATRIX_MUL_LID;MATRIX_MUL_LZERO;MATRIX_CONTINUOUS_MUL;MATRIX_PATH_IMAGE_MATRIX_MUL]);;

let DISCONNECTED_GENERAL_LINEAR_GROUP = prove
    (`!g:real^N^N. ~(matrix_path_connected (group_carrier(general_linear_group g)))`,
    SIMP_TAC[matrix_path_connected;GENERAL_LINEAR_GROUP;IN_ELIM_THM] THEN
    SIMP_TAC[NOT_FORALL_THM;TAUT `~(P ==> Q) <=> P /\ ~Q`;NOT_EXISTS_THM] THEN
    MAP_EVERY EXISTS_TAC [`mat 1 :real^N^N`;`(lambda i j. if i = j then if i = 1 then --(&1) else &1 else &0):real^N^N`] THEN
    SIMP_TAC[INVERTIBLE_I] THEN CONJ_TAC THENL
    [SIMP_TAC[INVERTIBLE_LEFT_INVERSE] THEN
     EXISTS_TAC `(lambda i j. if i = j then if i = 1 then --(&1) else &1 else &0):real^N^N` THEN
     SIMP_TAC[CART_EQ;LAMBDA_BETA;MAT_COMPONENT;matrix_mul] THEN
     REPEAT STRIP_TAC THEN
     ASM_CASES_TAC `i = i':num` THEN ASM_SIMP_TAC[] THENL
     [COND_CASES_TAC THEN
      ASM_SIMP_TAC[COND_LMUL_0;COND_RMUL_0;GSYM SUM_RESTRICT_SET;IN_NUMSEG;DIMINDEX_GE_1;REAL_MUL_RID;SET_RULE `1 <= k /\ k <= N /\ i = k <=> 1 <= i /\ i <= N /\ i = k`;GSYM CONJ_ASSOC;LE_REFL] THEN
      SIMP_TAC[SING_GSPEC;SUM_SING] THEN POP_ASSUM MP_TAC THEN
      REAL_ARITH_TAC;ALL_TAC] THEN
     MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
     ASM_ARITH_TAC;ALL_TAC] THEN
    SIMP_TAC[matrix_path_image;SUBSET;IN_ELIM_THM;DE_MORGAN_THM;NOT_FORALL_THM;TAUT `~(P ==> Q) <=> P /\ ~Q`] THEN
    GEN_TAC THEN
    ASM_CASES_TAC ` matrix_path (g:real^1^1->real^N^N) /\ (matrix_pathstart g = mat 1) /\ (matrix_pathfinish g = (lambda i j. if i = j then if i = 1 then --(&1) else &1 else &0):real^N^N)` THENL
    [ASM_SIMP_TAC[] THEN
     MP_TAC (ISPECL [`(\A:real^N^N. lift_lift (det A))`;`g:real^1^1->real^N^N`] MATRIX_PATH_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
    [ASM_SIMP_TAC[] THEN
     MATCH_MP_TAC MATRIX_CONTINUOUS_ON_SUBSET THEN
     EXISTS_TAC `(:real^N^N)` THEN
     SIMP_TAC[SUBSET_UNIV;DET_CONTINUOUS_ON];ALL_TAC] THEN
     SIMP_TAC[matrix_path;MATRIX_CONTINUOUS_ON_R11_EQ_REAL] THEN
     SIMP_TAC[o_DEF;LIFT_DROP2;IN_MATRIX_INTERVAL_1;DROP2_MAT;GSYM IN_REAL_INTERVAL] THEN
     SUBGOAL_THEN `{drop_drop x | drop_drop x IN real_interval [&0,&1]} = real_interval [&0,&1]` SUBST1_TAC THENL
     [SIMP_TAC[IN_REAL_INTERVAL;EXTENSION;IN_ELIM_THM] THEN
      MESON_TAC[LIFT2_DROP];ALL_TAC] THEN
     STRIP_TAC THEN
     MP_TAC(ISPECL [`(\x. det ((g:real^1^1->real^N^N) (lift_lift x)))`;`&0`;`&1`;`&0`] REAL_IVT) THEN
     ANTS_TAC THENL
    [ASM_SIMP_TAC[LIFT2_NUM;REAL_ARITH `&0 <= &1`] THEN
    SUBGOAL_THEN `det ((g:real^1^1->real^N^N) (mat 0)) = &1` SUBST1_TAC THENL
    [SIMP_TAC[GSYM DET_I] THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[GSYM matrix_pathstart];ALL_TAC] THEN
    SUBGOAL_THEN `det ((g:real^1^1->real^N^N) (mat 1)) = --(&1)` SUBST1_TAC THENL
    [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    SIMP_TAC[matrix_pathfinish] THEN
    SIMP_TAC[DET_LOWERTRIANGULAR;LAMBDA_BETA;LT_IMP_NE] THEN
    SIMP_TAC[PRODUCT_CLAUSES_LEFT;DIMINDEX_GE_1;REAL_MUL_LNEG;REAL_NEG_EQ;REAL_MUL_LID;REAL_NEG_NEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_EQ_1_NUMSEG THEN
    ARITH_TAC;ALL_TAC] THEN
    REAL_ARITH_TAC;ALL_TAC] THEN
    SIMP_TAC[IN_IMAGE;GSYM DET_EQ_0] THEN STRIP_TAC THEN
    EXISTS_TAC `(g:real^1^1->real^N^N) (lift_lift x)` THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `(lift_lift x)` THEN
    ASM_SIMP_TAC[LIFT2_IN_MATRIX_INTERVAL;DROP2_MAT];ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    SIMP_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let DISCONNECTED_ORTHOGONAL_GROUP = prove
    (`!g:real^N^N. ~(matrix_path_connected (group_carrier(orthogonal_group g)))`,
    SIMP_TAC[matrix_path_connected;ORTHOGONAL_GROUP;IN_ELIM_THM] THEN
    SIMP_TAC[NOT_FORALL_THM;TAUT `~(P ==> Q) <=> P /\ ~Q`;NOT_EXISTS_THM] THEN
    MAP_EVERY EXISTS_TAC [`mat 1 :real^N^N`;`(lambda i j. if i = j then if i = 1 then --(&1) else &1 else &0):real^N^N`] THEN
    SIMP_TAC[ORTHOGONAL_MATRIX_ID] THEN CONJ_TAC THENL
    [SIMP_TAC[orthogonal_matrix] THEN
     SIMP_TAC[CART_EQ;LAMBDA_BETA;MAT_COMPONENT;matrix_mul;TRANSP_COMPONENT] THEN
     CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
     ASM_CASES_TAC `i = i':num` THEN ASM_SIMP_TAC[] THENL
     [COND_CASES_TAC THEN
      ASM_SIMP_TAC[COND_LMUL_0;COND_RMUL_0;GSYM SUM_RESTRICT_SET;IN_NUMSEG;DIMINDEX_GE_1;REAL_MUL_RID;SET_RULE `1 <= k /\ k <= N /\ k = i <=> 1 <= i /\ i <= N /\ k = i`;GSYM CONJ_ASSOC;LE_REFL] THEN
      SIMP_TAC[SING_GSPEC;SUM_SING] THEN POP_ASSUM MP_TAC THEN
      REAL_ARITH_TAC;ALL_TAC] THEN
     MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
     ASM_ARITH_TAC;ALL_TAC] THEN
     REPEAT STRIP_TAC THEN
     ASM_CASES_TAC `i = i':num` THEN ASM_SIMP_TAC[] THENL
     [ASM_SIMP_TAC[SUM_CLAUSES_LEFT;DIMINDEX_GE_1;REAL_MUL_LNEG;REAL_MUL_RNEG;REAL_MUL_LID;REAL_NEG_NEG;COND_LMUL_0;COND_RMUL_0] THEN
      SIMP_TAC[COND_RAND] THEN SIMP_TAC[COND_RATOR] THEN
      COND_CASES_TAC THENL 
      [SIMP_TAC[REAL_ARITH `&1 + c = &1 <=> c = &0`] THEN
      MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
      POP_ASSUM MP_TAC THEN ARITH_TAC;ALL_TAC] THEN
      SUBGOAL_THEN `sum (1 + 1..dimindex (:N))
    (\k. if k = 1 then &0 else if i' = k then &1 * &1 else &0) = 
    sum (1 + 1..dimindex (:N))
    (\k. if k = i' then &1 * &1 else &0)` SUBST1_TAC THENL
      [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ARITH_TAC;ALL_TAC] THEN
      SIMP_TAC[REAL_ADD_LID;SUM_DELTA;IN_NUMSEG;GSYM (num_CONV `2`)] THEN
      ASM_ARITH_TAC;ALL_TAC] THEN
     MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
     ASM_ARITH_TAC;ALL_TAC] THEN
    SIMP_TAC[matrix_path_image;SUBSET;IN_ELIM_THM;DE_MORGAN_THM;NOT_FORALL_THM;TAUT `~(P ==> Q) <=> P /\ ~Q`] THEN
    GEN_TAC THEN
    ASM_CASES_TAC ` matrix_path (g:real^1^1->real^N^N) /\ (matrix_pathstart g = mat 1) /\ (matrix_pathfinish g = (lambda i j. if i = j then if i = 1 then --(&1) else &1 else &0):real^N^N)` THENL
    [ASM_SIMP_TAC[] THEN
     MP_TAC (ISPECL [`(\A:real^N^N. lift_lift (det A))`;`g:real^1^1->real^N^N`] MATRIX_PATH_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
    [ASM_SIMP_TAC[] THEN
     MATCH_MP_TAC MATRIX_CONTINUOUS_ON_SUBSET THEN
     EXISTS_TAC `(:real^N^N)` THEN
     SIMP_TAC[SUBSET_UNIV;DET_CONTINUOUS_ON];ALL_TAC] THEN
     SIMP_TAC[matrix_path;MATRIX_CONTINUOUS_ON_R11_EQ_REAL] THEN
     SIMP_TAC[o_DEF;LIFT_DROP2;IN_MATRIX_INTERVAL_1;DROP2_MAT;GSYM IN_REAL_INTERVAL] THEN
     SUBGOAL_THEN `{drop_drop x | drop_drop x IN real_interval [&0,&1]} = real_interval [&0,&1]` SUBST1_TAC THENL
     [SIMP_TAC[IN_REAL_INTERVAL;EXTENSION;IN_ELIM_THM] THEN
      MESON_TAC[LIFT2_DROP];ALL_TAC] THEN
     STRIP_TAC THEN
     SIMP_TAC[ORTHOGONAL_MATRIX_EQ;DE_MORGAN_THM] THEN
     MP_TAC(ISPECL [`(\x. det ((g:real^1^1->real^N^N) (lift_lift x)))`;`&0`;`&1`;`&0`] REAL_IVT) THEN
     ANTS_TAC THENL
    [ASM_SIMP_TAC[LIFT2_NUM;REAL_ARITH `&0 <= &1`] THEN
    SUBGOAL_THEN `det ((g:real^1^1->real^N^N) (mat 0)) = &1` SUBST1_TAC THENL
    [SIMP_TAC[GSYM DET_I] THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[GSYM matrix_pathstart];ALL_TAC] THEN
    SUBGOAL_THEN `det ((g:real^1^1->real^N^N) (mat 1)) = --(&1)` SUBST1_TAC THENL
    [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    SIMP_TAC[matrix_pathfinish] THEN
    SIMP_TAC[DET_LOWERTRIANGULAR;LAMBDA_BETA;LT_IMP_NE] THEN
    SIMP_TAC[PRODUCT_CLAUSES_LEFT;DIMINDEX_GE_1;REAL_MUL_LNEG;REAL_NEG_EQ;REAL_MUL_LID;REAL_NEG_NEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_EQ_1_NUMSEG THEN
    ARITH_TAC;ALL_TAC] THEN
    REAL_ARITH_TAC;ALL_TAC] THEN
    SIMP_TAC[IN_IMAGE;GSYM DET_EQ_0] THEN STRIP_TAC THEN
    EXISTS_TAC `(g:real^1^1->real^N^N) (lift_lift x)` THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `(lift_lift x)` THEN
    ASM_SIMP_TAC[LIFT2_IN_MATRIX_INTERVAL;DROP2_MAT];ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    SIMP_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;
    
(*
let CONNECTED_SPECIAL_LINEAR_GROUP = prove
    (`!g:real^N^N. matrix_path_connected (group_carrier(special_linear_group g))`,
    GEN_TAC THEN
    SIMP_TAC[matrix_path_connected;SPECIAL_LINEAR_GROUP;IN_ELIM_THM] THEN
    SIMP_TAC[matrix_path_image;SUBSET;IN_ELIM_THM;INVERTIBLE_DET_NZ;REAL_ARITH `(~(x = &0) /\ x = &1) <=> x = &1`] THEN
    SIMP_TAC[det;CART_EQ;LAMBDA_BETA] THEN
    MP_TAC (ISPEC `(:N)` DIMINDEX_GE_1) THEN
    ABBREV_TAC `n = dimindex(:N)` THEN
    SPEC_TAC(`n:num`,`n:num`) THEN
    INDUCT_TAC THENL [ARITH_TAC;ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN INTRO_TAC "indtN" THEN
    ASM_CASES_TAC `n' = 0` THENL
    [ASM_SIMP_TAC[GSYM (num_CONV `1`);PRODUCT_SING;NUMSEG_SING;PERMUTES_SING;SIGN_I;SING_GSPEC;SUM_SING;I_THM;LE_REFL;REAL_MUL_LID;FORALL_1] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `(\x:real^1^1. mat 1 :real^N^N)` THEN
    SIMP_TAC[matrix_path;MATRIX_CONTINUOUS_ON_CONST;matrix_pathstart;matrix_pathfinish;MAT_COMPONENT;ARITH_EQ;DIMINDEX_GE_1;LE_REFL;IN_IMAGE;IN_MATRIX_INTERVAL_1;GSYM LEFT_FORALL_IMP_THM];ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    REMOVE_THEN "indtN" MP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> 1 <= n`]
    SIMP_TAC[PRODUCT_CLAUSES_NUMSEG] THEN
    ASM_SIMP_TAC[] THEN
     MP_TAC (ISPECL [`(\A:real^N^N. lift_lift (det A))`;`g:real^1^1->real^N^N`] MATRIX_PATH_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
    [ASM_SIMP_TAC[] THEN
     MATCH_MP_TAC MATRIX_CONTINUOUS_ON_SUBSET THEN
     EXISTS_TAC `(:real^N^N)` THEN
     SIMP_TAC[SUBSET_UNIV;DET_CONTINUOUS_ON];ALL_TAC] THEN
     SIMP_TAC[matrix_path;MATRIX_CONTINUOUS_ON_R11_EQ_REAL] THEN
     SIMP_TAC[o_DEF;LIFT_DROP2;IN_MATRIX_INTERVAL_1;DROP2_MAT;GSYM IN_REAL_INTERVAL] THEN
     SUBGOAL_THEN `{drop_drop x | drop_drop x IN real_interval [&0,&1]} = real_interval [&0,&1]` SUBST1_TAC THENL
     [SIMP_TAC[IN_REAL_INTERVAL;EXTENSION;IN_ELIM_THM] THEN
      MESON_TAC[LIFT2_DROP];ALL_TAC] THEN
     STRIP_TAC THEN
     SIMP_TAC[ORTHOGONAL_MATRIX_EQ;DE_MORGAN_THM] THEN
     MP_TAC(ISPECL [`(\x. det ((g:real^1^1->real^N^N) (lift_lift x)))`;`&0`;`&1`;`&0`] REAL_IVT) THEN
     ANTS_TAC THENL
    [ASM_SIMP_TAC[LIFT2_NUM;REAL_ARITH `&0 <= &1`] THEN
    SUBGOAL_THEN `det ((g:real^1^1->real^N^N) (mat 0)) = &1` SUBST1_TAC THENL
    [SIMP_TAC[GSYM DET_I] THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[GSYM matrix_pathstart];ALL_TAC] THEN
    SUBGOAL_THEN `det ((g:real^1^1->real^N^N) (mat 1)) = --(&1)` SUBST1_TAC THENL
    [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    SIMP_TAC[matrix_pathfinish] THEN
    SIMP_TAC[DET_LOWERTRIANGULAR;LAMBDA_BETA;LT_IMP_NE] THEN
    SIMP_TAC[PRODUCT_CLAUSES_LEFT;DIMINDEX_GE_1;REAL_MUL_LNEG;REAL_NEG_EQ;REAL_MUL_LID;REAL_NEG_NEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_EQ_1_NUMSEG THEN
    ARITH_TAC;ALL_TAC] THEN
    REAL_ARITH_TAC;ALL_TAC] THEN
    SIMP_TAC[IN_IMAGE;GSYM DET_EQ_0] THEN STRIP_TAC THEN
    EXISTS_TAC `(g:real^1^1->real^N^N) (lift_lift x)` THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `(lift_lift x)` THEN
    ASM_SIMP_TAC[LIFT2_IN_MATRIX_INTERVAL;DROP2_MAT] THEN
    POP_ASSUM MP_TAC THEN
    SIMP_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;
*)

(* ------------------------------------------------------------------------- *)
(* lie algebra                                                               *)
(* ------------------------------------------------------------------------- *)
    
let lie_algebra_tybij =
  let eth = prove
   (`?s:A->bool f:A->A->A g:A->A->A h:K->A->A e:A. 
        (!x y. x IN s /\ y IN s ==> 
            (!k. k IN s ==> f x (g k y) = g (f x k) (f x y) /\
                            f (g x k) y = g (f x y) (f k y)) /\
            (!c. f x (h c y) = h c (f x y) /\ f (h c x) y = h c (f x y))) /\ 
        (!x y.  x IN s /\ y IN s ==> g (f x y) (f y x) = e) /\
        (!x y z. x IN s /\ y IN s /\ z IN s ==> g (g (f x (f y z)) (f y (f z x))) (f z (f x y)) = e)`,
  MAP_EVERY EXISTS_TAC
     [`{ARB:A}`;`(\x y. ARB):A->A->A`;`(\x y. ARB):A->A->A`;`(\c y. ARB):K->A->A`;`ARB:A`] THEN REWRITE_TAC[IN_SING]) in
  new_type_definition "lie_algebra" ("lie_algebra","lie_algebra_op")
   (GEN_REWRITE_RULE DEPTH_CONV [EXISTS_UNPAIR_THM] eth);;

let lie_alg_set = new_definition
 `(lie_alg_set:(A,K)lie_algebra->A->bool) = \g. FST(lie_algebra_op g)`;;
 
let lie_bracket = new_definition
 `(lie_bracket:(A,K)lie_algebra->A->A->A) = \g. FST(SND(lie_algebra_op g))`;;

let lie_alg_add = new_definition
 `(lie_alg_add:(A,K)lie_algebra->A->A->A) = \g. FST(SND(SND(lie_algebra_op g)))`;;

let lie_alg_mul = new_definition
 `(lie_alg_mul:(A,K)lie_algebra->K->A->A) = \g. FST(SND(SND(SND(lie_algebra_op g))))`;;
 
let lie_alg_zero = new_definition
 `(lie_alg_zero:(A,K)lie_algebra->A) = \g. SND(SND(SND(SND(lie_algebra_op g))))`;;

let ([LIE_BRACKET_BILINEAR;LIE_BRACKET_BILINEAR_RADD;LIE_BRACKET_BILINEAR_RCMUL;LIE_BRACKET_BILINEAR_LADD;LIE_BRACKET_BILINEAR_LCMUL;LIE_BRACKET_SSM_IN;LIE_BRACKET_JACOBI_I_IN] as
     LIE_ALGEBRA_PROPERTIES) = (CONJUNCTS o prove)
 (`(!g:(A,K)lie_algebra x y k c. 
        x IN lie_alg_set g /\ y IN lie_alg_set g ==>
        (!k. k IN lie_alg_set g ==> 
            lie_bracket g x (lie_alg_add g k y) = lie_alg_add g (lie_bracket g x k) (lie_bracket g x y) /\
            lie_bracket g (lie_alg_add g x k) y = lie_alg_add g (lie_bracket g x y) (lie_bracket g k y)) /\
        (!c. lie_bracket g x (lie_alg_mul g c y) = lie_alg_mul g c (lie_bracket g x y) /\
             lie_bracket g (lie_alg_mul g c x) y = lie_alg_mul g c (lie_bracket g x y))) /\
    (!g:(A,K)lie_algebra x y k. 
        x IN lie_alg_set g /\ y IN lie_alg_set g /\ k IN lie_alg_set g ==> 
            lie_bracket g x (lie_alg_add g k y) = lie_alg_add g (lie_bracket g x k) (lie_bracket g x y)) /\
    (!g:(A,K)lie_algebra x y c. 
        x IN lie_alg_set g /\ y IN lie_alg_set g ==> 
            lie_bracket g x (lie_alg_mul g c y) = lie_alg_mul g c (lie_bracket g x y)) /\
    (!g:(A,K)lie_algebra x y k. 
        x IN lie_alg_set g /\ y IN lie_alg_set g /\ k IN lie_alg_set g ==> 
            lie_bracket g (lie_alg_add g x k) y = lie_alg_add g (lie_bracket g x y) (lie_bracket g k y)) /\
    (!g:(A,K)lie_algebra x y c. 
        x IN lie_alg_set g /\ y IN lie_alg_set g ==> 
            lie_bracket g (lie_alg_mul g c x) y = lie_alg_mul g c (lie_bracket g x y)) /\
    (!g:(A,K)lie_algebra x y.
          x IN lie_alg_set g /\ y IN lie_alg_set g
          ==> lie_alg_add g (lie_bracket g x y) (lie_bracket g y x) = lie_alg_zero g) /\
    (!g:(A,K)lie_algebra x y z.
          x IN lie_alg_set g /\ y IN lie_alg_set g /\ z IN lie_alg_set g
          ==> lie_alg_add g 
                (lie_alg_add g (lie_bracket g x (lie_bracket g y z)) (lie_bracket g y (lie_bracket g z x)))
                (lie_bracket g z (lie_bracket g x y)) = lie_alg_zero g)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  MP_TAC(SPEC `g:(A,K)lie_algebra` (MATCH_MP(MESON[]
   `(!a. mk(dest a) = a) /\ (!r. P r <=> dest(mk r) = r)
    ==> !a. P(dest a)`) lie_algebra_tybij)) THEN
  REWRITE_TAC[lie_alg_set;lie_bracket;lie_alg_add;lie_alg_mul;lie_alg_zero] THEN
  SIMP_TAC[]);; 

let LIE_ALGEBRAS_EQ = prove
 (`!G H:(A,K)lie_algebra.
        G = H <=>
        lie_alg_set G = lie_alg_set H /\
        lie_bracket G = lie_bracket H /\
        lie_alg_add G = lie_alg_add H /\
        lie_alg_mul G = lie_alg_mul H /\
        lie_alg_zero G = lie_alg_zero H`,
  REWRITE_TAC[GSYM PAIR_EQ] THEN
  REWRITE_TAC[lie_alg_set;lie_bracket;lie_alg_add;lie_alg_mul;lie_alg_zero] THEN
  MESON_TAC[CONJUNCT1 lie_algebra_tybij]);; 
  
(* ------------------------------------------------------------------------- *)
(* lie bracket in matrix space                                               *)
(* ------------------------------------------------------------------------- *)

make_overloadable "matrix_lie_bracket" `:A^N^N->A^N^N->A^N^N`;;

overload_interface ("matrix_lie_bracket", `real_matrix_lie_bracket:real^N^N->real^N^N->real^N^N`);;

overload_interface ("matrix_lie_bracket", `complex_matrix_lie_bracket:complex^N^N->complex^N^N->complex^N^N`);;

let real_matrix_lie_bracket = new_definition
    `real_matrix_lie_bracket (A:real^N^N) (B:real^N^N) = A ** B - B ** A`;;
    
let complex_matrix_lie_bracket = new_definition
    `complex_matrix_lie_bracket (A:complex^N^N) (B:complex^N^N) = A ** B - B ** A`;;

let matrix_lie_bracket = prove
    (`(!A B:real^N^N. real_matrix_lie_bracket A B = A ** B - B ** A) /\
      (!A B:complex^N^N. complex_matrix_lie_bracket A B = A ** B - B ** A)`,
    SIMP_TAC[real_matrix_lie_bracket;complex_matrix_lie_bracket]);;

let MATRIX_LIE_BRACKET_BILINEAR = prove
    (`bimlinear (matrix_lie_bracket:real^N^N->real^N^N->real^N^N)`,
    SIMP_TAC [bimlinear; mlinear;matrix_lie_bracket] THEN
    REPEAT STRIP_TAC THEN CMATRIX_ARITH_TAC);;
    
let MATRIX_LIE_BRACKET_BILINEAR_ALT = prove
    (`(!x y k:real^N^N c.
        matrix_lie_bracket x (k + y) = 
        matrix_lie_bracket x k + matrix_lie_bracket x y /\
        matrix_lie_bracket (x + k) y =
        matrix_lie_bracket x y + matrix_lie_bracket k y /\
        matrix_lie_bracket x (c %% y) = c %% matrix_lie_bracket x y /\
        matrix_lie_bracket (c %% x) y = c %% matrix_lie_bracket x y) /\
        (!x y k:complex^N^N c.
        matrix_lie_bracket x (k + y) = 
        matrix_lie_bracket x k + matrix_lie_bracket x y /\
        matrix_lie_bracket (x + k) y =
        matrix_lie_bracket x y + matrix_lie_bracket k y /\
        matrix_lie_bracket x (c %%% y) = c %%% matrix_lie_bracket x y /\
        matrix_lie_bracket (c %%% x) y = c %%% matrix_lie_bracket x y)`,
    SIMP_TAC [matrix_lie_bracket] THEN
    REPEAT STRIP_TAC THEN CMATRIX_ARITH_TAC);;
    
let MATRIX_LIE_BRACKET_SSM = prove
    (`(!A B:real^N^N. matrix_lie_bracket A B = --(matrix_lie_bracket B A)) /\ (!A B:complex^N^N. matrix_lie_bracket A B = --(matrix_lie_bracket B A))`,
    SIMP_TAC [matrix_lie_bracket] THEN CMATRIX_ARITH_TAC);;
    
let MATRIX_LIE_BRACKET_SSM_ALT = prove
    (`(!A B:real^N^N. matrix_lie_bracket A B + matrix_lie_bracket B A = mat 0) /\ (!A B:complex^N^N. matrix_lie_bracket A B + matrix_lie_bracket B A = cmat 0)`,
    CONJ_TAC THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [MATRIX_LIE_BRACKET_SSM] THEN CMATRIX_ARITH_TAC);;
    
let MATRIX_LIE_BRACKET_REFL = prove
    (`(!A:real^N^N. matrix_lie_bracket A A = mat 0) /\
     (!A:complex^N^N. matrix_lie_bracket A A = cmat 0)`,
    SIMP_TAC [matrix_lie_bracket;MATRIX_SUB_REFL;CMATRIX_SUB_REFL]);;
    
let MATRIX_LIE_BRACKET_JACOBI_I = prove
    (`(!A B C:real^N^N. matrix_lie_bracket A (matrix_lie_bracket B C) + matrix_lie_bracket B (matrix_lie_bracket C A) + matrix_lie_bracket C (matrix_lie_bracket A B) = mat 0) /\
    (!A B C:complex^N^N. matrix_lie_bracket A (matrix_lie_bracket B C) + matrix_lie_bracket B (matrix_lie_bracket C A) + matrix_lie_bracket C (matrix_lie_bracket A B) = cmat 0)`,
    SIMP_TAC [matrix_lie_bracket] THEN SIMP_TAC[MATRIX_SUB_LDISTRIB;MATRIX_SUB_RDISTRIB;GSYM MATRIX_MUL_ASSOC] THEN
    SIMP_TAC[CMATRIX_SUB_LDISTRIB;CMATRIX_SUB_RDISTRIB;GSYM CMATRIX_MUL_ASSOC] THEN
    SIMP_TAC[CMATRIX_ARITH `A1 - A2 - (B1 - C1) + B1 - B2 - (C2 - A2) + C2 - C1 - (A1 - B2) :real^N^N = mat 0`;CMATRIX_ARITH `A1 - A2 - (B1 - C1) + B1 - B2 - (C2 - A2) + C2 - C1 - (A1 - B2) :complex^N^N = cmat 0`]);;

(* ------------------------------------------------------------------------- *)
(* related properties of matrix exponential function                         *)
(* ------------------------------------------------------------------------- *)

let INVERTIBLE_MATRIX_EXP = prove    
    (`!x t. invertible (matrix_exp (t %% x))`,
    REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
    MESON_TAC[MATRIX_EXP_INV_FUN;LIFT_DROP2]);;     
  
let MATRIX_POW_SIM = prove
    (`!A:real^N^N P:real^N^N n. invertible P ==>
    (((matrix_inv P) ** A ** P) matrix_pow n) = 
    (matrix_inv P) ** (A matrix_pow n) ** P`,
    GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    STRIP_TAC THEN SIMP_TAC [matrix_pow] THENL
    [ASM_SIMP_TAC[MATRIX_MUL_LID;MATRIX_INV] ;ALL_TAC] THEN
    ASM_SIMP_TAC[MESON [MATRIX_MUL_ASSOC] `((IP:real^N^N) ** (A:real^N^N) ** P) ** IP **
    (AP:real^N^N) ** (P:real^N^N) = IP ** A ** (P ** IP) **AP **P`] THEN
    ASM_SIMP_TAC[MATRIX_INV] THEN MESON_TAC[MATRIX_MUL_LID;MATRIX_MUL_ASSOC]);;

let MSUMMABLE_MATRIX_EXP = prove
    (`!A:real^N^N. msummable (from 0) (\n. &1 / &(FACT n) %% A matrix_pow n)` ,
    SIMP_TAC[GSYM MSUMS_INFSUM;MATRIX_EXP_CONVERGES;GSYM matrix_exp]);;

let MSUMMABLE_LMUL = prove
    (`!s x:num->real^N^M A:real^M^P. 
    msummable s x ==> msummable s (\n. A ** (x n))`,
    REWRITE_TAC[msummable] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `(A:real^M^P) ** (l:real^N^M)` THEN 
    ASM_SIMP_TAC[MSERIES_LMUL] );;
 
let MSUMMABLE_RMUL = prove
    (`!s x:num->real^N^M A:real^P^N. 
    msummable s x ==> msummable s (\n. (x n) ** A)`,
    REWRITE_TAC[msummable] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `(l:real^N^M) ** (A:real^P^N)` THEN 
    ASM_SIMP_TAC[MSERIES_RMUL] );;

let MATRIX_EXP_ID_EQ = prove
    (`!A:real^N^N P:real^N^N . invertible P ==>
    (((matrix_inv P )** matrix_exp A ** P) = 
    matrix_exp ((matrix_inv P) ** A ** P))`,
    REPEAT STRIP_TAC THEN SIMP_TAC[matrix_exp] THEN
    ASM_SIMP_TAC[MATRIX_POW_SIM] THEN 
    SIMP_TAC[MESON [MATRIX_MUL_LMUL;MATRIX_MUL_RMUL;MATRIX_MUL_ASSOC] `c %% (x ** y ** z) = x ** (c %% y) ** z`] THEN 
    SIMP_TAC[INFMSUM_RMUL;INFMSUM_LMUL;MSUMMABLE_MATRIX_EXP;
    MSUMMABLE_LMUL;MSUMMABLE_RMUL]);;
    
(*
let EIGENVALUES_IMP_CHARACTERISTIC_DET = prove
    (`!A:real^N^N i. ?c:num->real. i <= dimindex(:N) /\ (?v. ~(v = vec 0) /\ A ** v = (c i) % v) ==> det(A) = product (1..dimindex(:N)) (\i. c i)`,   
    GEN_TAC THEN SIMP_TAC[EIGENVALUES_CHARACTERISTIC] THEN    
    MP_TAC(ISPEC `A:real^N^N` MATRIX_DIAGONALIZABLE) THEN
    DISCH_THEN(X_CHOOSE_THEN `P:real^N^N` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `D:real^N^N` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `Q:real^N^N` MP_TAC) THEN
    SIMP_TAC[DET_MUL;DET_DIAGONAL] THEN REPEAT STRIP_TAC THEN
    MP_TAC (ISPEC `P:real^N^N` DET_ORTHOGONAL_MATRIX) THEN
    MP_TAC (ISPEC `Q:real^N^N` DET_ORTHOGONAL_MATRIX) THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `(\i. if det(P:real^N^N) * det(Q:real^N^N) = -- &1 /\ i = dimindex(:N) then -- ((D:real^N^N)$i$i) else D$i$i)` THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_LID;REAL_MUL_RID;REAL_MUL_LNEG;REAL_MUL_RNEG;REAL_ARITH `~(&1 = -- &1)`;ARITH_EQ;REAL_NEG_NEG] THEN
    ONCE_REWRITE_TAC[(MESON [DIMINDEX_GE_1;ARITH_RULE `1 <= N ==> N = (N - 1) + 1`] `dimindex(:N) = dimindex(:N) - 1 + 1`)] THEN
    SIMP_TAC[PRODUCT_ADD_SPLIT;DIMINDEX_GE_1;GSYM (ARITH_RULE `1 <= N ==> N = (N - 1) + 1`);PRODUCT_SING_NUMSEG;REAL_MUL_RNEG;REAL_NEG_EQ;REAL_NEG_NEG;REAL_EQ_MUL_RCANCEL] THEN
    DISJ1_TAC THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN ARITH_TAC);;
*)

let COND_LMUL = prove
 (`!b x1 x2 y. (if b then x1 else x2) * y = (if b then x1 * y else x2 * y)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;
  
let COND_RMUL = prove
 (`!b x1 x2 y. y * (if b then x1 else x2) = (if b then y * x1 else y * x2)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;
  
let COND_LMUL_0 = prove
 (`!b x y. (if b then x else &0) * y = (if b then x * y else &0)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[REAL_MUL_LZERO]);;
  
let COND_RMUL_0 = prove
 (`!b x y. y * (if b then x else &0) = (if b then y * x else &0)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[REAL_MUL_RZERO]);;    
    
(* ------------------------------------------------------------------------- *)
(* the lie algebra of matrix lie group                                       *)
(* ------------------------------------------------------------------------- *)

make_overloadable "is_lie_algebra_of_mlg" `:(N)mlg->(A^N^N,A)lie_algebra->bool`;;

overload_interface ("is_lie_algebra_of_mlg", `is_lie_algebra_of_mlg_r:(N)mlg->(real^N^N,real)lie_algebra->bool`);;

overload_interface ("is_lie_algebra_of_mlg", `is_lie_algebra_of_mlg_c:(N)mlg->(complex^N^N,complex)lie_algebra->bool`);;

let is_lie_algebra_of_mlg_r = new_definition
    `is_lie_algebra_of_mlg_r (G:(N)mlg) (g:(real^N^N,real)lie_algebra) <=>
    !X t:real. X IN lie_alg_set g ==> Cx_matrix(matrix_exp (t %% X)) IN (mlg_set G)`;;
    
let is_lie_algebra_of_mlg_c = new_definition
    `is_lie_algebra_of_mlg_c (G:(N)mlg) (g:(complex^N^N,complex)lie_algebra) <=>
    !X t:real. X IN lie_alg_set g ==> matrix_exp (Cx(t) %%% X) IN (mlg_set G)`;;
    
let is_lie_algebra_of_mlg = prove
    (`(!G g. is_lie_algebra_of_mlg_r G g <=>
    !X t:real. X IN lie_alg_set g ==> Cx_matrix(matrix_exp (t %% X)) IN (mlg_set G)) /\
    (!G g. is_lie_algebra_of_mlg_c G g <=>
    !X t:real. X IN lie_alg_set g ==> matrix_exp (Cx(t) %%% X) IN (mlg_set G))`,
    SIMP_TAC[is_lie_algebra_of_mlg_r;is_lie_algebra_of_mlg_c]);;
    
let IN_LIE_ALGEBRA_MATRIX_EXP_1 = prove
    (`!G g:(real^N^N,real)lie_algebra X. 
    is_lie_algebra_of_mlg G g /\ X IN lie_alg_set g ==> Cx_matrix(matrix_exp X) IN (mlg_set G)`,
    MESON_TAC[is_lie_algebra_of_mlg;MATRIX_CMUL_LID]);;
    
let CX_MATRIX_MUL_EQ_CX = prove
    (`!A B:real^N^M. Cx_matrix(A ** B) = Cx_matrix A ** Cx_matrix B`,
    SIMP_TAC[CMATRIX_EQ_ALT;CMATRIX_MUL;RE_MATRIX_CX_MATRIX;RE_MATRIX;IM_MATRIX;IM_MATRIX_CX_MATRIX] THEN
    SIMP_TAC[MATRIX_MUL_LZERO;MATRIX_MUL_RZERO;MATRIX_SUB_RZERO;MATRIX_ADD_RID]);;
    
let IN_LIE_ALGEBRA_MATRIX_EXP_ADD = prove
    (`!G g:(real^N^N,real)lie_algebra X Y. 
    is_lie_algebra_of_mlg G g /\ X IN lie_alg_set g /\ Y IN lie_alg_set g /\ X ** Y = Y ** X ==> Cx_matrix(matrix_exp (X + Y)) IN (mlg_set G)`,
    SIMP_TAC[MATRIX_EXP_ADD;CX_MATRIX_MUL_EQ_CX] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CMATRIX_MUL_IN_MLG_SET THEN
    ASM_MESON_TAC[IN_LIE_ALGEBRA_MATRIX_EXP_1]);;
    
let IN_IMAGE_CX_MATRIX_ALT_IMP = prove
    (`!s A:real^N^M. (Cx_matrix A IN s ==> A IN (IMAGE Re_matrix s))`,
    REPEAT STRIP_TAC THEN SIMP_TAC[IN_IMAGE] THEN
    EXISTS_TAC `Cx_matrix (A:real^N^M)` THEN
    ASM_SIMP_TAC[RE_MATRIX_CX_MATRIX]);;
    
let IN_IMAGE_RE_MATRIX_ALT_IMP = prove
    (`!s A:real^N^M. IMAGE (Cx_matrix o Re_matrix) s = s /\ A IN IMAGE Re_matrix s ==> Cx_matrix A IN s`,
    SIMP_TAC[IN_IMAGE;EXTENSION;o_DEF] THEN REPEAT STRIP_TAC THEN 
    ASM_MESON_TAC[]);;
    
let IN_IMAGE_RE_MATRIX_ALT_EQ = prove
    (`!s A:real^N^M. IMAGE (Cx_matrix o Re_matrix) s = s ==> (A IN IMAGE Re_matrix s <=> Cx_matrix A IN s)`,
    MESON_TAC[IN_IMAGE_RE_MATRIX_ALT_IMP;IN_IMAGE_CX_MATRIX_ALT_IMP]);;
    
let IN_LIE_ALGEBRA_MATRIX_EXP_SIMILAR = prove
    (`!G g:(real^N^N,real)lie_algebra X A. 
    is_lie_algebra_of_mlg G g /\ X IN lie_alg_set g /\ Cx_matrix A IN mlg_set G /\ IMAGE (Cx_matrix o Re_matrix) (mlg_set G) = mlg_set G ==> Cx_matrix(matrix_exp (matrix_inv A ** X ** A)) IN (mlg_set G)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `A IN IMAGE Re_matrix (mlg_set (G:(N)mlg))` ASSUME_TAC THENL
    [ASM_SIMP_TAC[IN_IMAGE_CX_MATRIX_ALT_IMP];ALL_TAC] THEN
    SUBGOAL_THEN `invertible (A:real^N^N)` ASSUME_TAC THENL
    [MP_TAC (SPEC `G:(N)mlg` (CONJUNCT2 MLG_SUBGROUP_OF_GLG)) THEN
     ASM_SIMP_TAC[subgroup_of;GENERAL_LINEAR_GROUP;SUBSET;IN_ELIM_THM];ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM MATRIX_EXP_ID_EQ;CX_MATRIX_MUL_EQ_CX] THEN
    MATCH_MP_TAC CMATRIX_MUL_IN_MLG_SET THEN
    CONJ_TAC THENL 
    [MATCH_MP_TAC IN_IMAGE_RE_MATRIX_ALT_IMP THEN
     ASM_SIMP_TAC[MATRIX_INV_IN_MLG_SET];ALL_TAC] THEN
    MATCH_MP_TAC CMATRIX_MUL_IN_MLG_SET THEN
    ASM_MESON_TAC[IN_LIE_ALGEBRA_MATRIX_EXP_1]);;
    
(* ------------------------------------------------------------------------- *)
(* gl(n) the lie algebra of general linear group                             *)
(* ------------------------------------------------------------------------- *)
 
let lie_algebra_of_glg = new_definition
 `lie_algebra_of_glg (group_mlg(general_linear_group (a:real^N^N))) = lie_algebra ((:real^N^N),matrix_lie_bracket,matrix_add,(%%):real->real^N^N->real^N^N,(mat 0 :real^N^N))`;;

let LIE_ALGEBRA_OF_GLG = prove
    (`(!a:real^N^N. lie_alg_set (lie_algebra_of_glg (group_mlg(general_linear_group a))) = (:real^N^N)) /\
    (!a:real^N^N. lie_bracket (lie_algebra_of_glg (group_mlg (general_linear_group a))) = matrix_lie_bracket) /\
    (!a:real^N^N. lie_alg_add (lie_algebra_of_glg (group_mlg (general_linear_group a))) = matrix_add) /\
    (!a:real^N^N. lie_alg_mul (lie_algebra_of_glg (group_mlg (general_linear_group a))) = (%%)) /\
    (!a:real^N^N. lie_alg_zero (lie_algebra_of_glg (group_mlg (general_linear_group a))) = mat 0)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN 
    MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl lie_algebra_of_glg)))))
   (CONJUNCT2 lie_algebra_tybij)))) THEN
    REWRITE_TAC[GSYM lie_algebra_of_glg] THEN 
    SIMP_TAC[IN_UNIV;MATRIX_LIE_BRACKET_BILINEAR_ALT;MATRIX_LIE_BRACKET_SSM_ALT;MATRIX_LIE_BRACKET_JACOBI_I;GSYM MATRIX_ADD_ASSOC] THEN
    SIMP_TAC[lie_alg_set; lie_bracket; lie_alg_add; lie_alg_mul;lie_alg_zero]);;

(* ------------------------------------------------------------------------- *)
(* sl(n) the lie algebra of special linear group                             *)
(* ------------------------------------------------------------------------- *)

let lie_algebra_of_slg = new_definition
 `lie_algebra_of_slg (group_mlg(special_linear_group (a:real^N^N))) = lie_algebra ({ A:real^N^N | trace A = &0},matrix_lie_bracket,matrix_add,(%%):real->real^N^N->real^N^N,(mat 0 :real^N^N))`;; 
 
let LIE_ALGEBRA_OF_SLG = prove
    (`(!a:real^N^N. lie_alg_set (lie_algebra_of_slg (group_mlg(special_linear_group a))) = {A:real^N^N | trace A = &0}) /\
    (!a:real^N^N. lie_bracket (lie_algebra_of_slg (group_mlg (special_linear_group a))) = matrix_lie_bracket) /\
    (!a:real^N^N. lie_alg_add (lie_algebra_of_slg (group_mlg (special_linear_group a))) = matrix_add) /\
    (!a:real^N^N. lie_alg_mul (lie_algebra_of_slg (group_mlg (special_linear_group a))) = (%%)) /\
    (!a:real^N^N. lie_alg_zero (lie_algebra_of_slg (group_mlg (special_linear_group a))) = mat 0)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN 
    MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl lie_algebra_of_slg)))))
   (CONJUNCT2 lie_algebra_tybij)))) THEN
    REWRITE_TAC[GSYM lie_algebra_of_slg] THEN 
    SIMP_TAC[MATRIX_LIE_BRACKET_BILINEAR_ALT;MATRIX_LIE_BRACKET_SSM_ALT;MATRIX_LIE_BRACKET_JACOBI_I;GSYM MATRIX_ADD_ASSOC] THEN
    SIMP_TAC[lie_alg_set; lie_bracket; lie_alg_add; lie_alg_mul;lie_alg_zero]);;

(* ------------------------------------------------------------------------- *)
(* o(n) the lie algebra of orthogonal group                             *)
(* ------------------------------------------------------------------------- *)

let lie_algebra_of_og = new_definition
 `lie_algebra_of_og (group_mlg(orthogonal_group (a:real^N^N))) = lie_algebra ({ A:real^N^N | transp A = --A},matrix_lie_bracket,matrix_add,(%%):real->real^N^N->real^N^N,(mat 0 :real^N^N))`;; 
 
let LIE_ALGEBRA_OF_OG = prove
    (`(!a:real^N^N. lie_alg_set (lie_algebra_of_og (group_mlg(orthogonal_group a))) = { A:real^N^N | transp A = --A}) /\
    (!a:real^N^N. lie_bracket (lie_algebra_of_og (group_mlg (orthogonal_group a))) = matrix_lie_bracket) /\
    (!a:real^N^N. lie_alg_add (lie_algebra_of_og (group_mlg (orthogonal_group a))) = matrix_add) /\
    (!a:real^N^N. lie_alg_mul (lie_algebra_of_og (group_mlg (orthogonal_group a))) = (%%)) /\
    (!a:real^N^N. lie_alg_zero (lie_algebra_of_og (group_mlg (orthogonal_group a))) = mat 0)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN 
    MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl lie_algebra_of_og)))))
   (CONJUNCT2 lie_algebra_tybij)))) THEN
    REWRITE_TAC[GSYM lie_algebra_of_og] THEN 
    SIMP_TAC[MATRIX_LIE_BRACKET_BILINEAR_ALT;MATRIX_LIE_BRACKET_SSM_ALT;MATRIX_LIE_BRACKET_JACOBI_I;GSYM MATRIX_ADD_ASSOC] THEN
    SIMP_TAC[lie_alg_set; lie_bracket; lie_alg_add; lie_alg_mul;lie_alg_zero]);;

(* ------------------------------------------------------------------------- *)
(* so(n) the lie algebra of special orthogonal group (rotation group) *)
(* ------------------------------------------------------------------------- *)

let lie_algebra_of_sog = new_definition
 `lie_algebra_of_sog (group_mlg(rotation_group (a:real^N^N))) = lie_algebra ({ A:real^N^N | transp A = --A},matrix_lie_bracket,matrix_add,(%%):real->real^N^N->real^N^N,(mat 0 :real^N^N))`;;
 
let LIE_ALGEBRA_OF_SOG = prove
    (`(!a:real^N^N. lie_alg_set (lie_algebra_of_sog (group_mlg(rotation_group a))) = { A:real^N^N | transp A = --A}) /\
    (!a:real^N^N. lie_bracket (lie_algebra_of_sog (group_mlg (rotation_group a))) = matrix_lie_bracket) /\
    (!a:real^N^N. lie_alg_add (lie_algebra_of_sog (group_mlg (rotation_group a))) = matrix_add) /\
    (!a:real^N^N. lie_alg_mul (lie_algebra_of_sog (group_mlg (rotation_group a))) = (%%)) /\
    (!a:real^N^N. lie_alg_zero (lie_algebra_of_sog (group_mlg (rotation_group a))) = mat 0)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN 
    MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl lie_algebra_of_sog)))))
   (CONJUNCT2 lie_algebra_tybij)))) THEN
    REWRITE_TAC[GSYM lie_algebra_of_sog] THEN 
    SIMP_TAC[MATRIX_LIE_BRACKET_BILINEAR_ALT;MATRIX_LIE_BRACKET_SSM_ALT;MATRIX_LIE_BRACKET_JACOBI_I;GSYM MATRIX_ADD_ASSOC] THEN
    SIMP_TAC[lie_alg_set; lie_bracket; lie_alg_add; lie_alg_mul;lie_alg_zero]);;

(* ------------------------------------------------------------------------- *)
(* matrix QR decomposition                                                   *)
(* ------------------------------------------------------------------------- *)
  
let ORTHOGONAL_MATRIX_REFLECT_ALONG = prove
    (`!v:real^N. orthogonal_matrix(matrix(reflect_along v))`,
    GEN_TAC THEN ASM_CASES_TAC `v = (vec 0):real^N` THENL
    [ASM_SIMP_TAC[REFLECT_ALONG_ZERO;MATRIX_I;ORTHOGONAL_MATRIX_ID];ALL_TAC] THEN
    MP_TAC (ISPEC `v:real^N` ROTOINVERSION_MATRIX_REFLECT_ALONG) THEN
    ASM_SIMP_TAC[rotoinversion_matrix]);;

let REFLECT_ALONG_EXISTS = prove
    (`!x:real^N u:real^N. norm(u) = &1 ==> ?v. reflect_along v x = norm(x) % u`,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `x = (vec 0):real^N` THENL
    [ASM_SIMP_TAC[NORM_0;VECTOR_MUL_LZERO;REFLECT_ALONG_0];ALL_TAC] THEN
    ASM_CASES_TAC `x = norm(x:real^N) % (u:real^N)` THENL
    [EXISTS_TAC `(vec 0):real^N` THEN
     ASM_MESON_TAC[REFLECT_ALONG_ZERO;I_THM;EQ_SYM_EQ];ALL_TAC] THEN
    EXISTS_TAC `x - norm(x:real^N) % (u:real^N)` THEN
    REWRITE_TAC[reflect_along] THEN
    MATCH_MP_TAC (MESON [VECTOR_ARITH `(x:real^N) - (x - y) = y`;VECTOR_MUL_LID] `!a. a = &1 ==> (x:real^N) - a % (x - y) = y`) THEN
    SIMP_TAC[DOT_LSUB;DOT_RSUB;DOT_RMUL;DOT_LMUL;REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[REAL_ARITH `a:real - b - (c - d) = (a + d) - (b + c)`] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `c * (x dot y) + c * (y dot x) = c * (x dot y) + c * (x dot y)`] THEN
    ASM_SIMP_TAC[GSYM NORM_POW_2;REAL_POW_2;REAL_MUL_LID;REAL_MUL_RID;GSYM REAL_MUL_2] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB;REAL_ARITH `a * (x / y) = (a * x) / y`] THEN
    REWRITE_TAC[REAL_DIV_EQ_1;REAL_ARITH `~(&2 * y = &0) <=> ~(y = &0)`] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
    SIMP_TAC[REAL_SUB_LDISTRIB;TAUT `~ ~ P <=> P`;GSYM REAL_POW_2;NORM_POW_2;GSYM DOT_RMUL] THEN
    SIMP_TAC[REAL_ARITH `x - y = &0 <=> x = y`;VECTOR_EQ] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[DOT_RMUL;DOT_LMUL;DOT_SQUARE_NORM;REAL_POW_ONE;REAL_MUL_RID] THEN
    ASM_SIMP_TAC[GSYM REAL_POW_2;NORM_POW_2;DOT_RMUL]);;
    
let REFLECT_ALONG_EXISTS_BASIS = prove
    (`!x:real^N i. 1 <= i /\ i <= dimindex (:N) ==> ?v. reflect_along v x = norm(x) % (basis i)`,
     REPEAT GEN_TAC THEN
     MP_TAC (ISPECL [`x:real^N`;`(basis i):real^N`] REFLECT_ALONG_EXISTS) THEN
     SIMP_TAC[DIMINDEX_GE_1;LE_REFL;NORM_BASIS]);;

let REFLECT_ALONG_EXISTS_LOW = prove
    (`!x:real^N u:real^N n. n <= dimindex(:N) /\ norm((lambda i. if (dimindex(:N) - n) < i then u$i else &0):real^N) = &1 ==> 
        ?v:real^N. reflect_along ((lambda i. if (dimindex(:N) - n) < i then v$i else &0):real^N) (lambda i. if (dimindex(:N) - n) < i then x$i else &0):real^N =
        norm((lambda i. if (dimindex(:N) - n) < i then x$i else &0):real^N) % (lambda i. if (dimindex(:N) - n) < i then u$i else &0):real^N`,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `(lambda i. if (dimindex(:N) - n) < i then (x:real^N)$i else &0) = (vec 0):real^N` THENL
    [ASM_SIMP_TAC[NORM_0;VECTOR_MUL_LZERO;REFLECT_ALONG_0];ALL_TAC] THEN
    ASM_CASES_TAC `(lambda i. if (dimindex(:N) - n) < i then (x:real^N)$i else &0):real^N = norm((lambda i. if (dimindex(:N) - n) < i then (x:real^N)$i else &0):real^N) % ((lambda i. if (dimindex(:N) - n) < i then (u:real^N)$i else &0):real^N)` THENL
    [EXISTS_TAC `(vec 0):real^N` THEN
     REWRITE_TAC[VEC_COMPONENT;COND_ID;GSYM vec] THEN
     ASM_MESON_TAC[REFLECT_ALONG_ZERO;I_THM;EQ_SYM_EQ];ALL_TAC] THEN
    EXISTS_TAC `(lambda i. if (dimindex(:N) - n) < i then (x:real^N)$i else &0):real^N - norm((lambda i. if (dimindex(:N) - n) < i then (x:real^N)$i else &0):real^N) % ((lambda i. if (dimindex(:N) - n) < i then (u:real^N)$i else &0):real^N)` THEN
    SUBGOAL_THEN `(lambda i. if dimindex (:N) - n < i
            then ((lambda i. if dimindex (:N) - n < i then (x:real^N)$i else &0):real^N - norm ((lambda i. if dimindex (:N) - n < i then x$i else &0):real^N) %
                  (lambda i. if dimindex (:N) - n < i then (u:real^N)$i else &0))$i
            else &0):real^N = 
            (lambda i. if dimindex (:N) - n < i then (x:real^N)$i else &0):real^N - norm ((lambda i. if dimindex (:N) - n < i then x$i else &0):real^N) %
                  (lambda i. if dimindex (:N) - n < i then (u:real^N)$i else &0)` SUBST1_TAC THENL
    [SIMP_TAC[CART_EQ;LAMBDA_BETA;VECTOR_SUB_COMPONENT;VECTOR_MUL_COMPONENT] THEN
     ASM_ARITH_TAC;ALL_TAC] THEN
    REWRITE_TAC[reflect_along] THEN
    MATCH_MP_TAC (MESON [VECTOR_ARITH `(x:real^N) - (x - y) = y`;VECTOR_MUL_LID] `!a. a = &1 ==> (x:real^N) - a % (x - y) = y`) THEN
    SIMP_TAC[DOT_LSUB;DOT_RSUB;DOT_RMUL;DOT_LMUL;REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[REAL_ARITH `a:real - b - (c - d) = (a + d) - (b + c)`] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `c * (x dot y) + c * (y dot x) = c * (x dot y) + c * (x dot y)`] THEN
    ASM_SIMP_TAC[GSYM NORM_POW_2;REAL_POW_2;REAL_MUL_LID;REAL_MUL_RID;GSYM REAL_MUL_2] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB;REAL_ARITH `a * (x / y) = (a * x) / y`] THEN
    REWRITE_TAC[REAL_DIV_EQ_1;REAL_ARITH `~(&2 * y = &0) <=> ~(y = &0)`] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
    SIMP_TAC[REAL_SUB_LDISTRIB;TAUT `~ ~ P <=> P`;GSYM REAL_POW_2;NORM_POW_2;GSYM DOT_RMUL] THEN
    SIMP_TAC[REAL_ARITH `x - y = &0 <=> x = y`;VECTOR_EQ] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[DOT_RMUL;DOT_LMUL;DOT_SQUARE_NORM;REAL_POW_ONE;REAL_MUL_RID] THEN
    ASM_SIMP_TAC[GSYM REAL_POW_2;NORM_POW_2;DOT_RMUL]);;
        
let REFLECT_ALONG_EXISTS_BASIS_LOW = prove
    (`!x:real^N k n. (dimindex(:N) - n) < k /\ k <= dimindex (:N) /\ n <= dimindex(:N) ==> ?v:real^N.
        reflect_along ((lambda i. if (dimindex(:N) - n) < i then v$i else &0):real^N) (lambda i. if (dimindex(:N) - n) < i then x$i else &0):real^N =
        norm((lambda i. if (dimindex(:N) - n) < i then x$i else &0):real^N) % (basis k)`,
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPECL [`x:real^N`;`(basis k):real^N`;`n:num`] REFLECT_ALONG_EXISTS_LOW) THEN
    SUBGOAL_THEN `(lambda i. if dimindex (:N) - n < i then ((basis k):real^N)$i else &0):real^N = ((basis k):real^N)` SUBST1_TAC THENL
    [SIMP_TAC[CART_EQ;LAMBDA_BETA;BASIS_COMPONENT] THEN ASM_ARITH_TAC;ALL_TAC] THEN
    ANTS_TAC THENL
    [ASM_SIMP_TAC[] THEN MATCH_MP_TAC NORM_BASIS THEN ASM_ARITH_TAC;ALL_TAC] THEN
    SIMP_TAC[]);;
    
let REFLECT_ALONG_EXISTS_BASIS_1 = prove
    (`!x:real^N. ?v. reflect_along v x = norm(x) % (basis 1)`,
     GEN_TAC THEN
     MP_TAC (ISPECL [`x:real^N`;`(basis 1):real^N`] REFLECT_ALONG_EXISTS) THEN
     SIMP_TAC[DIMINDEX_GE_1;LE_REFL;NORM_BASIS]);;

let MATRIX_REFLECT_ALONG = prove
    (`!v:real^N. matrix(reflect_along v) = mat 1 - (&2 / (v dot v)) %% (columnvector v ** rowvector v)`,
    SIMP_TAC[CART_EQ;LAMBDA_BETA;matrix;reflect_along;mat;dot;columnvector;rowvector;matrix_mul;matrix_cmul;VECTOR_SUB_COMPONENT;VECTOR_MUL_COMPONENT;BASIS_COMPONENT;MATRIX_SUB_COMPONENT] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC[COND_LMUL_0;DIMINDEX_1;SUM_SING_NUMSEG;GSYM SUM_RESTRICT_SET;REAL_MUL_LID;IN_NUMSEG] THEN
    ASM_SIMP_TAC[SET_RULE `1 <= i' /\ i' <= dimindex (:N) ==> {i | (1 <= i /\ i <= dimindex (:N)) /\ i = i'} = {i'}`;SUM_SING] THEN ARITH_TAC);;
    
let MATRIX_REFLECT_ALONG_LOW = prove
    (`!v:real^N n. n <= dimindex(:N) ==> 
        matrix(reflect_along ((lambda i. if (dimindex(:N) - n) < i then v$i else &0):real^N)) = 
        (lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j 
                    then (mat 1 - (&2 / (((lambda i. if (dimindex(:N) - n) < i then v$i else &0):real^N) dot ((lambda i. if (dimindex(:N) - n) < i then v$i else &0):real^N))) %% (columnvector v ** rowvector v))$i$j
                    else if i = j then &1 else &0):real^N^N`,
    REWRITE_TAC[MATRIX_REFLECT_ALONG] THEN
    SIMP_TAC[CART_EQ;LAMBDA_BETA;mat;columnvector;rowvector;matrix_mul;matrix_cmul;MATRIX_SUB_COMPONENT] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC[COND_LMUL_0;COND_RMUL_0;DIMINDEX_1;SUM_SING_NUMSEG] THEN
    ASM_ARITH_TAC);;

let REFLECT_ALONG_TRANSFORM = prove
    (`!v x:real^N. reflect_along v x = matrix(reflect_along v) ** x`,
    REWRITE_TAC[MATRIX_REFLECT_ALONG;MATRIX_VECTOR_MUL_SUB_RDISTRIB;MATRIX_VECTOR_MUL_LID;MATRIX_VECTOR_LMUL] THEN
    REWRITE_TAC[reflect_along;REAL_ARITH `&2 * a / b = (&2 / b) * a`] THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    REWRITE_TAC[VECTOR_ARITH `x - a % (b % y) - (x - a % z) = a % (z - b % y)`;VECTOR_MUL_EQ_0] THEN 
    REPEAT GEN_TAC THEN DISJ2_TAC THEN
    SIMP_TAC[CART_EQ;LAMBDA_BETA;dot;columnvector;rowvector;matrix_mul;matrix_vector_mul;VECTOR_SUB_COMPONENT;VEC_COMPONENT;VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[DIMINDEX_1;SUM_SING_NUMSEG;GSYM SUM_RMUL;GSYM REAL_MUL_ASSOC] THEN
    SIMP_TAC[GSYM SUM_SUB_NUMSEG] THEN
    SIMP_TAC[REAL_MUL_AC;SUM_0;REAL_SUB_REFL]);;

let MATRIX_MUL_DIMINDEX_UPP = prove
    (`!a:num->num->real q:num->num->real n. 1 <= n /\ n <= dimindex(:N) ==>
        (lambda i j. if i <= n /\ j <= n then a i j else if i = j then &1 else &0):real^N^N **
        (lambda i j. if i <= n /\ j <= n then q i j else if i = j then &1 else &0):real^N^N = 
        (lambda i j. if i <= n /\ j <= n then sum (1..n) (\k. (a i k) * (q k j)) else if i = j then &1 else &0):real^N^N`,
    SIMP_TAC[matrix_mul;LAMBDA_BETA;CART_EQ] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
    [SUBGOAL_THEN `(1..dimindex(:N)) = (1..(n + (dimindex(:N) - n)))` SUBST1_TAC THENL
     [ASM_SIMP_TAC[EXTENSION;IN_NUMSEG] THEN ASM_ARITH_TAC;ALL_TAC] THEN 
     ASM_SIMP_TAC[SUM_ADD_SPLIT;LE_ADDR] THEN
     SIMP_TAC[COND_RMUL;COND_LMUL;REAL_MUL_LZERO;REAL_MUL_RZERO;REAL_MUL_LID;REAL_MUL_RID] THEN
     SUBGOAL_THEN `sum (n + 1..n + dimindex (:N) - n) (\k. if k <= n then a i k * q k i'
      else if i = k then if k = i' then &1 else &0 else &0) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN ASM_ARITH_TAC;ALL_TAC] THEN
     SIMP_TAC[REAL_ADD_RID];ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
    COND_CASES_TAC THENL
    [ASM_SIMP_TAC[COND_RMUL_0;COND_LMUL_0;REAL_MUL_LID] THEN
     REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
     ASM_SIMP_TAC[SET_RULE `1 <= i' /\ i' <= dimindex (:N) ==> {k | (1 <= k /\ k <= dimindex (:N)) /\ i' = k} = {i'}`;SUM_SING;IN_NUMSEG];ALL_TAC] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN ASM_ARITH_TAC);;
    
let MATRIX_MUL_DIMINDEX_UPP_ALT = prove
    (`!a:num->num->real q:num->num->real n. 1 <= n /\ n <= dimindex(:N) ==>
        (lambda i j. if i <= n /\ j <= n then a i j else if i = j then &1 else &0):real^N^N **
        (lambda i j. if i <= n /\ j <= n then q i j else if i = j then &1 else &0):real^N^N = 
        (lambda i j. if i <= n /\ j <= n then (((lambda i j. if i <= n /\ j <= n then a i j else &0):real^N^N) ** ((lambda i j. if i <= n /\ j <= n then q i j else &0):real^N^N))$i$j else if i = j then &1 else &0):real^N^N`,
    SIMP_TAC[MATRIX_MUL_DIMINDEX_UPP] THEN
    SIMP_TAC[CART_EQ;matrix_mul;LAMBDA_BETA] THEN
    SIMP_TAC[COND_LMUL_0;COND_RMUL_0;GSYM SUM_RESTRICT_SET;IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
    [ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_SUPERSET THEN
     SIMP_TAC[SUBSET;IN_ELIM_THM;IN_NUMSEG] THEN ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC[]);;
    
let MATRIX_MUL_DIMINDEX_LOW = prove
    (`!a:num->num->real q:num->num->real n. 1 <= n /\ n <= dimindex(:N) ==>
        (lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j then a i j else if i = j then &1 else &0):real^N^N **
        (lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j then q i j else if i = j then &1 else &0):real^N^N = 
        (lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j then sum ((dimindex(:N) - n + 1)..dimindex(:N)) (\k. (a i k) * (q k j)) else if i = j then &1 else &0):real^N^N`,
    SIMP_TAC[matrix_mul;LAMBDA_BETA;CART_EQ] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
    [SUBGOAL_THEN `(1..dimindex(:N)) = (1..(dimindex(:N) - n + n))` SUBST1_TAC THENL
     [ASM_SIMP_TAC[EXTENSION;IN_NUMSEG] THEN ASM_ARITH_TAC;ALL_TAC] THEN 
     ASM_SIMP_TAC[SUM_ADD_SPLIT;LE_ADDR] THEN
     SIMP_TAC[COND_RMUL;COND_LMUL;REAL_MUL_LZERO;REAL_MUL_RZERO;REAL_MUL_LID;REAL_MUL_RID] THEN
     SUBGOAL_THEN `sum (1..dimindex (:N) - n) (\k. if dimindex (:N) - n < k then a i k * q k i' else if i = k then if k = i' then &1 else &0 else &0) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN ASM_ARITH_TAC;ALL_TAC] THEN
     ASM_SIMP_TAC[REAL_ADD_LID;SUB_ADD] THEN 
     MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_ARITH_TAC;ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
    COND_CASES_TAC THENL
    [ASM_SIMP_TAC[COND_RMUL;COND_LMUL;REAL_MUL_LZERO;REAL_MUL_RZERO;REAL_MUL_LID;REAL_MUL_RID] THEN
     REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
     ASM_SIMP_TAC[SET_RULE `1 <= i' /\ i' <= dimindex (:N) ==> {k | (1 <= k /\ k <= dimindex (:N)) /\ i' = k} = {i'}`;SUM_SING;IN_NUMSEG];ALL_TAC] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN ASM_ARITH_TAC);;
    
let MATRIX_MUL_DIMINDEX_LOW_ALT = prove
    (`!a:num->num->real q:num->num->real n. 1 <= n /\ n <= dimindex(:N) ==>
        (lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j then a i j else if i = j then &1 else &0):real^N^N **
        (lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j then q i j else if i = j then &1 else &0):real^N^N = 
        (lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j then (((lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j then a i j else &0):real^N^N) ** ((lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j then q i j else &0):real^N^N))$i$j else if i = j then &1 else &0):real^N^N`,
    SIMP_TAC[MATRIX_MUL_DIMINDEX_LOW] THEN
    SIMP_TAC[CART_EQ;matrix_mul;LAMBDA_BETA] THEN
    SIMP_TAC[COND_LMUL_0;COND_RMUL_0;GSYM SUM_RESTRICT_SET;IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
    [ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_SUPERSET THEN
     SIMP_TAC[SUBSET;IN_ELIM_THM;IN_NUMSEG] THEN ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC[]);;

let MATRIX_QR_DECOMPOSITION_ALT = prove
    (`!n A:real^N^N. 1 <= n /\ n <= dimindex(:N) ==>
                ?q r. orthogonal_matrix ((lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j then q i j else if i = j then &1 else &0):real^N^N) /\
                (!i j. dimindex (:N) - n < i /\ i <= dimindex(:N) /\
                       dimindex (:N) - n < j /\ j <= dimindex(:N) /\ j < i ==> r i j = &0) /\
                (lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j then A$i$j else if i = j then &1 else &0):real^N^N =
                ((lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j then q i j else if i = j then &1 else &0):real^N^N) **
                ((lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j then r i j else if i = j then &1 else &0):real^N^N)`,
    INDUCT_TAC THENL [ARITH_TAC;ALL_TAC] THEN GEN_TAC THEN
    ASM_CASES_TAC `n = 0` THENL
    [ASM_SIMP_TAC[GSYM (num_CONV `1`)] THEN STRIP_TAC THEN
     EXISTS_TAC `(\i:num j. if i = j then &1 else &0)` THEN
     EXISTS_TAC `(\i j. (A:real^N^N)$i$j)` THEN 
     SIMP_TAC[COND_ID;GSYM mat] THEN
     SIMP_TAC[ORTHOGONAL_MATRIX_ID;TRANSP_MAT;MATRIX_MUL_LID;MATRIX_MUL_RID] THEN
     ASM_ARITH_TAC;ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    ONCE_REWRITE_TAC[TAUT `(P ==> Q ==> R ==> S) <=> (R /\ Q) ==> P ==> S`] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [ARITH_RULE `~(n = 0) <=> 1 <= n`]) THEN
    ASM_SIMP_TAC[ARITH_RULE `SUC i <= N ==> i <= N`] THEN
    MP_TAC (ISPECL [`(column (dimindex(:N) - n) (A:real^N^N))`;`dimindex(:N) - n`;`SUC n`] REFLECT_ALONG_EXISTS_BASIS_LOW) THEN
    ASM_SIMP_TAC[ARITH_RULE `SUC n <= N ==> N - SUC n < N - n`;ARITH_RULE `(N:num) - n <= N`] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` MP_TAC) THEN
    INTRO_TAC "suc" THEN
    DISCH_THEN(MP_TAC o SPEC `( ((lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j then (matrix(reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N)))$i$j else if i = j then &1 else &0):real^N^N) ** 
        ((lambda i j.
               if dimindex (:N) - n < i /\ dimindex (:N) - n < j
               then (A:real^N^N)$i$j
               else if i = j then &1 else &0):real^N^N) + 
               ((lambda i j. if dimindex (:N) - n < i /\ dimindex (:N) - n < j 
               then (matrix(reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N)))$i$(dimindex (:N) - n) * (A:real^N^N)$(dimindex (:N) - n)$j
               else &0):real^N^N) )`) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:num->num->real` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num->num->real` MP_TAC) THEN
    INTRO_TAC "ort upp n" THEN 
    EXISTS_TAC `(\i:num j. if (dimindex(:N) - SUC n) < i /\ (dimindex(:N) - SUC n) < j
            then
                ( ((lambda i j. if (dimindex(:N) - SUC n) < i /\ (dimindex(:N) - SUC n) < j then transp(matrix(reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N)))$i$j else if i = j then &1 else &0):real^N^N) **
                ((lambda i j. if (dimindex(:N) - n) < i /\ (dimindex(:N) - n) < j then q i j else if i = j then &1 else &0):real^N^N) )$i$j
            else if i = j then &1 else &0)` THEN
    SIMP_TAC[] THEN
    SUBGOAL_THEN `(lambda i j. if dimindex (:N) - SUC n < i /\ dimindex (:N) - SUC n < j
          then ((lambda i j. if dimindex (:N) - SUC n < i /\ dimindex (:N) - SUC n < j
                     then transp(matrix (reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N)))$i$j
                     else if i = j then &1 else &0):real^N^N **
                (lambda i j.
                     if dimindex (:N) - n < i /\ dimindex (:N) - n < j
                     then q i j
                     else if i = j then &1 else &0):real^N^N)$i$j
          else if i = j then &1 else &0):real^N^N = 
          (lambda i j. if dimindex (:N) - SUC n < i /\ dimindex (:N) - SUC n < j
                     then transp(matrix (reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N)))$i$j
                     else if i = j then &1 else &0):real^N^N **
          (lambda i j.
                     if dimindex (:N) - n < i /\ dimindex (:N) - n < j
                     then q i j
                     else if i = j then &1 else &0):real^N^N` SUBST1_TAC THENL
    [SIMP_TAC[CART_EQ;LAMBDA_BETA;matrix_mul] THEN
     REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN
     POP_ASSUM MP_TAC THEN SIMP_TAC[DE_MORGAN_THM] THEN
     REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COND_RMUL;COND_LMUL] THEN
     SIMP_TAC[REAL_MUL_LZERO;REAL_MUL_RZERO;REAL_MUL_LID;REAL_MUL_RID;COND_ID] THEN
     COND_CASES_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `~(N - SUC n < i) /\ i = i' ==> ~(N - n < i')`] THEN
      SUBGOAL_THEN `(1..dimindex (:N)) = i' INSERT ((1..dimindex (:N)) DELETE i')` SUBST1_TAC THENL [ASM_SIMP_TAC[GSYM INSERT_DELETE;IN_NUMSEG];ALL_TAC] THEN
      SIMP_TAC[FINITE_NUMSEG;FINITE_DELETE;SUM_CLAUSES;SET_RULE `~(x IN (s DELETE x))`] THEN
      SIMP_TAC[GSYM SUM_RESTRICT_SET;SET_RULE `{x | x IN (1..dimindex (:N)) DELETE i' /\ i' = x} = {}`;SUM_CLAUSES;REAL_ADD_RID] THEN
      ASM_ARITH_TAC;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN 
      X_GEN_TAC `k:num` THEN REPEAT STRIP_TAC THEN SIMP_TAC[] THEN
      COND_CASES_TAC THENL 
      [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_ARITH_TAC;SIMP_TAC[]];ALL_TAC;ALL_TAC] THENL
     [ASM_SIMP_TAC[ARITH_RULE `~(N - SUC n < i) /\ i = i' ==> ~(N - n < i')`] THEN
      SUBGOAL_THEN `(1..dimindex (:N)) = i' INSERT ((1..dimindex (:N)) DELETE i')` SUBST1_TAC THENL [ASM_SIMP_TAC[GSYM INSERT_DELETE;IN_NUMSEG];ALL_TAC] THEN
      SIMP_TAC[FINITE_NUMSEG;FINITE_DELETE;SUM_CLAUSES;SET_RULE `~(x IN (s DELETE x))`] THEN
      SIMP_TAC[GSYM SUM_RESTRICT_SET;SET_RULE `{x | x IN (1..dimindex (:N)) DELETE i' /\ i' = x} = {}`;SUM_CLAUSES;REAL_ADD_RID] THEN
      ASM_ARITH_TAC;ALL_TAC] THEN
     CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
     SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
     COND_CASES_TAC THEN ASM_ARITH_TAC;ALL_TAC] THEN
    EXISTS_TAC `(\i:num j. if (dimindex(:N) - SUC n) < i /\ (dimindex(:N) - SUC n) < j /\ i <= j then if i = (dimindex(:N) - n) /\ j = (dimindex(:N) - n) 
          then  norm ((lambda i. if dimindex (:N) - SUC n < i
                 then (column (dimindex (:N) - n) (A:real^N^N))$i 
                 else &0):real^N)
          else if i = (dimindex(:N) - n) /\ ~(j = (dimindex(:N) - n)) 
                then  (matrix(reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N))$(dimindex (:N) - n)$(dimindex (:N) - n) * (A:real^N^N)$(dimindex (:N) - n)$j + 
                    sum (dimindex (:N) - n + 1..dimindex (:N))
                    (\k. matrix(reflect_along((lambda i. if dimindex (:N) - SUC n < i
                 then (v:real^N)$i else &0):real^N))$(dimindex (:N) - n)$k *(A:real^N^N)$k$j))
                else r i j
     else if i = j then &1 else &0)` THEN
    SUBGOAL_THEN `(lambda i j.
      if dimindex (:N) - SUC n < i /\ dimindex (:N) - SUC n < j
      then (transp(matrix (reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N))))$i$j
      else if i = j then &1 else &0):real^N^N =
      transp (lambda i j.
      if dimindex (:N) - SUC n < i /\ dimindex (:N) - SUC n < j
      then matrix (reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N))$i$j
      else if i = j then &1 else &0):real^N^N` ASSUME_TAC THENL
    [SIMP_TAC[CART_EQ;LAMBDA_BETA;TRANSP_COMPONENT] THEN ARITH_TAC;ALL_TAC] THEN
    SUBGOAL_THEN `orthogonal_matrix
    ((lambda i j.
      if dimindex (:N) - SUC n < i /\ dimindex (:N) - SUC n < j
      then matrix (reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N))$i$j
      else if i = j then &1 else &0):real^N^N)` ASSUME_TAC THENL
    [MP_TAC (ISPEC `(lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N` ORTHOGONAL_MATRIX_REFLECT_ALONG) THEN
     SIMP_TAC[ORTHOGONAL_MATRIX] THEN
     SIMP_TAC[CART_EQ;LAMBDA_BETA;matrix_mul;MAT_COMPONENT;transp] THEN
     SIMP_TAC[RIGHT_IMP_FORALL_THM] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`;`i':num`]) THEN
     ASM_SIMP_TAC[] THEN STRIP_TAC THEN
     SUBGOAL_THEN `(1..dimindex(:N)) = (1..(dimindex(:N) - SUC n + SUC n))` SUBST1_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `SUC n <= N ==> N - SUC n + SUC n = N`];ALL_TAC] THEN 
     ASM_SIMP_TAC[SUM_ADD_SPLIT;LE_ADDR] THEN
     SUBGOAL_THEN `sum (1..dimindex (:N) - SUC n)
     (\k. (if dimindex (:N) - SUC n < k /\ dimindex (:N) - SUC n < i
       then matrix (reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N))$k$i
       else if k = i then &1 else &0) *
      (if dimindex (:N) - SUC n < k /\ dimindex (:N) - SUC n < i'
       then matrix (reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N))$k$i'
       else if k = i' then &1 else &0)) = 
       sum (1..dimindex (:N) - SUC n) (\k. (if k = i then &1 else &0) * (if k = i' then &1 else &0))` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ARITH_TAC;ALL_TAC] THEN
     SUBGOAL_THEN `sum (dimindex (:N) - SUC n + 1..dimindex (:N) - SUC n + SUC n)
     (\k. (if dimindex (:N) - SUC n < k /\ dimindex (:N) - SUC n < i
       then matrix (reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N))$k$i
       else if k = i then &1 else &0) *
      (if dimindex (:N) - SUC n < k /\ dimindex (:N) - SUC n < i'
       then matrix (reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N))$k$i'
       else if k = i' then &1 else &0)) = 
       sum (dimindex (:N) - SUC n + 1..dimindex (:N) - SUC n + SUC n)
     (\k. (if dimindex (:N) - SUC n < i
       then matrix (reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N))$k$i
       else if k = i then &1 else &0) *
      (if dimindex (:N) - SUC n < i'
       then matrix (reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N))$k$i'
       else if k = i' then &1 else &0))` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ARITH_TAC;ALL_TAC] THEN
     ASM_CASES_TAC `dimindex (:N) - SUC n < i /\ dimindex (:N) - SUC n < i'` THENL
     [ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `sum (1..dimindex (:N) - SUC n)
      (\k. (if k = i then &1 else &0) * (if k = i' then &1 else &0)) = &0` SUBST1_TAC THENL
      [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN 
       SIMP_TAC[COND_RMUL_0;COND_LMUL_0;REAL_MUL_LID] THEN
       ASM_ARITH_TAC;ALL_TAC] THEN
      SIMP_TAC[REAL_ADD_LID] THEN
      SUBGOAL_THEN `(dimindex (:N) - SUC n + 1..dimindex (:N) - SUC n + SUC n) = {k | k IN (1..dimindex (:N)) /\ dimindex (:N) - SUC n < k}` SUBST1_TAC THENL
      [SIMP_TAC[IN_ELIM_THM;EXTENSION;IN_NUMSEG] THEN 
       ASM_SIMP_TAC[SUB_ADD;ARITH_RULE `dimindex (:N) - SUC n + 1 <= x <=> 1 <= x /\ dimindex (:N) - SUC n < x`;CONJ_ACI];ALL_TAC] THEN
      SIMP_TAC[SUM_RESTRICT_SET] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC `k:num` THEN REPEAT STRIP_TAC THEN SIMP_TAC[] THEN
      COND_CASES_TAC THENL [SIMP_TAC[];ALL_TAC] THEN
      ASM_SIMP_TAC[matrix;reflect_along;LAMBDA_BETA;dot;VECTOR_SUB_COMPONENT;VECTOR_MUL_COMPONENT;BASIS_COMPONENT] THEN
      SIMP_TAC[REAL_MUL_RZERO] THEN ASM_ARITH_TAC;ALL_TAC] THEN
     ASM_SIMP_TAC[COND_RMUL;COND_LMUL] THEN
     SIMP_TAC[REAL_MUL_LZERO;REAL_MUL_RZERO;REAL_MUL_LID;REAL_MUL_RID;COND_ID] THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
     COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[GSYM SUM_ADD_SPLIT;LE_ADDR;SUB_ADD] THEN
      REWRITE_TAC[GSYM SUM_RESTRICT_SET;IN_NUMSEG] THEN
      ASM_SIMP_TAC[SET_RULE `1 <= i' /\ i' <= dimindex (:N) ==> {k | (1 <= k /\ k <= dimindex (:N)) /\ k = i'} = {i'}`;SUM_SING];ALL_TAC] THEN
     REWRITE_TAC[COND_ID;SUM_0;REAL_ADD_LID] THEN
     ASM_SIMP_TAC[SUB_ADD] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
     MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
     X_GEN_TAC `k:num` THEN REPEAT STRIP_TAC THEN
     SIMP_TAC[COND_ID] THEN ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_MUL;ORTHOGONAL_MATRIX_TRANSP] THEN
    SIMP_TAC[ARITH_RULE `(j:num) < i ==> ~(i <= j)`;ARITH_RULE `(j:num) < i ==> ~(i = j)`] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
    MP_TAC ((ISPECL [`(lambda i j. if dimindex (:N) - SUC n < i /\ dimindex (:N) - SUC n < j then (matrix (reflect_along ((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N)))$i$j
      else if i = j then &1 else &0):real^N^N`;
      `(lambda i j.if dimindex (:N) - SUC n < i /\ dimindex (:N) - SUC n < j
      then (A:real^N^N)$i$j else if i = j then &1 else &0):real^N^N`] MATRIX_MUL_LCANCEL)) THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_IMP_INVERTIBLE] THEN 
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    SIMP_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_MUL_ASSOC;ORTHOGONAL_MATRIX_TRANSP_RMUL;MATRIX_MUL_LID] THEN
    SUBGOAL_THEN `(lambda i j. if dimindex (:N) - n < i /\ dimindex (:N) - n < j
      then q i j else if i = j then &1 else &0):real^N^N = 
      (lambda i j. if dimindex (:N) - SUC n < i /\ dimindex (:N) - SUC n < j
      then if i = dimindex (:N) - n /\ j = dimindex (:N) - n 
            then &1 
            else if dimindex (:N) - n < i /\ dimindex (:N) - n < j 
                    then q i j else &0
      else if i = j then &1 else &0)` SUBST1_TAC THENL
    [SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
     REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `N - n < i ==> N - SUC n < i`;LT_IMP_NE];ALL_TAC] THEN
     SIMP_TAC[] THEN COND_CASES_TAC THEN
     ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_MUL_DIMINDEX_LOW] THEN SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
    [ASM_SIMP_TAC[] THEN
     ASM_SIMP_TAC[ARITH_RULE `1 <= SUC n /\ SUC n <= N ==> N - SUC n + 1 <= N`;SUM_CLAUSES_LEFT] THEN
     ASM_SIMP_TAC[ARITH_RULE `SUC n <= N ==> N - SUC n + 1 = N - n`] THEN
     ASM_SIMP_TAC[ARITH_RULE `N - SUC n < i ==> N - n <= i`;ARITH_RULE `~((x:num) < x)`] THEN
     SUBGOAL_THEN `sum (dimindex (:N) - n + 1..dimindex (:N))
     (\k. (if i = dimindex (:N) - n /\ k = dimindex (:N) - n
       then &1
       else if dimindex (:N) - n < i /\ dimindex (:N) - n < k
            then q i k
            else &0) *
      (if k <= i'
       then if k = dimindex (:N) - n /\ i' = dimindex (:N) - n
            then norm
                 ((lambda i. if dimindex (:N) - SUC n < i
                            then column (dimindex (:N) - n) (A:real^N^N)$i
                            else &0):real^N)
            else if k = dimindex (:N) - n /\ ~(i' = dimindex (:N) - n)
                 then (matrix(reflect_along((lambda i. if dimindex (:N) - SUC n < i then (v:real^N)$i else &0):real^N))$(dimindex (:N) - n)$(dimindex (:N) - n) * A$(dimindex (:N) - n)$i' + 
                 sum (dimindex (:N) - n + 1..dimindex (:N))
                    (\k. matrix(reflect_along((lambda i. if dimindex (:N) - SUC n < i
                 then (v:real^N)$i else &0):real^N))$(dimindex (:N) - n)$k *(A:real^N^N)$k$i'))
                 else r k i'
       else if k = i' then &1 else &0)) =
       sum (dimindex (:N) - n + 1..dimindex (:N))
     (\k. (if dimindex (:N) - n < i then q i k else &0) *
      (if k <= i' then r k i' else if k = i' then &1 else &0))` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN 
      SIMP_TAC[ARITH_RULE `(N:num) - n < k ==> ~(k = N - n)`;ARITH_RULE `N - n + 1 <= k <=> N - n < k`];ALL_TAC] THEN
     POP_ASSUM MP_TAC THEN
     ASM_SIMP_TAC[ARITH_RULE `SUC n <= N ==> (N - SUC n < i <=> (i = N - n \/ N - n < i))`] THEN
     REPEAT STRIP_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `~((x:num) < x)`;REAL_MUL_LZERO;REAL_MUL_LID;SUM_0;REAL_ADD_RID] THEN
      REMOVE_THEN "suc" MP_TAC THEN
      REWRITE_TAC[REFLECT_ALONG_TRANSFORM] THEN
      SIMP_TAC[CART_EQ;LAMBDA_BETA;MATRIX_VECTOR_MUL_COMPONENT;BASIS_COMPONENT;VECTOR_MUL_COMPONENT;dot] THEN 
      DISCH_THEN(MP_TAC o SPEC `dimindex (:N) - n`) THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC n <= N ==> 1 <= N - n`;ARITH_RULE `(N:num) - n <= N`] THEN
      ASM_SIMP_TAC[COND_RMUL_0;GSYM SUM_RESTRICT_SET;IN_NUMSEG;ARITH_RULE `SUC n <= N ==> (((1 <= i /\ i <= N) /\ N - SUC n < i) <=> (N - n <= i /\ i <= N))`] THEN
      REWRITE_TAC[REAL_MUL_RID;GSYM IN_NUMSEG;SET_RULE `{x | x IN dimindex (:N) - n..dimindex (:N)} = (dimindex (:N) - n..dimindex (:N))`] THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC n <= N ==> 1 <= N - n`;ARITH_RULE `(N:num) - n <= N`;SUM_CLAUSES_LEFT;column;LAMBDA_BETA] THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC n <= N ==> ((i = N - n \/ N - n < i) <=> N - SUC n < i)`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_ARITH `(a:real) + b = a + c <=> b = c`] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN
      SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(A:real^N^N)$k$(dimindex (:N) - n) = ((lambda i. A$i$(dimindex (:N) - n)):real^N)$k` SUBST1_TAC THENL
      [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LAMBDA_BETA THEN ASM_ARITH_TAC;ALL_TAC] THEN
      SIMP_TAC[];ALL_TAC;ALL_TAC;ALL_TAC] THENL
     [ASM_SIMP_TAC[ARITH_RULE `~((x:num) < x)`;ARITH_RULE `(x:num) < i ==> ~(i = x)`;REAL_MUL_LZERO;REAL_MUL_LID;SUM_0;REAL_ADD_RID];ALL_TAC;ALL_TAC] THENL
     [ASM_SIMP_TAC[ARITH_RULE `(x:num) < i ==> ~(i = x)`;REAL_MUL_LZERO;REAL_ADD_LID] THEN
      SUBGOAL_THEN `sum (dimindex (:N) - n + 1..dimindex (:N))
      (\k. (q:num->num->real) i k *
      (if k <= dimindex (:N) - n
       then (r:num->num->real) k (dimindex (:N) - n)
       else if k = dimindex (:N) - n then &1 else &0)) = &0` SUBST1_TAC THENL
      [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
       SIMP_TAC[ARITH_RULE `x + 1 <= i ==> ~(i <= x)`;ARITH_RULE `x + 1 <= i ==> ~(i = x)`;REAL_MUL_RZERO];ALL_TAC] THEN
      REMOVE_THEN "suc" MP_TAC THEN
      REWRITE_TAC[REFLECT_ALONG_TRANSFORM] THEN
      SIMP_TAC[CART_EQ;LAMBDA_BETA;MATRIX_VECTOR_MUL_COMPONENT;BASIS_COMPONENT;VECTOR_MUL_COMPONENT;dot] THEN 
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
      ASM_SIMP_TAC[ARITH_RULE `(x:num) < i ==> ~(i = x)`;REAL_MUL_RZERO] THEN
      ASM_SIMP_TAC[COND_RMUL_0;GSYM SUM_RESTRICT_SET;IN_NUMSEG;ARITH_RULE `SUC n <= N ==> (((1 <= i /\ i <= N) /\ N - SUC n < i) <=> (N - n <= i /\ i <= N))`] THEN
      REWRITE_TAC[GSYM IN_NUMSEG;SET_RULE `{x | x IN dimindex (:N) - n..dimindex (:N)} = (dimindex (:N) - n..dimindex (:N))`] THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC n <= N ==> 1 <= N - n`;ARITH_RULE `(N:num) - n <= N`;SUM_CLAUSES_LEFT;column;LAMBDA_BETA] THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC n <= N ==> ((i = N - n \/ N - n < i) <=> N - SUC n < i)`] THEN
      MATCH_MP_TAC (REAL_ARITH `(a:real) = b ==> (a = c ==> b = c)`) THEN
      REWRITE_TAC[REAL_ARITH `(a:real) + b = a + c <=> b = c`] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN
      SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(A:real^N^N)$k$(dimindex (:N) - n) = ((lambda i. A$i$(dimindex (:N) - n)):real^N)$k` SUBST1_TAC THENL
      [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LAMBDA_BETA THEN ASM_ARITH_TAC;ALL_TAC] THEN
      SIMP_TAC[];ALL_TAC] THEN
     ASM_SIMP_TAC[ARITH_RULE `(x:num) < i ==> ~(i = x)`;REAL_MUL_LZERO;REAL_ADD_LID] THEN
     REMOVE_THEN "n" MP_TAC THEN
     ASM_SIMP_TAC[MATRIX_MUL_DIMINDEX_LOW;ARITH_RULE `SUC n <= N ==> n <= N`] THEN
     SIMP_TAC[CART_EQ;LAMBDA_BETA;RIGHT_IMP_FORALL_THM;MATRIX_ADD_COMPONENT] THEN
     DISCH_THEN(MP_TAC o SPECL [`i:num`;`i':num`]) THEN ASM_SIMP_TAC[] THEN
     SUBGOAL_THEN `sum (dimindex (:N) - n + 1..dimindex (:N))
     (\k. (q:num->num->real) i k * (if k <= i' then (r:num->num->real) k i' else if k = i' then &1 else &0)) =
     sum (dimindex (:N) - n + 1..dimindex (:N)) (\k. q i k * r k i')` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN REPEAT STRIP_TAC THEN
      SIMP_TAC[] THEN COND_CASES_TAC THENL [SIMP_TAC[];ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `~((k:num) <= i) ==> ~(k = i)`;REAL_MUL_RZERO] THEN
      REMOVE_THEN "upp" MP_TAC THEN
      DISCH_THEN(MP_TAC o SPECL [`k:num`;`i':num`]) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LE]) THEN
      ASM_SIMP_TAC[ARITH_RULE `x + 1 <= k ==> x < k`;REAL_MUL_RZERO];ALL_TAC] THEN
     ASM_SIMP_TAC[ARITH_RULE `SUC n <= N ==> ((i = N - n \/ N - n < i) <=> N - SUC n < i)`] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[REAL_ADD_SYM];ALL_TAC] THEN
     ASM_SIMP_TAC[]);;

let MATRIX_QR_DECOMPOSITION = prove
    (`!A:real^N^N.
                ?Q R:real^N^N. orthogonal_matrix Q /\
                (!i j. 1 <= i /\ i <= dimindex(:N) /\
                       1 <= j /\ j <= dimindex(:N) /\ j < i ==> R$i$j = &0) /\
                A = Q ** R`,
    GEN_TAC THEN
    MP_TAC (ISPECL [`dimindex(:N)`;`A:real^N^N`] MATRIX_QR_DECOMPOSITION_ALT) THEN
    SIMP_TAC[DIMINDEX_GE_1;LE_REFL;SUB_REFL;ARITH_RULE `0 < i <=> 1 <= i`] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:num->num->real` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num->num->real` MP_TAC) THEN
    SUBGOAL_THEN `!f:num->num->real. ((lambda i j.
           if 1 <= i /\ 1 <= j then f i j else if i = j then &1 else &0):real^N^N) = 
           ((lambda i j. f i j):real^N^N)` ASSUME_TAC THENL
    [SIMP_TAC[CART_EQ;LAMBDA_BETA];ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `(lambda i j. (q:num->num->real) i j):real^N^N` THEN
    EXISTS_TAC `(lambda i j. (r:num->num->real) i j):real^N^N` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[LAMBDA_BETA;CART_EQ]);;

(* ------------------------------------------------------------------------- *)
(* proof of Jacobi's formula (det derivative trace)                          *)
(* ------------------------------------------------------------------------- *)
    
let INVERTIBLE_MATRIX_RANK = prove
    (`!A:real^N^N. rank A = dimindex(:N) <=> invertible A`,
    SIMP_TAC[FULL_RANK_INJECTIVE;GSYM MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
    GEN_TAC THEN EQ_TAC THENL
    [STRIP_TAC THEN
     MP_TAC (ISPECL [`B:real^N^N`;`A:real^N^N`] MATRIX_INV_UNIQUE_LEFT) THEN
     ASM_SIMP_TAC[GSYM MATRIX_INV_LEFT];
     MESON_TAC[GSYM MATRIX_INV_LEFT]]);;
     
let CHARACTERISTIC_DET = prove
    (`!A:real^N^N. ?c:num->real. det(A) = product (1..dimindex(:N)) (\i. c i)`,   
    GEN_TAC THEN SIMP_TAC[EIGENVALUES_CHARACTERISTIC] THEN    
    MP_TAC(ISPEC `A:real^N^N` MATRIX_DIAGONALIZABLE) THEN
    DISCH_THEN(X_CHOOSE_THEN `P:real^N^N` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `D:real^N^N` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `Q:real^N^N` MP_TAC) THEN
    SIMP_TAC[DET_MUL;DET_DIAGONAL] THEN REPEAT STRIP_TAC THEN
    MP_TAC (ISPEC `P:real^N^N` DET_ORTHOGONAL_MATRIX) THEN
    MP_TAC (ISPEC `Q:real^N^N` DET_ORTHOGONAL_MATRIX) THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `(\i. if det(P:real^N^N) * det(Q:real^N^N) = -- &1 /\ i = dimindex(:N) then -- ((D:real^N^N)$i$i) else D$i$i)` THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_LID;REAL_MUL_RID;REAL_MUL_LNEG;REAL_MUL_RNEG;REAL_ARITH `~(&1 = -- &1)`;ARITH_EQ;REAL_NEG_NEG] THEN
    ONCE_REWRITE_TAC[(MESON [DIMINDEX_GE_1;ARITH_RULE `1 <= N ==> N = (N - 1) + 1`] `dimindex(:N) = dimindex(:N) - 1 + 1`)] THEN
    SIMP_TAC[PRODUCT_ADD_SPLIT;DIMINDEX_GE_1;GSYM (ARITH_RULE `1 <= N ==> N = (N - 1) + 1`);PRODUCT_SING_NUMSEG;REAL_MUL_RNEG;REAL_NEG_EQ;REAL_NEG_NEG;REAL_EQ_MUL_RCANCEL] THEN
    DISJ1_TAC THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN ARITH_TAC);;

let HAS_M_DERIVATIVE_MSUM_AT = prove
    (`!f x s.
     FINITE s /\
     (!a. a IN s ==> ((f a) has_m_derivative (f' a x)) (matrix_at x)) ==> 
    ((\x. msum s (\a. f a x)) has_m_derivative msum s (\a. f' a x)) (matrix_at x)`,
    GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC[MSUM_CLAUSES; HAS_M_DERIVATIVE_CONST] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_M_DERIVATIVE_ADD THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[IN_INSERT]);;

let HAS_M_DERIVATIVE_MSUM_NUMSEG_AT = prove
    (`!f x m n.
     (!i. m <= i /\ i <= n ==> ((f i) has_m_derivative (f' i x)) (matrix_at x))
     ==> ((\x. msum (m..n) (\i. f i x)) has_m_derivative
          msum (m..n) (\i. f' i x)) (matrix_at x)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_M_DERIVATIVE_MSUM_AT THEN
    ASM_REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG]);;

let HAS_MATRIX_DERIVATIVE_DROP2_MUL_WITHIN = prove
    (`!f:real^N^M->real^1^1 g:real^N^M->real^S^Q f' g' x:real^N^M s.
    (f has_matrix_derivative f') (matrix_at x within s) /\ 
    (g has_matrix_derivative g') (matrix_at x within s) 
        ==> ((\t:real^N^M. (drop_drop(f(t)) %% g(t))) has_matrix_derivative 
            (\h:real^N^M. drop_drop(f(x)) %% g'(h) + drop_drop(f'(h)) %% g(x))) (matrix_at x within s)`,
            REPEAT GEN_TAC THEN 
    MATCH_MP_TAC (REWRITE_RULE [TAUT `a /\ b /\ c ==> d <=> c ==> (a /\ b) ==> d`] HAS_MATRIX_DERIVATIVE_BILINEAR_WITHIN) THEN
    SIMP_TAC[bimlinear;MLINEAR_DROP2_CMUL;MLINEAR_ID;MLINEAR_COMPOSE_CMUL]);;
  
let HAS_MATRIX_DERIVATIVE_DROP2_MUL_AT = prove
    (`!f:real^N^M->real^1^1 g:real^N^M->real^S^Q f' g' x:real^N^M.
    (f has_matrix_derivative f') (matrix_at x) /\ 
    (g has_matrix_derivative g') (matrix_at x) 
        ==> ((\t:real^N^M. (drop_drop(f(t)) %% g(t))) has_matrix_derivative 
            (\h:real^N^M. drop_drop(f(x)) %% g'(h) + drop_drop(f'(h)) %% g(x))) (matrix_at x)`,
    ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN REWRITE_TAC[HAS_MATRIX_DERIVATIVE_DROP2_MUL_WITHIN]);;
    
let HAS_M_DERIVATIVE_DROP2_MUL_WITHIN = prove
    (`!f:real^1^1->real^1^1 g:real^1^1->real^S^Q f' g' x:real^1^1 s.
    (f has_m_derivative f' x) (matrix_at x within s) /\ 
    (g has_m_derivative g' x) (matrix_at x within s) 
        ==> ((\t. (drop_drop(f(t)) %% g(t))) has_m_derivative 
            (drop_drop(f(x)) %% g'(x) + drop_drop(f'(x)) %% g(x))) (matrix_at x within s)`,
    REPEAT GEN_TAC THEN 
    MATCH_MP_TAC (REWRITE_RULE [TAUT `a /\ b /\ c ==> d <=> c ==> (a /\ b) ==> d`] HAS_M_DERIVATIVE_BILINEAR_WITHIN) THEN
    SIMP_TAC[bimlinear;MLINEAR_DROP2_CMUL;MLINEAR_ID;MLINEAR_COMPOSE_CMUL]);;
    
let HAS_M_DERIVATIVE_DROP2_MUL_AT = prove
    (`!f:real^1^1->real^1^1 g:real^1^1->real^S^Q f' g' x:real^1^1.
    (f has_m_derivative f' x) (matrix_at x) /\ 
    (g has_m_derivative g' x) (matrix_at x) 
        ==> ((\t. (drop_drop(f(t)) %% g(t))) has_m_derivative 
            (drop_drop(f(x)) %% g'(x) + drop_drop(f'(x)) %% g(x))) (matrix_at x)`,
    ONCE_REWRITE_TAC[GSYM MATRIX_WITHIN_UNIV] THEN REWRITE_TAC[HAS_M_DERIVATIVE_DROP2_MUL_WITHIN]);;
    
let HAS_M_DERIVATIVE_MMUL_WITHIN = prove
    (`!f:real^1^1->real g:real^1^1->real^S^Q f' g' x:real^1^1 s.
    ((\x. lift_lift(f(x))) has_m_derivative lift_lift(f' x)) (matrix_at x within s) /\ 
    (g has_m_derivative g' x) (matrix_at x within s) 
        ==> ((\t. (f(t) %% g(t))) has_m_derivative 
            (f(x) %% g'(x) + f'(x) %% g(x))) (matrix_at x within s)`,
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPECL [`(\x. lift_lift((f:real^1^1->real)(x)))`;`g:real^1^1->real^S^Q`;`(\x. lift_lift((f':real^1^1->real)(x)))`;`g':real^1^1->real^S^Q`;`x:real^1^1`;`s:real^1^1->bool`] HAS_M_DERIVATIVE_DROP2_MUL_WITHIN) THEN
    ASM_SIMP_TAC[LIFT2_DROP]);;
    
let HAS_M_DERIVATIVE_MMUL_AT = prove
    (`!f:real^1^1->real g:real^1^1->real^S^Q f' g' x:real^1^1.
    ((\x. lift_lift(f(x))) has_m_derivative lift_lift(f' x)) (matrix_at x) /\ 
    (g has_m_derivative g' x) (matrix_at x) 
        ==> ((\t. (f(t) %% g(t))) has_m_derivative 
            (f(x) %% g'(x) + f'(x) %% g(x))) (matrix_at x)`,
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPECL [`(\x. lift_lift((f:real^1^1->real)(x)))`;`g:real^1^1->real^S^Q`;`(\x. lift_lift((f':real^1^1->real)(x)))`;`g':real^1^1->real^S^Q`;`x:real^1^1`] HAS_M_DERIVATIVE_DROP2_MUL_AT) THEN
    ASM_SIMP_TAC[LIFT2_DROP]);;
    
let HAS_M_DERIVATIVE_LIFT2_PRODUCT_AT = prove
    (`!f:real^1^1->num->real f' x n.
     (!i. 1 <= i /\ i <= n ==> ((\x. lift_lift(f x i)) has_m_derivative lift_lift(f' x i)) (matrix_at x))
    ==> ((\t. lift_lift(product (1..n) (f t))) has_m_derivative (lift_lift(sum (1..n) (\i. (f' x i) * product ((1..n) DELETE i) (f x))))) (matrix_at x)`,
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    INDUCT_TAC THENL
    [SIMP_TAC[PRODUCT_CLAUSES_NUMSEG;ARITH_EQ;SUM_CLAUSES_NUMSEG;LIFT2_NUM;HAS_M_DERIVATIVE_CONST]; ALL_TAC] THEN    
    REPEAT STRIP_TAC THEN 
    SIMP_TAC[PRODUCT_CLAUSES_NUMSEG;SUM_CLAUSES_NUMSEG;ARITH_RULE `1 <= SUC n`] THEN
    ONCE_SIMP_TAC[REAL_ARITH `(a:real) * (f t (SUC n)) = (f t (SUC n)) * a`] THEN
    SUBGOAL_THEN `sum (1..n) (\i. (f':real^1^1->num->real) x i * product ((1..SUC n) DELETE i) ((f:real^1^1->num->real) x)) =
                    sum (1..n) (\i. f' x i * product ((SUC n) INSERT ((1..n) DELETE i)) (f x))` SUBST1_TAC THENL
    [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
     REPEAT STRIP_TAC THEN SIMP_TAC[] THEN
     AP_TERM_TAC THEN
     SUBGOAL_THEN `(1..SUC n) DELETE i = (SUC n) INSERT ((1..n) DELETE i)` SUBST1_TAC THENL 
     [SIMP_TAC[EXTENSION;INSERT;DELETE;IN_ELIM_THM;IN_NUMSEG] THEN
      SIMP_TAC[ARITH_RULE `x <= SUC n <=> x <= n \/ x = SUC n`] THEN
      ASM_ARITH_TAC;ALL_TAC] THEN
     SIMP_TAC[];ALL_TAC] THEN
    SUBGOAL_THEN `(1..SUC n) DELETE SUC n = (1..n)` SUBST1_TAC THENL
    [SIMP_TAC[EXTENSION;DELETE;IN_ELIM_THM;IN_NUMSEG] THEN ARITH_TAC;ALL_TAC] THEN
    SIMP_TAC[FINITE_NUMSEG;FINITE_DELETE;PRODUCT_CLAUSES;IN_DELETE;IN_NUMSEG;ARITH_RULE `~(SUC n <= n)`] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * b * c = b * a * c`] THEN
    SIMP_TAC[SUM_LMUL;LIFT2_ADD;LIFT2_CMUL] THEN
    MATCH_MP_TAC HAS_M_DERIVATIVE_MMUL_AT THEN
    CONJ_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
     SIMP_TAC[ARITH_RULE `1 <= SUC n`;LE_REFL];ALL_TAC] THEN
     SUBGOAL_THEN `(!i. 1 <= i /\ i <= n ==> ((\x. lift_lift((f:real^1^1->num->real) x i)) has_m_derivative lift_lift(f' x i)) (matrix_at x))` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `i:num`) THEN
      ASM_SIMP_TAC[ARITH_RULE `i <= n ==> i <= SUC n`];ALL_TAC] THEN
     ASM_SIMP_TAC[]);;

let SUM_SWAP_NUMSEG_PERMUTATIONS = prove
    (`!a b c d f.
     sum(a..b) (\i. sum {p | p permutes (c..d)} (f i)) = sum {p | p permutes (c..d)} (\j. sum(a..b) (\i. f i j))`,
    REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_SWAP THEN
    SIMP_TAC[FINITE_NUMSEG;FINITE_PERMUTATIONS]);;  
  
let TRACE_TRANSP_MUL = prove
    (`!A B:real^N^M. trace(transp A ** B) = sum (1..dimindex(:N)) (\j. sum (1..dimindex(:M)) (\i. A$i$j * B$i$j))`,
    SIMP_TAC[trace;matrix_mul;LAMBDA_BETA;TRANSP_COMPONENT]);;
    
let PRODUCT_DIFF = prove
    (`!s t f. FINITE s /\ t SUBSET s ==> product(s DIFF t) f * product t f = product s f`,
    SIMP_TAC[product; ITERATE_DIFF; MONOIDAL_REAL_MUL]);;

let PRODUCT_RESTRICT_SET = prove 
    (`!P s f. product {x | x IN s /\ P x} f = product s (\x. if P x then f x else &1)`,
    SIMP_TAC[product;MONOIDAL_REAL_MUL;ITERATE_RESTRICT_SET;GSYM NEUTRAL_REAL_MUL]);;

(* ------------------------------------------------------------------------- *)
(* Jacobi's formula, corollary and applications                              *)
(* ------------------------------------------------------------------------- *)
    
let HAS_M_DERIVATIVE_DET = prove
    (`!f:real^1^1->real^N^N z:real^1^1 f'. 
     (f has_m_derivative f'(z)) (matrix_at z) ==>  
    ((\z. lift_lift(det(f(z)))) has_m_derivative lift_lift(trace(transp(cofactor(f(z))) ** f'(z)))) (matrix_at z)`,
    REPEAT STRIP_TAC THEN
    SIMP_TAC[TRACE_TRANSP_MUL;COFACTOR_COLUMN] THEN
    SUBGOAL_THEN `
    sum (1..dimindex (:N))
    (\j. sum (1..dimindex (:N))
        (\i. ((lambda i j.
                 det
                 ((lambda k l.
                      if l = j then if k = i then &1 else &0 else ((f:real^1^1->real^N^N) z)$k$l):real^N^N)):real^N^N)$i$j *
            ((f':real^1^1->real^N^N) z)$i$j)) = 
            sum (1..dimindex (:N))
    (\j. sum (1..dimindex (:N))
        (\i. det ((lambda k l.
                      if l = j then if k = i then &1 else &0 else (f z)$k$l):real^N^N) *
            (f' z)$i$j))` SUBST1_TAC THENL
    [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
     REPEAT STRIP_TAC THEN SIMP_TAC[] THEN
     MATCH_MP_TAC SUM_EQ_NUMSEG THEN
     ASM_SIMP_TAC[LAMBDA_BETA];ALL_TAC] THEN
    REWRITE_TAC[det;GSYM SUM_RMUL;SUM_SWAP_NUMSEG_PERMUTATIONS] THEN
    SIMP_TAC[LIFT2_SUM;o_DEF] THEN
    MATCH_MP_TAC HAS_M_DERIVATIVE_MSUM_AT THEN
    SIMP_TAC[FINITE_NUMSEG;FINITE_PERMUTATIONS] THEN
    X_GEN_TAC `p:num->num` THEN SIMP_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `msum (1..dimindex (:N))
    (\x. msum (1..dimindex (:N))
       (\x'. lift_lift((sign p *
               product (1..dimindex (:N))
               (\i'. ((lambda k l.
                          if l = x
                          then if k = x' then &1 else &0
                          else ((f:real^1^1->real^N^N) z)$k$l):real^N^N)$i'$p i')) *
              ((f':real^1^1->real^N^N) z)$x'$x))) =
              msum (1..dimindex (:N))
    (\x. msum (1..dimindex (:N))
       (\x'. lift_lift((sign p *
               product (1..dimindex (:N))
               (\i'. (if p i' = x
                          then if i' = x' then &1 else &0
                          else ((f:real^1^1->real^N^N) z)$i'$p i'))) *
              ((f':real^1^1->real^N^N) z)$x'$x)))` SUBST1_TAC THENL
    [MATCH_MP_TAC MSUM_EQ THEN REPEAT STRIP_TAC THEN SIMP_TAC[] THEN 
     MATCH_MP_TAC MSUM_EQ THEN REPEAT STRIP_TAC THEN SIMP_TAC[LIFT2_EQ] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
     ASM_SIMP_TAC[LAMBDA_BETA_PERM;LAMBDA_BETA];ALL_TAC] THEN
    SUBGOAL_THEN `msum (1..dimindex (:N))
    (\x. msum (1..dimindex (:N))
       (\x'. lift_lift((sign p *
               product (1..dimindex (:N))
               (\i'. (if p i' = x
                          then if i' = x' then &1 else &0
                          else ((f:real^1^1->real^N^N) z)$i'$p i'))) *
              ((f':real^1^1->real^N^N) z)$x'$x))) =               
        msum (1..dimindex (:N)) (\i.
        lift_lift((sign p *
        product ((1..dimindex (:N)) DIFF {k | inverse p i = k}) (\i'. f z$i'$p i')) *
        f' z$(inverse p i)$i))` SUBST1_TAC THENL 
    [MATCH_MP_TAC MSUM_EQ THEN
     X_GEN_TAC `i:num` THEN SIMP_TAC[IN_NUMSEG] THEN
     STRIP_TAC THEN
     SUBGOAL_THEN `msum (1..dimindex (:N))
     (\x'. lift_lift
       ((sign p *
         product (1..dimindex (:N))
               (\i'. (if p i' = i
                          then if i' = x' then &1 else &0
                          else ((f:real^1^1->real^N^N) z)$i'$p i'))) *
         ((f':real^1^1->real^N^N) z)$x'$i)) =
         msum (1..dimindex (:N))
        (\x'. lift_lift
       ((sign p *
         product ((1..dimindex (:N)) DIFF {k| ((p:num->num) k) = i}) 
                (\i'. (if p i' = i
                          then if i' = x' then &1 else &0
                          else ((f:real^1^1->real^N^N) z)$i'$p i')) * 
                product {k| ((p:num->num) k) = i} (\i'. (if p i' = i
                          then if i' = x' then &1 else &0
                          else ((f:real^1^1->real^N^N) z)$i'$p i'))) *
         f' z$x'$i))` SUBST1_TAC THENL
     [MATCH_MP_TAC MSUM_EQ THEN SIMP_TAC[IN_NUMSEG;LIFT2_EQ] THEN
      REPEAT STRIP_TAC THEN AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC PRODUCT_DIFF THEN
      SIMP_TAC[FINITE_NUMSEG;SUBSET;IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC (GSYM (ISPECL [`p:num->num`;`(1..dimindex(:N))`;`x':num`] PERMUTES_IN_IMAGE)) THEN
      ASM_SIMP_TAC[IN_NUMSEG];ALL_TAC] THEN
     SUBGOAL_THEN `msum (1..dimindex (:N))
     (\x'. lift_lift
       ((sign p *
         product ((1..dimindex (:N)) DIFF {k| ((p:num->num) k) = i}) 
                (\i'. (if p i' = i
                          then if i' = x' then &1 else &0
                          else ((f:real^1^1->real^N^N) z)$i'$p i')) * 
                product {k| ((p:num->num) k) = i} (\i'. (if p i' = i
                          then if i' = x' then &1 else &0
                          else ((f:real^1^1->real^N^N) z)$i'$p i'))) *
          ((f':real^1^1->real^N^N) z)$x'$i)) =
         msum (1..dimindex (:N))
     (\x'. lift_lift
       ((sign p *
         product ((1..dimindex (:N)) DIFF {k| ((p:num->num) k) = i}) 
                (\i'. ((f:real^1^1->real^N^N) z)$i'$p i') * 
                product {k| ((p:num->num) k) = i} (\i'. (if i' = x' then &1 else &0))) *
         f' z$x'$i))` SUBST1_TAC THENL
     [MATCH_MP_TAC MSUM_EQ THEN
      SIMP_TAC[IN_NUMSEG;LIFT2_EQ] THEN X_GEN_TAC `j:num` THEN
      REPEAT STRIP_TAC THEN AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
      MATCH_MP_TAC (MESON [] `(a:real) = c /\ b = d ==> a * b = c * d`) THEN
      CONJ_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
      SIMP_TAC[DIFF;IN_ELIM_THM;IN_NUMSEG];ALL_TAC] THEN
     SUBGOAL_THEN `msum (1..dimindex (:N))
     (\x'. lift_lift
       ((sign p *
         product ((1..dimindex (:N)) DIFF {k| ((p:num->num) k) = i}) 
                (\i'. ((f:real^1^1->real^N^N) z)$i'$p i') * 
                product {k| ((p:num->num) k) = i} (\i'. (if i' = x' then &1 else &0))) *
         ((f':real^1^1->real^N^N) z)$x'$i)) =
     msum (1..dimindex (:N))
     (\x'. lift_lift
       ((sign p *
         product ((1..dimindex (:N)) DIFF {k| ((p:num->num) k) = i}) 
                (\i'. ((f:real^1^1->real^N^N) z)$i'$p i') * 
                (if p x' = i then &1 else &0)) *
         f' z$x'$i))` SUBST1_TAC THENL
     [MATCH_MP_TAC MSUM_EQ THEN
      SIMP_TAC[IN_NUMSEG;LIFT2_EQ] THEN X_GEN_TAC `j:num` THEN
      REPEAT STRIP_TAC THEN AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
      SUBGOAL_THEN `FINITE {i' | i' IN {k | (p:num->num) k = i} /\ ~(i' = j)}` ASSUME_TAC THENL
      [MATCH_MP_TAC FINITE_RESTRICT THEN SIMP_TAC[GSYM IN_SING] THEN
       MATCH_MP_TAC FINITE_IMAGE_INJ THEN SIMP_TAC[FINITE_SING] THEN
       FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [permutes]) THEN
       ASM_MESON_TAC[];ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM COND_SWAP] THEN
      SIMP_TAC[GSYM PRODUCT_RESTRICT_SET] THEN
      COND_CASES_TAC THENL
      [MATCH_MP_TAC PRODUCT_EQ_1;ASM_SIMP_TAC[PRODUCT_EQ_0]] THEN
      SIMP_TAC[IN_ELIM_THM] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [permutes]) THEN
      ASM_MESON_TAC[];ALL_TAC] THEN
      SIMP_TAC[COND_RMUL_0;COND_LMUL_0;REAL_MUL_RID;REAL_MUL_LID] THEN
      SIMP_TAC[COND_RAND;LIFT2_NUM;GSYM MSUM_RESTRICT_SET] THEN 
      MP_TAC (GSYM (ISPECL [`p:num->num`;`(1..dimindex(:N))`] PERMUTES_INVERSE_EQ)) THEN 
      ASM_SIMP_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `{x' | x' IN 1..dimindex (:N) /\ inverse (p:num->num) i = x'} = {inverse p i}` SUBST1_TAC THENL
      [SIMP_TAC[EXTENSION;IN_ELIM_THM;IN_SING;IN_NUMSEG] THEN
       GEN_TAC THEN EQ_TAC THENL
      [SIMP_TAC[EQ_SYM_EQ];
       SIMP_TAC[] THEN STRIP_TAC THEN
       MATCH_MP_TAC PERMUTES_IN_NUMSEG THEN
       ASM_SIMP_TAC[IN_NUMSEG;PERMUTES_INVERSE]];ALL_TAC] THEN
      SIMP_TAC[MSUM_SING];ALL_TAC] THEN
    SIMP_TAC[GSYM REAL_MUL_ASSOC] THEN
    ONCE_SIMP_TAC[LIFT2_CMUL] THEN
    SIMP_TAC[MSUM_LMUL] THEN
    MATCH_MP_TAC HAS_M_DERIVATIVE_CMUL THEN
    MP_TAC(ISPECL [`(\z i. ((f:real^1^1->real^N^N) z)$i$p i)`;`(\z i. ((f':real^1^1->real^N^N) z)$i$p i)`;`z:real^1^1`;`dimindex(:N)`] HAS_M_DERIVATIVE_LIFT2_PRODUCT_AT) THEN
    ANTS_TAC THENL 
    [REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_m_derivative]) THEN
     ONCE_SIMP_TAC[HAS_MATRIX_DERIVATIVE_COMPONENTWISE_AT] THEN
     SIMP_TAC[MATRIX_CMUL_COMPONENT;LIFT2_CMUL;GSYM has_m_derivative] THEN
     DISCH_THEN(MP_TAC o SPECL [`i:num`;`(p:num->num) i`]) THEN
     ASM_SIMP_TAC[] THEN
     ANTS_TAC THENL [MATCH_MP_TAC PERMUTES_IN_NUMSEG THEN ASM_SIMP_TAC[IN_NUMSEG];ALL_TAC] THEN
     SIMP_TAC[];ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    SIMP_TAC[GSYM LIFT2_SUM] THEN SIMP_TAC[o_DEF] THEN
    SUBGOAL_THEN ` sum (1..dimindex (:N))
      (\i. 
           (product ((1..dimindex (:N)) DIFF {k | inverse (p:num->num) i = k})
            (\i'. ((f:real^1^1->real^N^N) z)$i'$p i') *
            ((f':real^1^1->real^N^N) z)$inverse p i$i)) =
            sum (1..dimindex (:N))
    (\x. 
       (f' z$x$p x * product ((1..dimindex (:N)) DELETE x) (\i. f z$i$p i)))` SUBST1_TAC THENL
    [MP_TAC (ISPECL [`(\i. 
           (product ((1..dimindex (:N)) DIFF {k | inverse (p:num->num) i = k})
            (\i'. ((f:real^1^1->real^N^N) z)$i'$p i') *
            ((f':real^1^1->real^N^N) z)$inverse p i$i))`;`(p:num->num)`;`(1..dimindex(:N))`] SUM_PERMUTE) THEN
     ASM_SIMP_TAC[o_DEF] THEN STRIP_TAC THEN
     MATCH_MP_TAC SUM_EQ_NUMSEG THEN
     MP_TAC (ISPECL [`p:num->num`;`(1..dimindex(:N))`] PERMUTES_INVERSES) THEN
     ASM_SIMP_TAC[SING_GSPEC] THEN REPEAT STRIP_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
     AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     SIMP_TAC[EXTENSION;DIFF;DELETE;IN_ELIM_THM;IN_SING];ALL_TAC] THEN 
    SIMP_TAC[]);;

let HAS_M_DERIVATIVE_DET_EXP = prove
    (`!A:real^N^N z:real^1^1. ((\z. lift_lift(det(matrix_exp(drop_drop z %% A)))) has_m_derivative lift_lift(trace(A) * det(matrix_exp(drop_drop z %% A)))) (matrix_at z)`,
     REPEAT GEN_TAC THEN
     MP_TAC (ISPECL [`(\z. matrix_exp(drop_drop z %% (A:real^N^N)))`;`z:real^1^1`;`(\z. A ** matrix_exp(drop_drop z %% (A:real^N^N)))`] HAS_M_DERIVATIVE_DET) THEN
     SIMP_TAC[HAS_M_DERIVATIVE_EXP] THEN
     SIMP_TAC[GSYM INVERTIBLE_DET_NZ;INVERTIBLE_MATRIX_EXP;COFACTOR_MATRIX_INV] THEN
     SIMP_TAC[TRANSP_MATRIX_CMUL;TRANSP_TRANSP;MATRIX_MUL_LMUL;TRACE_CMUL] THEN
     ONCE_REWRITE_TAC[TRACE_MUL_CYCLIC] THEN
     SIMP_TAC[MATRIX_INV;MATRIX_MUL_RID;INVERTIBLE_MATRIX_EXP;REAL_MUL_SYM]);;
    
let HAS_M_DERIVATIVE_DET_EXP_EQ_0 = prove
    (`!A:real^N^N z:real^1^1. trace(A) = &0 ==> ((\z. lift_lift(det(matrix_exp(drop_drop z %% A)))) has_m_derivative mat 0) (matrix_at z)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `mat 0 = lift_lift(trace(A:real^N^N) * det(matrix_exp(drop_drop z %% A)))` SUBST1_TAC THENL
    [ASM_SIMP_TAC[REAL_MUL_LZERO;LIFT2_NUM];ALL_TAC] THEN
    SIMP_TAC[HAS_M_DERIVATIVE_DET_EXP]);;

let HAS_REAL_MATRIX_DERIVATIVE_WITHIN = prove
    (`(f has_real_derivative f') (atreal x within s) <=>
        ((lift_lift o f o drop_drop) has_matrix_derivative (\x. f' %% x))
        (matrix_at (lift_lift x) within (IMAGE lift_lift s))`,
    REWRITE_TAC[has_matrix_derivative_within; HAS_REAL_DERIVATIVE_WITHINREAL] THEN
    REWRITE_TAC[o_THM; LIFT_DROP2; MATRIX_LIM_WITHIN; REALLIM_WITHINREAL] THEN
    SIMP_TAC[MLINEAR_COMPOSE_CMUL; MLINEAR_ID; IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; MATRIX_DIST_LIFT2; GSYM LIFT2_SUB; LIFT_DROP2;
        MATRIX_DIST_0; GSYM LIFT2_CMUL; GSYM LIFT2_ADD;FNORM_LIFT2] THEN
    SIMP_TAC[REAL_FIELD
    `&0 < abs(y - x)
    ==> fy - (fx + f' * (y - x)) = (y - x) * ((fy - fx) / (y - x) - f')`] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_ASSOC; REAL_ABS_INV; REAL_ABS_ABS] THEN
    SIMP_TAC[REAL_LT_IMP_NZ; REAL_MUL_LINV; REAL_MUL_LID]);;

let IMAGE_LIFT2_UNIV = prove
    (`IMAGE lift_lift (:real) = (:real^1^1)`,
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN MESON_TAC[LIFT_DROP2]);;
  
let HAS_REAL_MATRIX_DERIVATIVE_AT = prove
    (`(f has_real_derivative f') (atreal x) <=>
        ((lift_lift o f o drop_drop) has_matrix_derivative (\x. f' %% x))
        (matrix_at (lift_lift x))`,
    ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV; GSYM MATRIX_WITHIN_UNIV] THEN
    REWRITE_TAC[HAS_REAL_MATRIX_DERIVATIVE_WITHIN] THEN
    REWRITE_TAC[IMAGE_LIFT2_UNIV]);;
    
let HAS_REAL_M_DERIVATIVE_WITHIN = prove
    (`(f has_real_derivative f') (atreal x within s) <=>
        ((lift_lift o f o drop_drop) has_m_derivative (lift_lift f'))
        (matrix_at (lift_lift x) within (IMAGE lift_lift s))`,
    REWRITE_TAC[has_m_derivative; HAS_REAL_MATRIX_DERIVATIVE_WITHIN] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; FORALL_LIFT2; GSYM LIFT2_CMUL] THEN
    REWRITE_TAC[LIFT_DROP2; LIFT2_EQ; REAL_MUL_SYM]);;

let HAS_REAL_M_DERIVATIVE_AT = prove
    (`(f has_real_derivative f') (atreal x) <=>
        ((lift_lift o f o drop_drop) has_m_derivative (lift_lift f'))
        (matrix_at (lift_lift x))`,
    REWRITE_TAC[has_m_derivative; HAS_REAL_MATRIX_DERIVATIVE_AT] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; FORALL_LIFT2; GSYM LIFT2_CMUL] THEN
    REWRITE_TAC[LIFT_DROP2; LIFT2_EQ; REAL_MUL_SYM]);;

let TRACE_0_IMP_DET_EXP = prove
    (`!x:real^N^N t. trace(x) = &0 ==> det(matrix_exp(t %% x)) = &1`,
     SIMP_TAC[GSYM RIGHT_IMP_FORALL_THM] THEN
     GEN_TAC THEN STRIP_TAC THEN
     MATCH_MP_TAC (SIMP_RULE [IN_UNIV;IS_REALINTERVAL_UNIV] (ISPECL [`(\a. (det (matrix_exp (a %% A:real^N^N))))`;`(:real)`;`&1`;`&0`] HAS_REAL_DERIVATIVE_ZERO_UNIQUE)) THEN
     SIMP_TAC[MATRIX_CMUL_LZERO;MATRIX_EXP_0;DET_I;WITHINREAL_UNIV] THEN
     SIMP_TAC[HAS_REAL_M_DERIVATIVE_AT;o_DEF] THEN
     ASM_SIMP_TAC[LIFT2_NUM;HAS_M_DERIVATIVE_DET_EXP_EQ_0]);;

let SSM_IMP_DET_EXP_1 = prove
    (`!x:real^N^N t. transp x = -- x ==> det(matrix_exp(t %% x)) = &1`,
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[MESON [BETA_THM] `det(matrix_exp(t %% x)) = (\a. det (matrix_exp (a %% (x:real^N^N)))) t`] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_CONST_UNIQUE THEN
    EXISTS_TAC `--(&1)` THEN
    SIMP_TAC[DET_EXP_REAL_CONTINUOUS_AT] THEN
    SIMP_TAC[REAL_FIELD `a = &1 \/ a = -- &1 <=> a * a = &1`] THEN
    CONJ_TAC THENL
    [X_GEN_TAC `t:real` THEN 
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [GSYM DET_TRANSP] THEN
     ASM_SIMP_TAC[MATRIX_EXP_TRANSP;TRANSP_MATRIX_CMUL] THEN
     REWRITE_TAC[GSYM DET_MUL;MATRIX_CMUL_RNEG;GSYM MATRIX_EXP_INV] THEN
     SIMP_TAC[MATRIX_INV;INVERTIBLE_MATRIX_EXP;DET_I];
     EXISTS_TAC `&0` THEN
     SIMP_TAC[MATRIX_CMUL_LZERO;MATRIX_EXP_0;DET_I]]);;    

(* ------------------------------------------------------------------------- *)
(* related properties of the lie algebra of matrix lie group                 *)
(* ------------------------------------------------------------------------- *)

let IS_LIE_ALGEBRA_OF_GLG = prove
    (`!a:real^N^N. is_lie_algebra_of_mlg (group_mlg(general_linear_group a)) (lie_algebra_of_glg (group_mlg(general_linear_group a)))`,
    REWRITE_TAC[is_lie_algebra_of_mlg;LIE_ALGEBRA_OF_GLG;MLG_SET_EQ_GLG;GENERAL_LINEAR_GROUP;IN_ELIM_THM;IN_UNIV;INVERTIBLE_MATRIX_EXP]);;
    
let IS_LIE_ALGEBRA_OF_SLG = prove
    (`!a:real^N^N. is_lie_algebra_of_mlg (group_mlg(special_linear_group a)) (lie_algebra_of_slg (group_mlg(special_linear_group a)))`,
    REWRITE_TAC[is_lie_algebra_of_mlg;MLG_SET_EQ_SLG;LIE_ALGEBRA_OF_SLG;SPECIAL_LINEAR_GROUP;IN_ELIM_THM;IN_UNIV] THEN
    SIMP_TAC[INVERTIBLE_MATRIX_EXP;TRACE_0_IMP_DET_EXP]);;

let IS_LIE_ALGEBRA_OF_OG = prove
    (`!a:real^N^N. is_lie_algebra_of_mlg (group_mlg(orthogonal_group a)) (lie_algebra_of_og (group_mlg(orthogonal_group a)))`,
    REWRITE_TAC[is_lie_algebra_of_mlg;LIE_ALGEBRA_OF_OG;MLG_SET_EQ_OG;ORTHOGONAL_GROUP;IN_ELIM_THM;IN_UNIV] THEN
    SIMP_TAC[ORTHOGONAL_MATRIX_EQ;INVERTIBLE_MATRIX_EXP;TRANSP_TRANS_EXP;MATRIX_EXP_INV;CMATRIX_ARITH `!x:real^N^M t. --(t %% x) = t %% (--x)`]);;
     
let IS_LIE_ALGEBRA_OF_SOG = prove
    (`!a:real^N^N. is_lie_algebra_of_mlg (group_mlg(rotation_group a)) (lie_algebra_of_sog (group_mlg(rotation_group a)))`,
    REWRITE_TAC[is_lie_algebra_of_mlg;LIE_ALGEBRA_OF_SOG;MLG_SET_EQ_SOG;ROTATION_GROUP;IN_ELIM_THM;IN_UNIV] THEN
    SIMP_TAC[ORTHOGONAL_MATRIX_EQ;INVERTIBLE_MATRIX_EXP;TRANSP_TRANS_EXP;MATRIX_EXP_INV;MATRIX_CMUL_LNEG;MATRIX_CMUL_RNEG;SSM_IMP_DET_EXP_1]);;
