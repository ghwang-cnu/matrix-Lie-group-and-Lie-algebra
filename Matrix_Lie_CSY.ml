(*needs "Multivariate/topology.ml";;*)
needs "CNU/matrixanalysis.ml";;
needs "Multivariate/realanalysis.ml";;
needs "CNU/det_continuous.ml";;
needs "Library/grouptheory.ml";;

(*topology manifold*)
(*
let local_homeomorphic_maps = new_definition
 `local_homeomorphic_maps(top,top') (f:A->B,g) <=>
        (!x. x IN topspace top ==>
        (?u. x IN u /\ (open_in top u) /\
        homeomorphic_maps(subtopology top u, subtopology top' (IMAGE f u)) (f,g)))`;;

let countable_hausdorff = new_definition 
    `countable_hausdorff (M:A topology) <=>
     ?B. hausdorff_space M /\ COUNTABLE (B) /\ (open_in M = ARBITRARY UNION_OF B)`;;
     
let topology_manifold = new_definition 
  `topology_manifold (f:A->real^N,g:real^N->A) (M:A topology) <=>  
   countable_hausdorff M /\ local_homeomorphic_maps (M,euclidean) (f,g)`;;
 
let frechet_derivative_at2 = new_definition
  `frechet_derivative_at2 f x = @f'. (f has_derivative (\x. f')) (at x)`;;
  
let higher_derivative = define
 `(higher_derivative 0 f = f) /\
  (!n. higher_derivative (SUC n) f =
                frechet_derivative_at2 (higher_derivative n f))`;;

let frechet_derivative_at_x = new_definition                
    `!x:real^N. frechet_derivative_at_x f x = (jacobian f (at x)) ** x`;;
    
let higher_derivative_test = define
 `(higher_derivative_test 0 f = f) /\
  (!n. higher_derivative_test (SUC n) f =
                frechet_derivative_at_x (higher_derivative_test n f))`;;
*)

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

let general_linear_group = new_definition
    `general_linear_group (a:real^N^N) = group ({A:real^N^N | invertible A}, mat 1:real^N^N, matrix_inv, matrix_mul)`;;

let GENERAL_LINEAR_GROUP = prove
    (`(!a:real^N^N. group_carrier(general_linear_group a) = {A:real^N^N | invertible A})    /\
    (!a:real^N^N. group_id(general_linear_group a) = mat 1:real^N^N) /\
    (!a:real^N^N. group_inv(general_linear_group a) = matrix_inv) /\
    (!a:real^N^N. group_mul(general_linear_group a) = matrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl general_linear_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM general_linear_group] THEN SIMP_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[INVERTIBLE_I;INVERTIBLE_MATRIX_INV;
             MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RID;MATRIX_INV;
             INVERTIBLE_MATRIX_MUL] THEN
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);; 
    
let GENERAL_LINEAR_OPEN_IN_MATRIX_SPACE = prove
    (`!g:real^N^N. open_in matrix_space (group_carrier (general_linear_group g))`,
    GEN_TAC THEN 
    REWRITE_TAC[GSYM MATRIX_OPEN_IN;GENERAL_LINEAR_GROUP] THEN 
    REWRITE_TAC [SET_RULE `{A | invertible A} = (:real^N^N) DIFF {A | ~(invertible A)}`;GSYM matrix_closed] THEN
    REWRITE_TAC[GSYM DET_EQ_0;MATRIX_CLOSED_DET_CONSTANT]);;

(* ------------------------------------------------------------------------- *)
(* topological group                                                         *)
(* ------------------------------------------------------------------------- *)  

let HAUSDORFF_SPACE_MATRIX_SPACE = prove
 (`hausdorff_space matrix_space`,
  REWRITE_TAC[GSYM MTOPOLOGY_MATRIX_SPACE_METRIC; HAUSDORFF_SPACE_MTOPOLOGY]);;
  
let HAUSDORFF_SPACE_GLG = prove
    (`!a:real^N^N. hausdorff_space (subtopology matrix_space (group_carrier (general_linear_group a)))`,
    SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY;HAUSDORFF_SPACE_MATRIX_SPACE]);;

(* ------------------------------------------------------------------------- *)
(* matrix lie group                                                          *)
(* ------------------------------------------------------------------------- *)

let ismlg = define
    `ismlg (s:real^N^N->bool) <=>
        s subgroup_of (group ({A:real^N^N | invertible A}, mat 1:real^N^N, matrix_inv, matrix_mul))/\
        (!x:num->real^N^N l:real^N^N. (!n. x(n) IN s) /\ (x ->-> l) sequentially ==> (l IN s \/ ~(invertible l)))`;;

let mlg_tybij_th = prove
    (`?t:real^N^N->bool. ismlg t`,
    EXISTS_TAC `{A:real^N^N | invertible A}` THEN SIMP_TAC[ismlg] THEN CONJ_TAC THENL [SIMP_TAC[GSYM GENERAL_LINEAR_GROUP;CARRIER_SUBGROUP_OF;GSYM general_linear_group];
    SET_TAC[]]);;

let mlg_tybij =
    new_type_definition "mlg" ("mlg","mlg_set") mlg_tybij_th;;
  
let mlg_group = new_definition
    `(mlg_group:(N)mlg-> (real^N^N)group) G = group (mlg_set G, mat 1:real^N^N, matrix_inv, matrix_mul)`;;
    
let group_mlg = new_definition
    `(group_mlg:(real^N^N)group->(N)mlg) G = mlg(group_carrier G)`;;
    
let ISMLG_MLG_SET = prove
    (`!G:(N)mlg. ismlg(mlg_set G)`,
    MESON_TAC[mlg_tybij]);;

let MLG_SUBGROUP_OF_GLG = prove  
    (`!G:(N)mlg a:real^N^N. (mlg_set G) subgroup_of (general_linear_group a)`,
    MESON_TAC[ISMLG_MLG_SET;ismlg;general_linear_group]);;
    
let MLG_GROUP = prove
    (`(!G:(N)mlg. group_carrier(mlg_group G) = mlg_set G) /\
    (!G:(N)mlg. group_id(mlg_group G) = mat 1:real^N^N) /\
    (!G:(N)mlg. group_inv(mlg_group G) = matrix_inv) /\
    (!G:(N)mlg. group_mul(mlg_group G) = matrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl mlg_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM mlg_group] THEN
    SIMP_TAC[SIMP_RULE [subgroup_of;GENERAL_LINEAR_GROUP] MLG_SUBGROUP_OF_GLG;MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RID] THEN
    ANTS_TAC THENL [MESON_TAC[SIMP_RULE [subgroup_of;GENERAL_LINEAR_GROUP;SUBSET] MLG_SUBGROUP_OF_GLG;MATRIX_INV;IN_ELIM_THM];SIMP_TAC[group_carrier; group_id; group_inv; group_mul]]);;
    
let MLG_GROUP_BIJ = prove
    (`(!G. group_mlg(mlg_group G) = G) /\
    (!G:(real^N^N)group. ismlg(group_carrier G) /\ group_id G = mat 1 /\ group_inv G = matrix_inv /\ group_mul G = matrix_mul <=> mlg_group(group_mlg G) = G)`,
    SIMP_TAC[GROUPS_EQ;MLG_GROUP;group_mlg;mlg_tybij] THEN
    SIMP_TAC[EQ_SYM_EQ]);;

let GENERAL_LINEAR_GROUP_ISMLG = prove
    (`!g. ismlg (group_carrier (general_linear_group g))`,
    GEN_TAC THEN SIMP_TAC[ismlg;general_linear_group;CARRIER_SUBGROUP_OF] THEN
    SIMP_TAC[GSYM general_linear_group;GENERAL_LINEAR_GROUP] THEN SET_TAC[]);;

let MLG_GROUP_EQ_GLG = prove
    (`!G:(N)mlg a:real^N^N. 
      (mlg_set G = group_carrier (general_linear_group a)) <=>
      mlg_group G = (general_linear_group a)`,
    REWRITE_TAC[GROUPS_EQ;GENERAL_LINEAR_GROUP;MLG_GROUP]);; 
    
let MLG_SET_EQ_GLG = prove
    (`!a:real^N^N. mlg_set (group_mlg(general_linear_group a)) = group_carrier (general_linear_group a)`,
    SIMP_TAC[GENERAL_LINEAR_GROUP_ISMLG;GSYM mlg_tybij;group_mlg]);;
    
let MLG_INJ_GLG = prove
    (`(!a:real^N^N. mlg_group(group_mlg (general_linear_group a)) = general_linear_group a)`,
    SIMP_TAC[GSYM MLG_GROUP_BIJ;GENERAL_LINEAR_GROUP_ISMLG;GENERAL_LINEAR_GROUP]);;
   
(* ------------------------------------------------------------------------- *)
(* special linear group                                                      *)
(* ------------------------------------------------------------------------- *)

let special_linear_group = new_definition
    `special_linear_group (a:real^N^N) = group ({A:real^N^N | invertible A /\ det(A) = &1}, mat 1:real^N^N, matrix_inv, matrix_mul)`;;
 
let SPECIAL_LINEAR_GROUP = prove
    (`(!a:real^N^N. group_carrier(special_linear_group a) = 
                 {A:real^N^N | invertible A /\ det(A) = &1}) /\
    (!a:real^N^N. group_id(special_linear_group a) = mat 1:real^N^N) /\
    (!a:real^N^N. group_inv(special_linear_group a) = matrix_inv) /\
    (!a:real^N^N. group_mul(special_linear_group a) = matrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl special_linear_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM special_linear_group] THEN SIMP_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[INVERTIBLE_I;DET_I;INVERTIBLE_MATRIX_INV;DET_MATRIX_INV;REAL_INV_1;
              MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RID;
              MATRIX_INV;DET_MUL;REAL_MUL_LID;INVERTIBLE_MATRIX_MUL] THEN
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);;  
 
let LINEAR_SPECIAL_SUBGROUP_OF_GENERAL = prove
    (`!g. (group_carrier (special_linear_group g)) subgroup_of (general_linear_group g)`,
    SIMP_TAC[subgroup_of;SPECIAL_LINEAR_GROUP;GENERAL_LINEAR_GROUP;
             SUBSET;IN_ELIM_THM;INVERTIBLE_I;DET_I;
             INVERTIBLE_MATRIX_INV;DET_MATRIX_INV;REAL_INV_1;
             DET_MUL;REAL_MUL_LID;INVERTIBLE_MATRIX_MUL]);;
    
let SPECIAL_LINEAR_GROUP_ISMLG = prove
    (`!g:real^N^N. ismlg (group_carrier (special_linear_group g))`,
    GEN_TAC THEN SIMP_TAC[ismlg;special_linear_group] THEN
    SIMP_TAC[GSYM general_linear_group;GSYM special_linear_group] THEN
    SIMP_TAC[LINEAR_SPECIAL_SUBGROUP_OF_GENERAL;SPECIAL_LINEAR_GROUP] THEN
    SIMP_TAC[INVERTIBLE_DET_NZ;REAL_ARITH `~(x = &0) /\ (x = &1) <=> (x = &1)`;IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC (SPEC `&1` MATRIX_CLOSED_DET_CONSTANT) THEN
    SIMP_TAC[MATRIX_CLOSED_SEQUENTIAL_LIMITS] THEN
    DISCH_THEN(MP_TAC o ISPECL [`x:num -> real^N^N`; `l:real^N^N`]) THEN
    ASM_SIMP_TAC[IN_ELIM_THM]);;
    
let MLG_GROUP_EQ_SLG = prove
    (`!G:(N)mlg a:real^N^N. 
      (mlg_set G = group_carrier (special_linear_group a)) <=>
      mlg_group G = (special_linear_group a)`,
    REWRITE_TAC[GROUPS_EQ;SPECIAL_LINEAR_GROUP;MLG_GROUP]);; 
    
let MLG_SET_EQ_SLG = prove
    (`!a:real^N^N. mlg_set (group_mlg (special_linear_group a)) = group_carrier (special_linear_group a)`,
    SIMP_TAC[SPECIAL_LINEAR_GROUP_ISMLG;GSYM mlg_tybij;group_mlg]);;
    
let MLG_INJ_SLG = prove
    (`(!a:real^N^N. mlg_group(group_mlg (special_linear_group a)) = special_linear_group a)`,
    SIMP_TAC[GSYM MLG_GROUP_BIJ;SPECIAL_LINEAR_GROUP_ISMLG;SPECIAL_LINEAR_GROUP]);;

(* ------------------------------------------------------------------------- *)
(* orthogonal group                                                          *)
(* ------------------------------------------------------------------------- *)

let orthogonal_group = new_definition
    `orthogonal_group (a:real^N^N) = group ({A:real^N^N | orthogonal_matrix A}, mat 1:real^N^N, matrix_inv, matrix_mul)`;; 

let ORTHOGONAL_GROUP = prove
    (`(!a:real^N^N. group_carrier(orthogonal_group a) = {A:real^N^N | orthogonal_matrix A}) /\
   (!a:real^N^N. group_id(orthogonal_group a) = mat 1:real^N^N) /\
   (!a:real^N^N. group_inv(orthogonal_group a) = matrix_inv) /\
   (!a:real^N^N. group_mul(orthogonal_group a) = matrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl orthogonal_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM orthogonal_group] THEN ANTS_TAC THENL
    [SIMP_TAC[IN_ELIM_THM] THEN
     SIMP_TAC[ORTHOGONAL_MATRIX_ID;ORTHOGONAL_MATRIX_INV_EQ;ORTHOGONAL_MATRIX_MUL;
              MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RID;
              ORTHOGONAL_MATRIX_IMP_INVERTIBLE;MATRIX_INV];ALL_TAC] THEN
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);;

let ORTHOGONAL_SUBGROUP_OF_GENERAL = prove
    (`!g. (group_carrier (orthogonal_group g)) subgroup_of (general_linear_group g)`,
    SIMP_TAC[subgroup_of;ORTHOGONAL_GROUP;GENERAL_LINEAR_GROUP;
             SUBSET;IN_ELIM_THM;ORTHOGONAL_MATRIX_ID;
             ORTHOGONAL_MATRIX_INV_EQ;ORTHOGONAL_MATRIX_MUL;
             ORTHOGONAL_MATRIX_IMP_INVERTIBLE]);;
             
let ORTHOGONAL_GROUP_ISMLG = prove
    (`!g:real^N^N. ismlg (group_carrier (orthogonal_group g))`,
    GEN_TAC THEN SIMP_TAC[ismlg;orthogonal_group] THEN
    SIMP_TAC[GSYM general_linear_group;GSYM orthogonal_group] THEN
    SIMP_TAC[ORTHOGONAL_SUBGROUP_OF_GENERAL;ORTHOGONAL_GROUP] THEN
    MESON_TAC[TAUT `(P ==> Q) ==> (P ==> (Q \/ R))`;
              MATRIX_CLOSED_ORTHOGONAL_MATRIX;MATRIX_CLOSED_SEQUENTIAL_LIMITS]);;
              
let MLG_GROUP_EQ_OG = prove
    (`!G:(N)mlg a:real^N^N. 
      (mlg_set G = group_carrier (orthogonal_group a)) <=>
      mlg_group G = (orthogonal_group a)`,
    REWRITE_TAC[GROUPS_EQ;ORTHOGONAL_GROUP;MLG_GROUP]);;
    
let MLG_SET_EQ_OG = prove
    (`!a:real^N^N. mlg_set (group_mlg (orthogonal_group a)) = group_carrier (orthogonal_group a)`,
    SIMP_TAC[ORTHOGONAL_GROUP_ISMLG;GSYM mlg_tybij;group_mlg]);;
    
let MLG_INJ_OG = prove
    (`(!a:real^N^N. mlg_group(group_mlg (orthogonal_group a)) = orthogonal_group a)`,
    SIMP_TAC[GSYM MLG_GROUP_BIJ;ORTHOGONAL_GROUP_ISMLG;ORTHOGONAL_GROUP]);;

(* ------------------------------------------------------------------------- *)
(* rotation group                                                            *)
(* ------------------------------------------------------------------------- *)
  
let rotation_group = new_definition
    `rotation_group   (a:real^N^N) = group ({A:real^N^N | orthogonal_matrix A /\ det(A) = &1},mat 1:real^N^N, matrix_inv, matrix_mul)`;; 
 
let ROTATION_GROUP = prove
    (`(!a:real^N^N. group_carrier(rotation_group a) = 
     {A:real^N^N | orthogonal_matrix A  /\ det(A) = &1}) /\
    (!a:real^N^N. group_id(rotation_group a) = mat 1:real^N^N) /\
    (!a:real^N^N. group_inv(rotation_group a) = matrix_inv) /\
    (!a:real^N^N. group_mul(rotation_group a) = matrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl rotation_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM rotation_group] THEN ANTS_TAC THENL
    [SIMP_TAC[IN_ELIM_THM] THEN
     SIMP_TAC[ORTHOGONAL_MATRIX_ID;DET_I;
              ORTHOGONAL_MATRIX_INV_EQ;DET_MATRIX_INV;REAL_INV_1;
              ORTHOGONAL_MATRIX_MUL;DET_MUL;REAL_MUL_LID;
              MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RID;
              ORTHOGONAL_MATRIX_IMP_INVERTIBLE;MATRIX_INV];ALL_TAC] THEN
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);;

let ROTATION_SUBGROUP_OF_GENERAL = prove
    (`!g. (group_carrier (rotation_group g)) subgroup_of (general_linear_group g)`,
    SIMP_TAC[subgroup_of;ROTATION_GROUP;GENERAL_LINEAR_GROUP;
             SUBSET;IN_ELIM_THM;ORTHOGONAL_MATRIX_ID;DET_I;
             ORTHOGONAL_MATRIX_INV_EQ;DET_MATRIX_INV;REAL_INV_1;
             ORTHOGONAL_MATRIX_MUL;DET_MUL;REAL_MUL_LID;
             ORTHOGONAL_MATRIX_IMP_INVERTIBLE]);;
             
let ROTATION_GROUP_ISMLG = prove
    (`!g:real^N^N. ismlg (group_carrier (rotation_group g))`,
    GEN_TAC THEN SIMP_TAC[ismlg;rotation_group] THEN
    SIMP_TAC[GSYM general_linear_group;GSYM rotation_group] THEN
    SIMP_TAC[ROTATION_SUBGROUP_OF_GENERAL;ROTATION_GROUP] THEN
    MP_TAC(REWRITE_RULE [INTER;IN_ELIM_THM] (ISPECL [`{A:real^N^N | orthogonal_matrix A}`;`{A:real^N^N | det A = &1}`] MATRIX_CLOSED_INTER)) THEN
    SIMP_TAC[MATRIX_CLOSED_ORTHOGONAL_MATRIX;MATRIX_CLOSED_DET_CONSTANT;MATRIX_CLOSED_SEQUENTIAL_LIMITS] THEN SET_TAC[]);;
    
let MLG_GROUP_EQ_SOG = prove
    (`!G:(N)mlg a:real^N^N. 
      (mlg_set G = group_carrier (rotation_group a)) <=>
      mlg_group G = (rotation_group a)`,
    REWRITE_TAC[GROUPS_EQ;ROTATION_GROUP;MLG_GROUP]);;
    
let MLG_SET_EQ_SOG = prove
    (`!a:real^N^N. mlg_set (group_mlg (rotation_group a)) = group_carrier (rotation_group a)`,
    SIMP_TAC[ROTATION_GROUP_ISMLG;GSYM mlg_tybij;group_mlg]);;
    
let MLG_INJ_SOG = prove
    (`(!a:real^N^N. mlg_group(group_mlg (rotation_group a)) = rotation_group a)`,
    SIMP_TAC[GSYM MLG_GROUP_BIJ;ROTATION_GROUP_ISMLG;ROTATION_GROUP]);;

(* ------------------------------------------------------------------------- *)
(* homogeneous transformation of matrix                                      *)
(* ------------------------------------------------------------------------- *)
    
let homo_trans = new_definition
    `(homo_trans:real^N->real^N^N->real^(N,1)finite_sum^(N,1)finite_sum) x R = 
     (lambda i j. if i = (dimindex(:N) + 1) /\ ~(j = dimindex(:N) + 1) then &0
                 else if i = (dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then &1
                      else if ~(i = dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then x$i
                           else R$i$j)`;;

let point_tybij = new_type_definition "point" ("mk_point","dest_point") 
    (prove(`?x:real^N. T`,REWRITE_TAC[]));;
                           
let homo_point = new_definition
    `(homo_point:(N)point->real^(N,1)finite_sum) x = 
     (lambda i. if i = (dimindex(:N) + 1) then &1
                 else (dest_point x)$i )`;;

let HOMO_TRANS_COMPONENT = prove
    (`!x:real^N R:real^N^N i j.
        1 <= i /\ i <= dimindex(:N) + 1 /\
        1 <= j /\ j <= dimindex(:N) + 1 ==>
        (homo_trans x R)$i$j = 
        (if i = (dimindex(:N) + 1) /\ ~(j = dimindex(:N) + 1) then &0
                 else if i = (dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then &1
                      else if ~(i = dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then x$i
                           else R$i$j)`,
     SIMP_TAC[homo_trans;LAMBDA_BETA;DIMINDEX_FINITE_SUM;DIMINDEX_1]);;

let HOMO_TRANS_EQ_MAT = prove                           
    (`homo_trans ((vec 0):real^N) (mat 1) = mat 1`,
    SIMP_TAC[homo_trans;CART_EQ;LAMBDA_BETA;VEC_COMPONENT;MAT_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[];ALL_TAC] THEN
    UNDISCH_TAC `~(~(i = dimindex (:N) + 1) /\ i' = dimindex (:N) + 1)` THEN
    UNDISCH_TAC `~(i = dimindex (:N) + 1 /\ i' = dimindex (:N) + 1)` THEN
    UNDISCH_TAC `~(i = dimindex (:N) + 1 /\ ~(i' = dimindex (:N) + 1))` THEN
    SIMP_TAC[GSYM IMP_CONJ] THEN
    SIMP_TAC[TAUT `((~(P /\ ~Q) /\ ~(P /\ Q)) /\ ~(~P /\ Q)) <=> (~P /\ ~Q)`] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `i <= dimindex (:(N,1)finite_sum)` THEN
    UNDISCH_TAC `i' <= dimindex (:(N,1)finite_sum)` THEN
    SIMP_TAC[ARITH_RULE `m <= n + 1 <=> m <= n \/ m = n + 1`;DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    ASM_MESON_TAC[MAT_COMPONENT]);;

let HOMO_POINT_MK_POINT = prove
    (`!x:real^N. homo_point (mk_point x) = 
            (lambda i. if i = (dimindex(:N) + 1) then &1
                        else x$i )`,
    MESON_TAC[homo_point;point_tybij;CART_EQ;LAMBDA_BETA]);;
    
let HOMO_TRANS_MUL_POINT = prove    
    (`!x y:real^N R:real^N^N. (homo_trans x R) ** (homo_point (mk_point y)) = homo_point (mk_point (R ** y + x))`,
    REPEAT GEN_TAC THEN 
    SIMP_TAC[homo_trans;HOMO_POINT_MK_POINT;
             CART_EQ;LAMBDA_BETA;matrix_vector_mul] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;
             ARITH_RULE `x + 1 = SUC x`;ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG] THEN
    GEN_TAC THEN DISCH_TAC THEN
    COND_CASES_TAC THENL 
    [SIMP_TAC[REAL_ARITH `x + &1 * &1 = &1 <=> x = &0`] THEN
     MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN BETA_TAC THEN
     MESON_TAC[ARITH_RULE `i <= x ==> ~(i = SUC x)`;REAL_MUL_LZERO]; ALL_TAC] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT;GSYM matrix_vector_mul;
             REAL_MUL_RID;REAL_EQ_ADD_RCANCEL] THEN
    UNDISCH_TAC `1 <= i /\ i <= SUC (dimindex (:N))` THEN
    UNDISCH_TAC `~(i = SUC (dimindex (:N)))` THEN
    SIMP_TAC[TAUT `~P /\ Q /\ (P \/ R) <=> (~P /\ Q /\ R)`;
             GSYM IMP_CONJ;LE;dot;MATRIX_VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN BETA_TAC THEN
    SIMP_TAC[ARITH_RULE `i <= x ==> ~(i = SUC x)`]);;
    
let HOMO_TRANS_MUL_TRANS_POINT = prove
    (`!x1 x2 y:real^N R1 R2:real^N^N. 
    (homo_trans x1 R1) ** (homo_trans x2 R2) ** (homo_point (mk_point y)) = 
    homo_point (mk_point (R1 ** R2 ** y + (x1 + R1 ** x2)))`,
    REWRITE_TAC[HOMO_TRANS_MUL_POINT;MATRIX_VECTOR_MUL_ADD_LDISTRIB;VECTOR_ADD_AC]);;

let MATRIX_EQ_HOMO_POINT = prove 
    (`!A:real^(N,1)finite_sum^M B. 
        (A = B) = !y:real^N. A ** (homo_point (mk_point y)) = B ** (homo_point (mk_point y))`, 
    REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN `i:num` o SPEC `(vec 0):real^N`) THEN
    SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA;
             HOMO_POINT_MK_POINT; VEC_COMPONENT] THEN
    SIMP_TAC[COND_RAND; REAL_MUL_RZERO] THEN
    SIMP_TAC[SUM_DELTA] THEN
    SIMP_TAC[IN_NUMSEG;DIMINDEX_FINITE_SUM;DIMINDEX_1;LE_REFL;
             ARITH_RULE `x + 1 = SUC x`;ARITH_RULE `1 <= x ==> 1 <= SUC x`;DIMINDEX_GE_1;REAL_MUL_RID] THEN
    REPEAT STRIP_TAC THEN 
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN `i:num` o SPEC `(basis i):real^N`) THEN
    SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA; HOMO_POINT_MK_POINT; basis] THEN
    DISCH_THEN(MP_TAC o SPEC `i':num`) THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    SIMP_TAC[ARITH_RULE `x + 1 = SUC x`;ARITH_RULE `1 <= x ==> 1 <= SUC x`;
    ARITH_RULE `i <= x ==> ~(i = SUC x)`;DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG] THEN
    ASM_SIMP_TAC[REAL_MUL_RID;REAL_EQ_ADD_RCANCEL] THEN
    ASM_SIMP_TAC[LAMBDA_BETA;COND_RAND; REAL_MUL_RZERO] THEN
    SIMP_TAC[SUM_DELTA;REAL_MUL_RID] THEN
    ASM_CASES_TAC `i' = SUC (dimindex (:N))` THENL
    [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `i' <= SUC (dimindex (:N))` THEN
    UNDISCH_TAC `~(i' = SUC (dimindex (:N)))` THEN
    SIMP_TAC[TAUT `~P /\ (P \/ R) <=> (~P /\ R)`;GSYM IMP_CONJ;LE] THEN
    ASM_SIMP_TAC[IN_NUMSEG;IMP_CONJ]);;
  
let HOMO_TRANS_MUL_TRANS = prove
    (`!x1 x2:real^N R1 R2:real^N^N. 
    (homo_trans x1 R1) ** (homo_trans x2 R2) = homo_trans (x1 + R1 ** x2) (R1 ** R2)`, 
    MESON_TAC[MATRIX_EQ_HOMO_POINT;HOMO_TRANS_MUL_POINT;HOMO_TRANS_MUL_TRANS_POINT;MATRIX_VECTOR_MUL_ASSOC]);;
    
let INVERTIBLE_HOMO_TRANS = prove
    (`!x:real^N R:real^N^N. invertible R ==> invertible (homo_trans x R)`,
    REPEAT STRIP_TAC THEN SIMP_TAC[invertible] THEN
    EXISTS_TAC `homo_trans (-- (matrix_inv (R:real^N^N)) ** (x:real^N)) (matrix_inv R)` THEN
    ASM_SIMP_TAC[HOMO_TRANS_MUL_TRANS;MATRIX_INV;MATRIX_VECTOR_MUL_ASSOC;
                 MATRIX_MUL_RNEG;MATRIX_VECTOR_MUL_LNEG;MATRIX_VECTOR_MUL_LID;
                 VECTOR_ADD_RINV;VECTOR_ADD_LINV;HOMO_TRANS_EQ_MAT]);;

let MATRIX_INV_HOMO_TRANS = prove    
    (`!x:real^N R:real^N^N. invertible R ==> 
    matrix_inv (homo_trans x R) = homo_trans (-- (matrix_inv R) ** x) (matrix_inv R)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_LEFT THEN
    ASM_SIMP_TAC[HOMO_TRANS_MUL_TRANS;MATRIX_INV;MATRIX_VECTOR_MUL_LNEG;VECTOR_ADD_LINV;HOMO_TRANS_EQ_MAT]);;

let HOMO_POINT_MK_POINT_UNIQUE = prove
    (`!x1 x2:real^N. homo_point (mk_point x1) = homo_point (mk_point x2) <=> x1 = x2`,
    REPEAT GEN_TAC THEN SIMP_TAC[HOMO_POINT_MK_POINT;CART_EQ;LAMBDA_BETA] THEN 
    EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `x + 1 = SUC x`;LE] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN ARITH_TAC);;

let HOMO_TRANS_UNIQUE = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
        homo_trans x1 R1 = homo_trans x2 R2 <=> (x1 = x2 /\ R1 = R2)`,
    REPEAT GEN_TAC THEN 
    SIMP_TAC[MATRIX_EQ_HOMO_POINT;HOMO_TRANS_MUL_POINT;
             HOMO_POINT_MK_POINT_UNIQUE] THEN 
    SIMP_TAC[VECTOR_ARITH `!x1 x2 y1 y2:real^N. (y1 + x1 = y2 + x2) <=> (y1 - y2 = x2 - x1)`; GSYM MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN EQ_TAC THENL
    [DISCH_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `(vec 0):real^N`) THEN 
     SIMP_TAC[MATRIX_VECTOR_MUL_RZERO;VECTOR_ARITH `vec 0 = x2 - x1 <=> x1 = x2`] THEN STRIP_TAC THEN UNDISCH_TAC `!y. ((R1:real^N^N) - R2) ** y = x2 - x1` THEN
     ASM_SIMP_TAC[GSYM MATRIX_EQ_0;VECTOR_SUB_REFL;MATRIX_SUB_EQ];
     SIMP_TAC[VECTOR_SUB_REFL;MATRIX_SUB_REFL;MATRIX_VECTOR_MUL_LZERO]]);;

let HOMO_TRANS_SUB = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
    (homo_trans x1 R1) - (homo_trans x2 R2) =
    (lambda i j. if i = (dimindex(:N) + 1) /\ ~(j = dimindex(:N) + 1) then &0
                 else if i = (dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then &0
                      else if ~(i = dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then (x1 - x2)$i
                           else (R1 - R2)$i$j)`,
    SIMP_TAC[homo_trans;CART_EQ;LAMBDA_BETA;MATRIX_SUB_COMPONENT] THEN
    REPEAT STRIP_TAC THEN 
    COND_CASES_TAC THENL [ASM_SIMP_TAC[REAL_SUB_0]; ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_SIMP_TAC[REAL_SUB_0]; ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_SIMP_TAC[VECTOR_SUB_COMPONENT]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_SUB_COMPONENT]);;
    
let HOMO_TRANS_LEFT_EQ_DIST = prove
    (`!x:real^N R1 R2:real^N^N. matrix_dist((homo_trans x R1), (homo_trans x R2)) = matrix_dist(R1,R2)`,
    SIMP_TAC[matrix_dist;HOMO_TRANS_SUB;FNORM_EQ;matrix_mul;TRANSP_COMPONENT;
             LAMBDA_BETA;trace;VECTOR_SUB_REFL;VEC_COMPONENT] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `x + 1 = SUC x`;
             ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             ARITH_RULE `i <= x ==> ~(i = SUC x)`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC[REAL_ADD_RID;REAL_MUL_RZERO;SUM_0]);;

let HOMO_TRANS_RIGHT_EQ_DIST = prove
    (`!x1 x2:real^N R:real^N^N. 
        matrix_dist((homo_trans x1 R), (homo_trans x2 R)) = dist(x1,x2)`,
    SIMP_TAC[matrix_dist;HOMO_TRANS_SUB;dist;fnorm;vector_norm;SQRT_INJ;
             matrix_mul;TRANSP_COMPONENT;trace;LAMBDA_BETA;dot;
             MATRIX_SUB_REFL;MAT_0_COMPONENT] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `x + 1 = SUC x`;
             ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             ARITH_RULE `i <= x ==> ~(i = SUC x)`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC[REAL_ADD_RID;REAL_ADD_LID;REAL_MUL_RZERO;SUM_0]);;
    
let HOMO_TRANS_DIST_TRIANGLE = prove
    (`!x1 x2:real^N R1 R2:real^N^N. 
        matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) <= 
        matrix_dist(R1,R2) + dist(x1,x2)`,
    let lem1 = prove
    (`!x y.  (&0 <= x /\ &0 <= y) ==> (&0 <= x * y)`,
    SIMP_TAC[REAL_MUL_POS_LE] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN ITAUT_TAC) in
    REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_ABS_DIST;GSYM REAL_ABS_MATRIX_DIST] THEN
    SIMP_TAC[DIST_POS_LE;MATRIX_DIST_POS_LE;REAL_ARITH `!x y. &0 <= x /\ &0 <= y ==> abs(x) + abs(y) = abs(x + y)`;REAL_LE_SQUARE_ABS] THEN
    SIMP_TAC[matrix_dist;HOMO_TRANS_SUB;dist;fnorm;vector_norm;SQRT_INJ;
             matrix_mul;TRANSP_COMPONENT;trace;LAMBDA_BETA;dot] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `x + 1 = SUC x`;
             ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             ARITH_RULE `i <= x ==> ~(i = SUC x)`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC[REAL_ADD_RID;REAL_MUL_RZERO;SUM_0] THEN
    SIMP_TAC[SQRT_POW_2;REAL_LE_ADD;SUM_SUM_SQUARE_LE;SUM_POS_LE_NUMSEG;REAL_LE_POW_2;GSYM REAL_POW_2] THEN
    SIMP_TAC[REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB;REAL_POW_2] THEN
    SIMP_TAC[SQRT_POW_2;REAL_LE_ADD;SUM_SUM_SQUARE_LE;SUM_POS_LE_NUMSEG;REAL_LE_POW_2;GSYM REAL_POW_2] THEN
    SIMP_TAC[GSYM REAL_ADD_ASSOC] THEN
    MATCH_MP_TAC (REAL_ARITH `&0 <= C /\ &0 <= D ==> A + B <= A + C + D + B`) THEN
    SIMP_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC lem1 THEN
    SIMP_TAC[SQRT_POS_LE;REAL_POW_2;SUM_SUM_SQUARE_LE] THEN
    SIMP_TAC[SQRT_POS_LE;SUM_POS_LE_NUMSEG;REAL_LE_POW_2;GSYM REAL_POW_2]);;

let HOMO_TRANS_DIST_TRIANGLE_FST = prove    
    (`!x1 x2:real^N R1 R2:real^N^N. 
        dist(x1,x2) <= 
        matrix_dist((homo_trans x1 R1), (homo_trans x2 R2))`,
    REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_ABS_DIST;GSYM REAL_ABS_MATRIX_DIST] THEN
    SIMP_TAC[DIST_POS_LE;MATRIX_DIST_POS_LE;REAL_ARITH `!x y. &0 <= x /\ &0 <= y ==> abs(x) + abs(y) = abs(x + y)`;REAL_LE_SQUARE_ABS] THEN
    SIMP_TAC[matrix_dist;HOMO_TRANS_SUB;dist;fnorm;vector_norm;SQRT_INJ;
             matrix_mul;TRANSP_COMPONENT;trace;LAMBDA_BETA;dot] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `x + 1 = SUC x`;
             ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             ARITH_RULE `i <= x ==> ~(i = SUC x)`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC[REAL_ADD_RID;REAL_MUL_RZERO;SUM_0] THEN
    SIMP_TAC[SQRT_POW_2;REAL_LE_ADD;SUM_SUM_SQUARE_LE;SUM_POS_LE_NUMSEG;REAL_LE_POW_2;GSYM REAL_POW_2] THEN
    SIMP_TAC[REAL_LE_ADDL] THEN
    SIMP_TAC[SUM_POS_LE_NUMSEG;REAL_LE_POW_2]);;
    
let HOMO_TRANS_DIST_TRIANGLE_SND = prove    
    (`!x1 x2:real^N R1 R2:real^N^N. 
        matrix_dist(R1,R2) <= 
        matrix_dist((homo_trans x1 R1), (homo_trans x2 R2))`,
    REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_ABS_DIST;GSYM REAL_ABS_MATRIX_DIST] THEN
    SIMP_TAC[DIST_POS_LE;MATRIX_DIST_POS_LE;REAL_ARITH `!x y. &0 <= x /\ &0 <= y ==> abs(x) + abs(y) = abs(x + y)`;REAL_LE_SQUARE_ABS] THEN
    SIMP_TAC[matrix_dist;HOMO_TRANS_SUB;dist;fnorm;vector_norm;SQRT_INJ;
             matrix_mul;TRANSP_COMPONENT;trace;LAMBDA_BETA;dot] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `x + 1 = SUC x`;
             ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             ARITH_RULE `i <= x ==> ~(i = SUC x)`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC[REAL_ADD_RID;REAL_MUL_RZERO;SUM_0] THEN
    SIMP_TAC[SQRT_POW_2;REAL_LE_ADD;SUM_SUM_SQUARE_LE;SUM_POS_LE_NUMSEG;REAL_LE_POW_2;GSYM REAL_POW_2] THEN
    SIMP_TAC[REAL_LE_ADDR] THEN
    SIMP_TAC[SUM_POS_LE_NUMSEG;REAL_LE_POW_2]);;
        
let HOMO_TRANS_DIST_TRIANGLE_LE_FST = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
    matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) <= e ==> dist(x1,x2) <= e`,
    MESON_TAC[REAL_LE_TRANS; HOMO_TRANS_DIST_TRIANGLE_FST]);;
    
let HOMO_TRANS_DIST_TRIANGLE_LE_SND = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
        matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) <= e ==> matrix_dist(R1,R2) <= e`,
    MESON_TAC[REAL_LE_TRANS; HOMO_TRANS_DIST_TRIANGLE_SND]);;

let HOMO_TRANS_DIST_TRIANGLE_LT_FST = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
    matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) < e ==> dist(x1,x2) < e`,
    MESON_TAC[REAL_LET_TRANS; HOMO_TRANS_DIST_TRIANGLE_FST]);;
    
let HOMO_TRANS_DIST_TRIANGLE_LT_SND = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
        matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) < e ==> matrix_dist(R1,R2) < e`,
    MESON_TAC[REAL_LET_TRANS; HOMO_TRANS_DIST_TRIANGLE_SND]);;
    
let HOMO_TRANS_DIST_TRIANGLE_LE = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
        matrix_dist(R1,R2) + dist(x1,x2) <= e ==> matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) <= e`,
    MESON_TAC[REAL_LE_TRANS; HOMO_TRANS_DIST_TRIANGLE]);;
    
let HOMO_TRANS_DIST_TRIANGLE_LT = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
        matrix_dist(R1,R2) + dist(x1,x2) < e ==> matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) < e`,
    MESON_TAC[REAL_LET_TRANS; HOMO_TRANS_DIST_TRIANGLE]);;

let HOMO_TRANS_DIST_TRIANGLE_HALF_LE = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
    matrix_dist(R1,R2) <= e / &2 /\ dist(x1,x2) <= e / &2 ==> matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) <= e`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMO_TRANS_DIST_TRIANGLE_LE THEN
    ASM_MESON_TAC[REAL_HALF; REAL_LE_ADD2;
                  HOMO_TRANS_DIST_TRIANGLE_LE_FST;HOMO_TRANS_DIST_TRIANGLE_LE_SND]);;
    
let HOMO_TRANS_DIST_TRIANGLE_HALF_LT = prove
    (`!x1 x2:real^N R1 R2:real^N^N.
    matrix_dist(R1,R2) < e / &2 /\ dist(x1,x2) < e / &2 ==> matrix_dist((homo_trans x1 R1), (homo_trans x2 R2)) < e`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMO_TRANS_DIST_TRIANGLE_LT THEN
    ASM_MESON_TAC[REAL_HALF; REAL_LT_ADD2;
                  HOMO_TRANS_DIST_TRIANGLE_LT_FST;HOMO_TRANS_DIST_TRIANGLE_LT_SND]);;

let INVERTIBLE_HOMO_TRANS_MAT = prove 
    (`!x:real^N. invertible (homo_trans x (mat 1))`,
    GEN_TAC THEN SIMP_TAC[INVERTIBLE_LEFT_INVERSE] THEN 
    EXISTS_TAC `homo_trans (--(x:real^N)) (mat 1)` THEN
    SIMP_TAC[HOMO_TRANS_MUL_TRANS;MATRIX_VECTOR_MUL_LID;
             MATRIX_MUL_LID;VECTOR_ADD_LINV;HOMO_TRANS_EQ_MAT]);;
             
let INVERTIBLE_HOMO_TRANS_VEC = prove     
    (`!R:real^N^N. invertible R ==> invertible (homo_trans (vec 0) R)`,
    REPEAT STRIP_TAC THEN SIMP_TAC[INVERTIBLE_LEFT_INVERSE] THEN
    EXISTS_TAC `homo_trans (vec 0) (matrix_inv (R:real^N^N))` THEN
    ASM_SIMP_TAC[HOMO_TRANS_MUL_TRANS;MATRIX_VECTOR_MUL_RZERO;
             MATRIX_INV;VECTOR_ADD_LID;HOMO_TRANS_EQ_MAT]);;
             
let HOMO_TRANS_SPLIT = prove
    (`!x:real^N R:real^N^N. 
        homo_trans x R = (homo_trans x (mat 1)) ** (homo_trans (vec 0) R)`,
    SIMP_TAC[HOMO_TRANS_MUL_TRANS;MATRIX_VECTOR_MUL_RZERO;
             MATRIX_MUL_LID;VECTOR_ADD_RID;HOMO_TRANS_UNIQUE]);;
    
let MATRIX_CLOSED_HOMO_TRANS = prove
    (`matrix_closed {homo_trans (x:real^N) (R:real^N^N) | orthogonal_matrix R}`,
    REWRITE_TAC[GSYM MATRIX_COMPLETE_EQ_CLOSED;matrix_complete] THEN 
    SIMP_TAC[IN_ELIM_THM;MATRIX_LIM_SEQUENTIALLY;
             MATRIX_CAUCHY;SKOLEM_THM;IMP_CONJ] THEN
    GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC `R:num->real^N^N`) THEN
    ASM_SIMP_TAC[HOMO_TRANS_LEFT_EQ_DIST] THEN DISCH_TAC THEN
    MP_TAC MATRIX_CLOSED_ORTHOGONAL_MATRIX THEN
    SIMP_TAC[GSYM MATRIX_COMPLETE_EQ_CLOSED;matrix_complete] THEN
    SIMP_TAC[IN_ELIM_THM;MATRIX_LIM_SEQUENTIALLY;MATRIX_CAUCHY] THEN
    DISCH_THEN(MP_TAC o SPEC `R:num->real^N^N`) THEN ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `R:real^N^N`) THEN SIMP_TAC[LEFT_AND_EXISTS_THM] THEN
    EXISTS_TAC `homo_trans (x:real^N) (R:real^N^N)` THEN
    EXISTS_TAC `(R:real^N^N)` THEN
    ASM_SIMP_TAC[HOMO_TRANS_UNIQUE;HOMO_TRANS_LEFT_EQ_DIST]);;

(* ------------------------------------------------------------------------- *)
(* homogeneous type                                                          *)
(* ------------------------------------------------------------------------- *)
    
let ishomo = define
 `ishomo (s:real^(N,1)finite_sum^(N,1)finite_sum) <=> ?x R. s = (homo_trans x R)`;;

let homo_tybij_th = prove
 (`?t:real^(N,1)finite_sum^(N,1)finite_sum. ishomo t`,
  EXISTS_TAC `homo_trans ((vec 0):real^N) (mat 0)` THEN MESON_TAC[ishomo]);;

let homo_tybij =
  new_type_definition "homo" ("homo","homo_operations") homo_tybij_th;; 

overload_interface ("--",`(homo_neg):(N)homo->(N)homo`);;
overload_interface ("+",`(homo_add):(N)homo->(N)homo->(N)homo`);;
overload_interface ("-",`(homo_sub):(N)homo->(N)homo->(N)homo`);;

parse_as_infix("%%%",(21,"right"));;

let homo_pair = new_definition
`(homo_pair:(N)homo->(real^N#real^N^N)) h = @p. homo_operations h = homo_trans (FST p) (SND p)`;;

let HOMO_EQ = prove
    (`!h1:(N)homo h2.  h1 = h2 <=> homo_operations h1 = homo_operations h2`,
    MESON_TAC [homo_tybij;ishomo]);;

let HOMO_PAIR_EXISTS = prove
    (`!h:(N)homo. ?p. homo_operations h = homo_trans (FST p) (SND p)`,
    GEN_TAC THEN MP_TAC (CONJUNCT2 homo_tybij) THEN 
    DISCH_THEN (MP_TAC o ISPEC `homo_operations (h:(N)homo)`) THEN
    SIMP_TAC [EXISTS_PAIR_THM;ishomo] THEN MESON_TAC [homo_tybij;ishomo]);;
    
let HOMO_PAIR = prove
    (`!x:real^N R. homo_pair (homo (homo_trans x R)) = (x,R)`,
    REPEAT GEN_TAC THEN REWRITE_TAC [homo_pair] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    GEN_TAC THEN REWRITE_TAC [LAMBDA_PAIR_THM] THEN EQ_TAC THENL
    [STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM PAIR] THEN 
     SIMP_TAC [PAIR_EQ] THEN REWRITE_TAC[GSYM HOMO_TRANS_UNIQUE] THEN
     ASM_MESON_TAC [homo_tybij; ishomo]; ALL_TAC] THEN 
    SIMP_TAC[] THEN ASM_MESON_TAC [homo_tybij; ishomo]);;
    
let HOMO_PAIR_BIJ = prove
    (`!h1:(N)homo h2. 
        h1 = h2 <=> homo_pair h1 = homo_pair h2`,
    REPEAT GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC HOMO_PAIR_EXISTS THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC  o SPEC `h1:(N)homo`) THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC  o SPEC `h2:(N)homo`) THEN STRIP_TAC THEN
    REWRITE_TAC[HOMO_EQ] THEN
    ASM_REWRITE_TAC[homo_pair;HOMO_TRANS_UNIQUE;GSYM PAIR_EQ] THEN
    SELECT_ELIM_TAC THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;    
    
let HOMO_PAIR_ALT = prove
    (`!h:(N)homo. homo (homo_trans (FST (homo_pair h)) (SND (homo_pair h))) = h`,
    REWRITE_TAC[HOMO_PAIR_BIJ;HOMO_PAIR]);;

let homo_cmul = new_definition
`((%%%):real->(N)homo->(N)homo) c h = homo (homo_trans (c % (FST (homo_pair h)))  (c %% (SND (homo_pair h))))`;;

let homo_neg = new_definition
`(homo_neg:(N)homo->(N)homo) h = homo (homo_trans (--(FST (homo_pair h)))  (--(SND (homo_pair h))))`;;

let homo_add = new_definition
`(homo_add:(N)homo->(N)homo->(N)homo) h1 h2 = homo (homo_trans (FST (homo_pair h1) + FST (homo_pair h2))  (SND (homo_pair h1) + SND (homo_pair h2)))`;;

let homo_sub = new_definition
`(homo_sub:(N)homo->(N)homo->(N)homo) h1 h2 = homo (homo_trans (FST (homo_pair h1) - FST (homo_pair h2))  (SND (homo_pair h1) - SND (homo_pair h2)))`;;

let homo_mat = new_definition
`(homo_mat:num->(N)homo) k = homo (homo_trans (vec 0) (mat k))`;;

let HOMO_PAIR_EQ = prove
    (`!h1:(N)homo h2. 
         (homo_pair h1) = (homo_pair h2) <=>
        (FST (homo_pair h1) = FST (homo_pair h2)) /\ 
        (SND (homo_pair h1) = SND (homo_pair h2))`,
    REWRITE_TAC[GSYM PAIR_EQ]);;

let HOMO_PAIR_ADD = prove
    (`!h1:(N)homo h2. 
        (FST (homo_pair (h1 + h2)) = FST (homo_pair h1) + FST (homo_pair h2)) /\ 
        (SND (homo_pair (h1 + h2)) = SND (homo_pair h1) + SND (homo_pair h2))`,
    REWRITE_TAC[GSYM PAIR_EQ;homo_add;HOMO_PAIR]);;

let HOMO_PAIR_SUB = prove
    (`!h1:(N)homo h2. 
        (FST (homo_pair (h1 - h2)) = FST (homo_pair h1) - FST (homo_pair h2)) /\ 
        (SND (homo_pair (h1 - h2)) = SND (homo_pair h1) - SND (homo_pair h2))`,
    REWRITE_TAC[GSYM PAIR_EQ;homo_sub;HOMO_PAIR]);;
    
let HOMO_PAIR_CMUL = prove
    (`!h:(N)homo c:real. 
        (FST (homo_pair (c %%% h)) = c % (FST (homo_pair h))) /\ 
        (SND (homo_pair (c %%% h)) = c %% (SND (homo_pair h)))`,
    REWRITE_TAC[GSYM PAIR_EQ;homo_cmul;HOMO_PAIR]);;
    
let HOMO_PAIR_NEG = prove
    (`!h:(N)homo. 
        (FST (homo_pair (-- h)) = -- (FST (homo_pair h))) /\ 
        (SND (homo_pair (-- h)) = -- (SND (homo_pair h)))`,
    REWRITE_TAC[GSYM PAIR_EQ;homo_neg;HOMO_PAIR]);;
    
let HOMO_PAIR_ZERO = prove
    (`  (FST (homo_pair (homo_mat 0)) = vec 0) /\ 
        (SND (homo_pair (homo_mat 0)) = mat 0)`,
    REWRITE_TAC[GSYM PAIR_EQ;homo_mat;HOMO_PAIR]);;

let HM_CMUL_ASSOC = prove
    (`!a b X:(N)homo. a %%% (b %%% X) = (a * b) %%% X`,
    REPEAT GEN_TAC THEN REWRITE_TAC[homo_cmul] THEN AP_TERM_TAC THEN
    REWRITE_TAC[HOMO_TRANS_UNIQUE;HOMO_PAIR] THEN CONJ_TAC THENL
    [VECTOR_ARITH_TAC; MATRIX_ARITH_TAC]);;
  
let HM_CMUL_LID = prove
    (`!X:(N)homo. &1 %%% X = X`,
    REWRITE_TAC[homo_cmul;VECTOR_MUL_LID;MATRIX_CMUL_LID;HOMO_PAIR_ALT]);;
  
let HM_ADD_SYM = prove
    (`!A:(N)homo B. A + B = B + A`,
    REWRITE_TAC[homo_add;VECTOR_ADD_SYM;MATRIX_ADD_SYM]);;
  
let HM_ADD_ASSOC = prove
    (`!A:(N)homo B C. A + (B + C) = (A + B) + C`,
    REWRITE_TAC[homo_add;VECTOR_ADD_ASSOC;MATRIX_ADD_ASSOC;HOMO_PAIR]);;
    
let HM_ADD_LID = prove
    (`!A. homo_mat 0 + A = A`,
    REWRITE_TAC[homo_add;homo_mat;VECTOR_ADD_LID;MATRIX_ADD_LID;HOMO_PAIR;HOMO_PAIR_ALT]);;

let HM_ADD_RID = prove
    (`!A. A + homo_mat 0 = A`,
    REWRITE_TAC[homo_add;homo_mat;VECTOR_ADD_RID;MATRIX_ADD_RID;HOMO_PAIR;HOMO_PAIR_ALT]);;
    
let HM_NEG_SUB = prove
    (`!A:(N)homo B. --(A - B) = B - A`,
    REWRITE_TAC[homo_neg;homo_sub;HOMO_PAIR;VECTOR_NEG_SUB;MATRIX_NEG_SUB]);;
    
let HM_SUB_NEG2 = prove
    (`!A:(N)homo B. (--A - --B) = B - A`,
    REWRITE_TAC[homo_neg;homo_sub;HOMO_PAIR;MATRIX_SUB_NEG2;VECTOR_ARITH `!A B:real^N. (--A - --B) = B - A`]);;

let HM_ADD_LNEG = prove
    (`!A. --A + A = homo_mat 0`,
    REWRITE_TAC[homo_neg;homo_add;homo_mat;HOMO_PAIR;
                VECTOR_ADD_LINV;MATRIX_ADD_LNEG]);;

let HM_ADD_RNEG = prove
    (`!A. A + --A = homo_mat 0`,
    REWRITE_TAC[homo_neg;homo_add;homo_mat;HOMO_PAIR;
                VECTOR_ADD_RINV;MATRIX_ADD_RNEG]);;
    
let HM_SUB = prove
    (`!A:(N)homo B. A - B = A + --B`,
    REWRITE_TAC[homo_neg;homo_sub;homo_add;HOMO_PAIR;VECTOR_SUB;MATRIX_SUB]);;
    
let HM_SUB_REFL = prove
    (`!A:(N)homo. A - A = homo_mat 0`,
    REWRITE_TAC[HM_SUB; HM_ADD_RNEG]);;
    
let HM_SUB_EQ = prove
    (`!A B:(N)homo. A - B = homo_mat 0 <=> A = B`,
    REWRITE_TAC[homo_sub;homo_mat;HOMO_PAIR_BIJ;HOMO_PAIR;
                HOMO_PAIR_EQ;PAIR_EQ;VECTOR_SUB_EQ;MATRIX_SUB_EQ]);;
                
let HM_SUB_ADD = prove
    (`!A B:(N)homo. (A - B) + B = A`,
    REWRITE_TAC[homo_sub;homo_add;HOMO_PAIR;MATRIX_SUB_ADD;VECTOR_SUB_ADD;HOMO_PAIR_ALT]);;

let HM_SUB_ADD2 = prove
    (`!A B:(N)homo. A + (B - A) = B`,
    REWRITE_TAC[homo_sub;homo_add;HOMO_PAIR;MATRIX_SUB_ADD2;VECTOR_SUB_ADD2;HOMO_PAIR_ALT]);;
              
let HM_CMUL_ADD_LDISTRIB = prove
    (`!A:(N)homo B c. c %%% (A + B) = c %%% A + c %%% B`,
    REWRITE_TAC[homo_cmul;homo_add;HOMO_PAIR;VECTOR_ADD_LDISTRIB;MATRIX_CMUL_ADD_LDISTRIB]);;

let HM_CMUL_SUB_LDISTRIB = prove
    (`!A:(N)homo B c. c %%% (A - B) = c %%% A - c %%% B`,
    REWRITE_TAC[homo_cmul;homo_sub;HOMO_PAIR;VECTOR_SUB_LDISTRIB;MATRIX_CMUL_SUB_LDISTRIB]);;

let HM_CMUL_ADD_RDISTRIB = prove
    (`!A:(N)homo b c. (b + c) %%% A = b %%% A + c %%% A`,
    REWRITE_TAC[homo_cmul;homo_add;HOMO_PAIR;VECTOR_ADD_RDISTRIB;MATRIX_CMUL_ADD_RDISTRIB]);;

let HM_CMUL_SUB_RDISTRIB = prove
    (`!A:(N)homo b c. (b - c) %%% A = b %%% A - c %%% A`,
    REWRITE_TAC[homo_cmul;homo_sub;HOMO_PAIR;VECTOR_SUB_RDISTRIB;MATRIX_CMUL_SUB_RDISTRIB]);;
    
let HM_SUB_RZERO = prove
    (`!A:(N)homo. A - homo_mat 0 = A`,
    REWRITE_TAC[homo_sub;homo_mat;HOMO_PAIR;VECTOR_SUB_RZERO;MATRIX_SUB_RZERO;HOMO_PAIR_ALT]);;

let HM_SUB_LZERO = prove
    (`!A:(N)homo. homo_mat 0 - A = --A`,
    REWRITE_TAC[homo_sub;homo_neg;homo_mat;HOMO_PAIR;VECTOR_SUB_LZERO;MATRIX_SUB_LZERO;HOMO_PAIR_ALT]);;
    
let HM_NEG_NEG = prove
    (`!A:(N)homo. --(--A) = A`,
    REWRITE_TAC[homo_neg;HOMO_PAIR;HOMO_PAIR_ALT;VECTOR_NEG_NEG;MATRIX_NEG_NEG]);;
    
let HM_SUB_SUB = prove
    (`!A B:(N)homo.(A - B) - A = --B`,
    REWRITE_TAC[homo_neg;homo_sub;HOMO_PAIR;HOMO_PAIR_ALT;MATRIX_SUB_SUB;VECTOR_ARITH `!A B:real^N. (A - B) - A = --B`]);;

(* ------------------------------------------------------------------------- *)
(* homogeneous interval                                                      *)
(* ------------------------------------------------------------------------- *)

let open_homo_interval = new_definition
  `open_homo_interval(a:(N)homo,b:(N)homo) =
        {x:(N)homo | (FST (homo_pair x)) IN interval ((FST (homo_pair a)),(FST (homo_pair b))) /\ (SND (homo_pair x)) IN matrix_interval ((SND (homo_pair a)),(SND (homo_pair b)))}`;;

let closed_homo_interval = new_definition
  `closed_homo_interval(l:((N)homo#(N)homo)list) =
         {x:(N)homo | (FST (homo_pair x)) IN interval [(FST (homo_pair (FST(HD l)))),(FST (homo_pair (SND(HD l))))] /\ (SND (homo_pair x)) IN matrix_interval [(SND (homo_pair (FST(HD l)))),(SND (homo_pair (SND(HD l))))]}`;;

make_overloadable "homo_interval" `:A`;;

overload_interface("homo_interval",`open_homo_interval`);;
overload_interface("homo_interval",`closed_homo_interval`);;

let homo_interval = prove
 (`!a:(N)homo b. (homo_interval (a,b) = 
           {x:(N)homo | (FST (homo_pair x)) IN interval ((FST (homo_pair a)),(FST (homo_pair b))) /\ (SND (homo_pair x)) IN matrix_interval ((SND (homo_pair a)),(SND (homo_pair b)))}) /\
   (homo_interval [a,b] =  
           {x:(N)homo | (FST (homo_pair x)) IN interval [(FST (homo_pair a)),(FST (homo_pair b))] /\ (SND (homo_pair x)) IN matrix_interval [(SND (homo_pair a)),(SND (homo_pair b))]})`,
  REWRITE_TAC[open_homo_interval; closed_homo_interval; HD; FST; SND]);;
  
let IN_HOMO_INTERVAL = prove
 (`(!x:(N)homo.
        x IN homo_interval (a,b) <=>
        (FST (homo_pair x)) IN interval ((FST (homo_pair a)),(FST (homo_pair b))) /\ (SND (homo_pair x)) IN matrix_interval ((SND (homo_pair a)),(SND (homo_pair b)))) /\
   (!x:(N)homo.
        x IN homo_interval [a,b] <=>
        (FST (homo_pair x)) IN interval [(FST (homo_pair a)),(FST (homo_pair b))] /\ (SND (homo_pair x)) IN matrix_interval [(SND (homo_pair a)),(SND (homo_pair b))])`,
  REWRITE_TAC[homo_interval; IN_ELIM_THM]);;
  
let HOMO_INTERVAL_OPEN_SUBSET_CLOSED = prove
 (`!a b. homo_interval(a,b) SUBSET homo_interval[a,b]`,
  REWRITE_TAC[SUBSET; IN_HOMO_INTERVAL;IN_INTERVAL;IN_MATRIX_INTERVAL] THEN
  MESON_TAC[REAL_LT_IMP_LE]);;

let HOMO_INTERVAL_EQ_EMPTY = prove
 (`((homo_interval [a:(N)homo,b] = {}) <=>
    interval [(FST (homo_pair a)),(FST (homo_pair b))] = {} \/ 
    matrix_interval [(SND (homo_pair a)),(SND (homo_pair b))] = {}) /\
   ((homo_interval (a:(N)homo,b) = {}) <=>
    interval ((FST (homo_pair a)),(FST (homo_pair b))) = {} \/ 
    matrix_interval ((SND (homo_pair a)),(SND (homo_pair b))) = {})`,
  REWRITE_TAC[MATRIX_INTERVAL_EQ_EMPTY;INTERVAL_EQ_EMPTY] THEN
  REWRITE_TAC[EXTENSION; IN_HOMO_INTERVAL; IN_MATRIX_INTERVAL;IN_INTERVAL; NOT_IN_EMPTY] THEN
  REWRITE_TAC[NOT_FORALL_THM;DE_MORGAN_THM;NOT_IMP; GSYM CONJ_ASSOC] THEN
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
   `homo (homo_trans (lambda i. mid ((FST(homo_pair (a:(N)homo)))$i) ((FST(homo_pair (b:(N)homo)))$i)) (lambda i j. mid ((SND(homo_pair (a:(N)homo)))$i$j) ((SND(homo_pair (b:(N)homo)))$i$j))):(N)homo`) THEN
  REWRITE_TAC[HOMO_PAIR;FST;SND] THEN
  STRIP_TAC THEN POP_ASSUM MP_TAC THEN 
  ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN STRIP_TAC THEN 
  REWRITE_TAC[LEFT_OR_EXISTS_THM;RIGHT_OR_EXISTS_THM] THEN
  MAP_EVERY EXISTS_TAC [`i:num`;`i:num`;`j:num`] THEN ASM_SIMP_TAC [] THENL 
  [FIRST_X_ASSUM (MP_TAC o SPECL [`FST (homo_pair (a:(N)homo))$i`;`FST (homo_pair (b:(N)homo))$i`]);
   FIRST_X_ASSUM (MP_TAC o SPECL [`FST (homo_pair (a:(N)homo))$i`;`FST (homo_pair (b:(N)homo))$i`]);
   FIRST_X_ASSUM (MP_TAC o SPECL [`SND (homo_pair (a:(N)homo))$i$j`;`SND (homo_pair (b:(N)homo))$i$j`]);
   FIRST_X_ASSUM (MP_TAC o SPECL [`SND (homo_pair (a:(N)homo))$i$j`;`SND (homo_pair (b:(N)homo))$i$j`])] THEN
  ASM_MESON_TAC[CONTRAPOS_THM; REAL_NOT_LT]);;
  
let HOMO_INTERVAL_NE_EMPTY = prove
  (`(~(homo_interval [a:(N)homo,b] = {}) <=>
    ~(interval [(FST (homo_pair a)),(FST (homo_pair b))] = {}) /\ 
    ~(matrix_interval [(SND (homo_pair a)),(SND (homo_pair b))] = {})) /\
   (~(homo_interval (a:(N)homo,b) = {}) <=>
    ~(interval ((FST (homo_pair a)),(FST (homo_pair b))) = {}) /\ 
    ~(matrix_interval ((SND (homo_pair a)),(SND (homo_pair b))) = {}))`,
  REWRITE_TAC[HOMO_INTERVAL_EQ_EMPTY;DE_MORGAN_THM]);;

(* ------------------------------------------------------------------------- *)
(* inner product of homogeneous matrix                                       *)
(* ------------------------------------------------------------------------- *)
    
let hip = new_definition 
`(hip:(N)homo->(N)homo->real) h1 h2 = ((FST (homo_pair h1)) dot (FST (homo_pair h2))) + ((SND (homo_pair h1)) mip (SND (homo_pair h2)))`;;

parse_as_infix("hip",(21,"right"));;

let HIP_SYM = prove
    (`!A:(N)homo B. A hip B = B hip A`,
    REWRITE_TAC[hip;MIP_SYM;DOT_SYM]);;

let HIP_LADD = prove
    (`!A:(N)homo B C. (A + B) hip C = (A hip C) + (B hip C)`,
    REWRITE_TAC[hip;HOMO_PAIR_ADD;MIP_LADD;DOT_LADD] THEN REAL_ARITH_TAC);;
    
let HIP_RADD = prove
    (`!A:(N)homo B C. A hip (B + C) = (A hip B) + (A hip C)`,
    REWRITE_TAC[hip;HOMO_PAIR_ADD;MIP_RADD;DOT_RADD] THEN REAL_ARITH_TAC);;
    
let HIP_LSUB = prove
    (`!A:(N)homo B C. (A - B) hip C = (A hip C) - (B hip C)`,
    REWRITE_TAC[hip;HOMO_PAIR_SUB;MIP_LSUB;DOT_LSUB] THEN REAL_ARITH_TAC);;
    
let HIP_RSUB = prove
    (`!A:(N)homo B C. A hip (B - C) = (A hip B) - (A hip C)`,
    REWRITE_TAC[hip;HOMO_PAIR_SUB;MIP_RSUB;DOT_RSUB] THEN REAL_ARITH_TAC);;
    
let HIP_LMUL = prove
    (`!A:(N)homo B c. (c %%% A) hip B = c * (A hip B)`,
    REWRITE_TAC[hip;HOMO_PAIR_CMUL;MIP_LMUL;DOT_LMUL] THEN REAL_ARITH_TAC);;
    
let HIP_RMUL = prove
    (`!A:(N)homo B c. A hip (c %%% B) = c * (A hip B)`,
    REWRITE_TAC[hip;HOMO_PAIR_CMUL;MIP_RMUL;DOT_RMUL] THEN REAL_ARITH_TAC);;
    
let HIP_LNEG = prove
    (`!A:(N)homo B. (--A) hip B = --(A hip B)`,
    REWRITE_TAC[hip;HOMO_PAIR_NEG;MIP_LNEG;DOT_LNEG] THEN REAL_ARITH_TAC);;
    
let HIP_RNEG = prove
    (`!A:(N)homo B. A hip (--B) = --(A hip B)`,
    REWRITE_TAC[hip;HOMO_PAIR_NEG;MIP_RNEG;DOT_RNEG] THEN REAL_ARITH_TAC);;
    
let HIP_LZERO = prove
    (`!A:(N)homo. (homo_mat 0) hip A = &0`,
    REWRITE_TAC[hip;HOMO_PAIR_ZERO;MIP_LZERO;DOT_LZERO] THEN REAL_ARITH_TAC);;
    
let HIP_RZERO = prove
    (`!A:(N)homo. A hip (homo_mat 0) = &0`,
    REWRITE_TAC[hip;HOMO_PAIR_ZERO;MIP_RZERO;DOT_RZERO] THEN REAL_ARITH_TAC);;
    
let HIP_POS_LE = prove
    (`!A:(N)homo. &0 <= A hip A`,
    SIMP_TAC[hip;MIP_POS_LE;DOT_POS_LE;REAL_LE_ADD]);;
    
let HIP_EQ_0 = prove
    (`!A:(N)homo. (A hip A = &0) <=> (A = (homo_mat 0))`,
    SIMP_TAC[hip;DOT_POS_LE;MIP_POS_LE;REAL_ARITH `&0 <= x /\ &0 <= y ==> ((x + y) = &0 <=> ((x = &0) /\ (y = &0)))`;DOT_EQ_0;MIP_EQ_0] THEN
    REWRITE_TAC[GSYM PAIR_EQ;GSYM HOMO_PAIR;GSYM HOMO_PAIR_BIJ;homo_mat]);;
    
let HIP_POS_LT = prove
    (`!A:(N)homo. (&0 < A hip A) <=> ~(A = (homo_mat 0))`,
    MESON_TAC[REAL_LT_LE; HIP_POS_LE;HIP_EQ_0]);;
    
let FORALL_HIP_EQ_0 = prove
    (`(!B:(N)homo. (!A. A hip B = &0) <=> B = (homo_mat 0)) /\
      (!A:(N)homo. (!B. A hip B = &0) <=> A = (homo_mat 0))`,
    MESON_TAC[HIP_LZERO; HIP_RZERO; HIP_EQ_0]);;
    
let hnorm = new_definition
    `(hnorm:(N)homo->real) h = sqrt (h hip h)`;;

let HNORM_0 = prove
    (`hnorm(homo_mat 0) = &0`,
    REWRITE_TAC[hnorm;SQRT_0;HIP_LZERO]);;
    
let HNORM_EQ_0 = prove
    (`!A:(N)homo. hnorm A = &0 <=> A = homo_mat 0`,
    REWRITE_TAC[hnorm;SQRT_EQ_0;HIP_EQ_0]);;

let HNORM_POS_LE = prove
    (`!A:(N)homo. &0 <= hnorm A`,
    SIMP_TAC[hnorm;SQRT_POS_LE;HIP_POS_LE]);;
  
let HNORM_POS_LT = prove
    (`!A:(N)homo. &0 < hnorm A <=> ~(A = homo_mat 0)`,
    METIS_TAC[REAL_LT_LE; HNORM_POS_LE; HNORM_EQ_0]);;
  
let HNORM_MUL = prove
    (`!a A:(N)homo. hnorm(a %%% A) = abs(a) * hnorm A`,
    REWRITE_TAC[hnorm;HIP_LMUL;HIP_RMUL] THEN
    REWRITE_TAC[SQRT_MUL;REAL_MUL_ASSOC;GSYM REAL_POW_2;REAL_SQRT_POW_2]);;

let HNORM_NEG = prove
    (`!A::(N)homo. hnorm(--A) = hnorm A`,
    REWRITE_TAC[hnorm;HIP_LNEG;HIP_RNEG;REAL_NEG_NEG]);;  

let HNORM_SUB_SYM = prove
    (`!A:(N)homo B. hnorm(A - B) = hnorm(B - A)`,
    METIS_TAC[HNORM_NEG; HM_NEG_SUB]);;
    
let HNORM_POW_2 = prove
    (`!A:(N)homo. hnorm(A) pow 2 = (A hip A)`,
    SIMP_TAC[hnorm; SQRT_POW_2; HIP_POS_LE]);;
    
let HNORM_EQ_0_IMP = prove
    (`!A:(N)homo. (hnorm A = &0) ==> (A = homo_mat 0)`,
    SIMP_TAC[HNORM_EQ_0]);;
    
let HNORM_LE_0 = prove
    (`!x:(N)homo. hnorm x <= &0 <=> (x = homo_mat 0)`,
    MESON_TAC[REAL_LE_ANTISYM; HNORM_EQ_0; HNORM_POS_LE]);;
    
let HNORM_LE = prove
    (`!A:(N)homo B. (hnorm A <= hnorm B) <=> ((A hip A) <= (B hip B))`,
    REWRITE_TAC[hnorm] THEN MESON_TAC[SQRT_MONO_LE_EQ; HIP_POS_LE]);;

let HNORM_LT = prove
    (`!A:(N)homo B. (hnorm A < hnorm B) <=> ((A hip A) < (B hip B))`,
    REWRITE_TAC[hnorm] THEN MESON_TAC[SQRT_MONO_LT_EQ; HIP_POS_LE]);;
    
let HNORM_EQ = prove
    (`!A:(N)homo B. (hnorm A = hnorm B) <=> ((A hip A) = (B hip B))`,
    REWRITE_TAC[GSYM REAL_LE_ANTISYM; HNORM_LE]);;

let HNORM_CAUCHY_SCHWARZ = prove
    (`!A:(N)homo B:(N)homo. (A hip B) <= hnorm(A) * hnorm(B)`,
    REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC 
     [`hnorm(A:(N)homo) = &0`; `hnorm(B:(N)homo) = &0`] THEN
    ASM_SIMP_TAC[HNORM_EQ_0_IMP; HIP_LZERO; HIP_RZERO; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    MP_TAC(ISPEC `hnorm(A:(N)homo) %%% B - hnorm(B:(N)homo) %%% A`
           HIP_POS_LE) THEN
    REWRITE_TAC[HIP_LSUB;HIP_RSUB;HIP_LMUL;HIP_RMUL] THEN
    SIMP_TAC[GSYM HNORM_POW_2;REAL_POW_2;REAL_LE_REFL] THEN
    REWRITE_TAC[HIP_SYM; REAL_ARITH
     `&0 <= A * (A * B * B - B * t) - B * (A * t - B * A * A) <=>
      A * B * t <= A * B * A * B`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_LE; HNORM_POS_LE]);;
    
let HNORM_TRIANGLE = prove
    (`!A:(N)homo B:(N)homo. hnorm(A + B) <= hnorm(A) + hnorm(B)`,
    REPEAT GEN_TAC THEN REWRITE_TAC[hnorm] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN
    SIMP_TAC[GSYM hnorm; HNORM_POS_LE; REAL_LE_ADD] THEN
    REWRITE_TAC[HIP_LADD;HIP_RADD] THEN
    REWRITE_TAC[REAL_POW_2; GSYM HNORM_POW_2] THEN 
    SIMP_TAC[HNORM_CAUCHY_SCHWARZ; HIP_SYM;REAL_ARITH
             `t <= A * B ==> (A * A + t) + (t + B * B) <= (A + B) * (A + B)`]);;
             
let REAL_ABS_HNORM = prove
    (`!x:(N)homo. abs(hnorm x) = hnorm x`,
    REWRITE_TAC[HNORM_POS_LE; REAL_ABS_REFL]);;
  
let HNORM_TRIANGLE_SUB = prove
    (`!x y:(N)homo. hnorm(x) <= hnorm(y) + hnorm(x - y)`,
    MESON_TAC[HNORM_TRIANGLE; HM_SUB_ADD2]);;
  
let HNORM_TRIANGLE_LE = prove
    (`!x y. hnorm(x) + hnorm(y) <= e ==> hnorm(x + y) <= e`,
    MESON_TAC[REAL_LE_TRANS; HNORM_TRIANGLE]);;

let HNORM_TRIANGLE_LT = prove
    (`!x y. hnorm(x) + hnorm(y) < e ==> hnorm(x + y) < e`,
    MESON_TAC[REAL_LET_TRANS; HNORM_TRIANGLE]);;
  
let REAL_ABS_SUB_HNORM = prove
    (`abs(hnorm(x) - hnorm(y)) <= hnorm(x - y)`,
    REWRITE_TAC[REAL_ARITH `abs(x - y) <= a <=> x <= y + a /\ y <= x + a`] THEN
    MESON_TAC[HNORM_TRIANGLE_SUB; HNORM_SUB_SYM]);;
             
let HNORM_EQ_SQRT_NORM_FNORM = prove
    (`!A:(N)homo. hnorm A = sqrt ((norm(FST (homo_pair A))) pow 2 + (fnorm(SND (homo_pair A))) pow 2)`,
    SIMP_TAC[hnorm;hip;NORM_POW_2;FNORM_ON_MIP;SQRT_POW_2;MIP_POS_LE]);;
    
let FST_LE_HNORM = prove
    (`!A:(N)homo. norm(FST (homo_pair A)) <= hnorm A`,
    GEN_TAC THEN REWRITE_TAC[HNORM_EQ_SQRT_NORM_FNORM] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN
    SIMP_TAC[REAL_LE_ADDR;FNORM_POW_2;TRACE_TRANSP_POS_LE]);;
    
let SND_LE_HNORM = prove
    (`!A:(N)homo. fnorm(SND (homo_pair A)) <= hnorm A`,
    GEN_TAC THEN REWRITE_TAC[HNORM_EQ_SQRT_NORM_FNORM] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN
    SIMP_TAC[REAL_LE_ADDL;NORM_POS_LE;REAL_POW_LE]);;
    
let HNORM_LE_PAIR = prove
    (`!A:(N)homo. hnorm A <= norm(FST (homo_pair A)) + fnorm(SND (homo_pair A))`,
    let lem = prove
    (`!x y.  (&0 <= x /\ &0 <= y) ==> (&0 <= x * y)`,
    SIMP_TAC[REAL_MUL_POS_LE] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN ITAUT_TAC) in
    GEN_TAC THEN REWRITE_TAC[HNORM_EQ_SQRT_NORM_FNORM] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN
    SIMP_TAC[REAL_LE_ADD;NORM_POS_LE;FNORM_POS_LE] THEN
    REWRITE_TAC[REAL_POW_2;REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB] THEN
    SIMP_TAC[REAL_ARITH `&0 <= t ==> (A * A + B * B <= (A * A + t) + t + B * B)`;
             lem;REAL_MUL_SYM;NORM_POS_LE;FNORM_POS_LE]);;
             
let HNORM_TRIANGLE_LE_FST = prove
    (`!A:(N)homo. hnorm A <= e ==> norm(FST (homo_pair A)) <= e`,
    MESON_TAC[REAL_LE_TRANS; FST_LE_HNORM]);;
    
let HNORM_TRIANGLE_LE_SND = prove
    (`!A:(N)homo. hnorm A <= e ==> fnorm(SND (homo_pair A)) <= e`,
    MESON_TAC[REAL_LE_TRANS; SND_LE_HNORM]);;

let HNORM_TRIANGLE_LT_FST = prove
    (`!A:(N)homo. hnorm A < e ==> norm(FST (homo_pair A)) < e`,
    MESON_TAC[REAL_LET_TRANS; FST_LE_HNORM]);;
    
let HNORM_TRIANGLE_LT_SND = prove
    (`!A:(N)homo. hnorm A < e ==> fnorm(SND (homo_pair A)) < e`,
    MESON_TAC[REAL_LET_TRANS; SND_LE_HNORM]);;
    
let HNORM_TRIANGLE_LE_PAIR = prove
    (`!A:(N)homo.
    norm(FST (homo_pair A)) + fnorm(SND (homo_pair A)) <= e ==> hnorm A <= e`,
    MESON_TAC[REAL_LE_TRANS; HNORM_LE_PAIR]);;
    
let HNORM_TRIANGLE_LT_PAIR = prove
    (`!A:(N)homo.
    norm(FST (homo_pair A)) + fnorm(SND (homo_pair A)) < e ==> hnorm A < e`,
    MESON_TAC[REAL_LET_TRANS; HNORM_LE_PAIR]);;

let HNORM_TRIANGLE_HALF_LE_PAIR = prove
    (`!A:(N)homo. norm(FST (homo_pair A)) <= e / &2 /\ fnorm(SND (homo_pair A)) <= e / &2 ==> hnorm A <= e`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HNORM_TRIANGLE_LE_PAIR THEN
    ASM_MESON_TAC[REAL_HALF; REAL_LE_ADD2;
                  HNORM_TRIANGLE_LE_FST;HNORM_TRIANGLE_LE_SND]);;
    
let HNORM_TRIANGLE_HALF_LT_PAIR = prove
    (`!A:(N)homo. norm(FST (homo_pair A)) < e / &2 /\ fnorm(SND (homo_pair A)) < e / &2 ==> hnorm A < e`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HNORM_TRIANGLE_LT_PAIR THEN
    ASM_MESON_TAC[REAL_HALF; REAL_LT_ADD2;
                  HNORM_TRIANGLE_LT_FST;HNORM_TRIANGLE_LT_SND]);;
 
(* ------------------------------------------------------------------------- *)
(* homogeneous transformation of matrix                                      *)
(* ------------------------------------------------------------------------- *)
    
override_interface("homo_dist",`hdistance:(N)homo#(N)homo->real`);;

let homo_dist = new_definition
  `homo_dist(A,B) = hnorm(A - B)`;;
  
let HM_DIST_NEG = prove
    (`!A:(N)homo B. homo_dist (--A, --B) = homo_dist (A,B)`,
    REWRITE_TAC [homo_dist; HM_SUB_NEG2; HNORM_SUB_SYM]);;
 
let HM_DIST_REFL = prove
    (`!A:(N)homo. homo_dist(A,A) = &0`,
    SIMP_TAC[homo_dist; HM_SUB_REFL; HNORM_0]);;

let HM_DIST_POS_LE = prove
    (`!A:(N)homo B. &0 <= homo_dist(A,B)`,
    REWRITE_TAC [homo_dist;HNORM_POS_LE]);;
 
let HM_DIST_EQ_0 = prove
    (`!A:(N)homo B. (homo_dist(A,B) = &0) <=> (A = B)`,
    REPEAT GEN_TAC THEN METIS_TAC[homo_dist;HNORM_EQ_0;HM_SUB_EQ]);;
  
let HM_DIST_SYM = prove
    (`!A:(N)homo B. homo_dist(A,B) = homo_dist(B,A)`,
    REPEAT GEN_TAC THEN METIS_TAC[homo_dist;HNORM_SUB_SYM]);;
   
let REAL_ABS_HM_DIST = prove
    (`!A B:(N)homo. abs(homo_dist(A,B)) = homo_dist(A,B)`,
    REPEAT GEN_TAC THEN METIS_TAC[homo_dist;REAL_ABS_REFL;HNORM_POS_LE]);;

let HM_DIST_NZ = prove
    (`!A:(N)homo B. ~(A = B) <=> &0 < homo_dist(A,B)`,
    METIS_TAC[homo_dist;HM_SUB_EQ;HNORM_POS_LT]);;
  
let HM_DIST_POS_LT = prove
    (`!A:(N)homo B. ~(A = B) ==> &0 < homo_dist(A,B)`,
    METIS_TAC[HM_DIST_NZ]);;
    
let HM_DIST_TRIANGLE = prove
    (`!A:(N)homo B C. homo_dist(A,C) <= homo_dist(A,B) + homo_dist(B,C)`,
    let HM_SUB_TRANS = prove
    (`!A:(N)homo B C. A - C = (A - B) + (B - C)`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[homo_sub;homo_add;HOMO_PAIR;HOMO_PAIR_BIJ;PAIR_EQ] THEN
    CONJ_TAC THENL [VECTOR_ARITH_TAC;MATRIX_ARITH_TAC]) in
    REPEAT GEN_TAC THEN SIMP_TAC[homo_dist] THEN 
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [HM_SUB_TRANS] THEN 
    SIMP_TAC[HNORM_TRIANGLE]);;
    
let HM_DIST_TRIANGLE_ALT = prove
    (`!A:(N)homo B C. homo_dist(B,C) <= homo_dist(A,B) + homo_dist(A,C)`,
    METIS_TAC[HM_DIST_SYM;HM_DIST_TRIANGLE]);; 
  
let HM_DIST_TRIANGLE_LE = prove
    (`!A:(N)homo B C e. homo_dist(A,C) + homo_dist(B,C) <= e ==>
                      homo_dist(A,B) <= e`,
    METIS_TAC [HM_DIST_SYM;REAL_LE_TRANS;HM_DIST_TRIANGLE]);;
  
let HM_DIST_TRIANGLE_LT = prove
    (`!A:(N)homo B C e. homo_dist(A,C) + homo_dist(B,C) < e ==>
                      homo_dist(A,B) < e`,
    METIS_TAC [HM_DIST_SYM;REAL_LET_TRANS;HM_DIST_TRIANGLE]);;
  
let HM_DIST_TRIANGLE_HALF_L = prove
    (`!A1:(N)homo A2 B. homo_dist(A1,B) < e / &2 /\ homo_dist(A2,B) < e / &2 
                     ==> homo_dist(A1,A2) < e`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HM_DIST_TRIANGLE_LT THEN
    EXISTS_TAC `B:(N)homo` THEN ASM_MESON_TAC [REAL_HALF; REAL_LT_ADD2]);;
  
let HM_DIST_TRIANGLE_HALF_R = prove
    (`!A1:(N)homo A2 B. homo_dist(B,A1) < e / &2 /\ homo_dist(B,A2) < e / &2 
                     ==> homo_dist(A1,A2) < e`,
    METIS_TAC [HM_DIST_SYM;HM_DIST_TRIANGLE_HALF_L]);;
  
let HM_DIST_TRIANGLE_ADD = prove
    (`!A:(N)homo A' B B'. homo_dist(A + B,A' + B') <= 
                         homo_dist(A,A') + homo_dist(B,B')`,
    let HM_SUB_TRANS = prove
    (`!A:(N)homo A' B B'. (A + B) - (A' + B') = (A - A') + (B - B')`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[homo_sub;homo_add;HOMO_PAIR;HOMO_PAIR_BIJ;PAIR_EQ] THEN
    CONJ_TAC THENL [VECTOR_ARITH_TAC;MATRIX_ARITH_TAC]) in
    REPEAT GEN_TAC THEN SIMP_TAC[homo_dist] THEN 
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [HM_SUB_TRANS] THEN 
    SIMP_TAC[HNORM_TRIANGLE]);;
  
let HM_DIST_TRIANGLE_ADD_HALF = prove
    (`!A A' B B':(N)homo.
        homo_dist(A,A') < e / &2 /\ homo_dist(B,B') < e / &2 ==> 
        homo_dist(A + B,A' + B') < e`,
    REPEAT GEN_TAC THEN INTRO_TAC "h" THEN 
    FIRST_ASSUM (MP_TAC o MATCH_MP REAL_LT_ADD2) THEN
    METIS_TAC [REAL_HALF;HM_DIST_TRIANGLE_ADD; REAL_LET_TRANS]);;
    
let HM_DIST_TRIANGLE_SUB = prove
    (`!A:(N)homo A' B B'. 
        homo_dist(A - B,A' - B') <= homo_dist(A,A') + homo_dist(B,B')`,
    METIS_TAC[HM_DIST_TRIANGLE_ADD; HM_DIST_NEG; HM_SUB]);;
  
let HM_DIST_TRIANGLE_SUB_HALF = prove
    (`!A A' B B':(N)homo.
        homo_dist(A,A') < e / &2 /\ homo_dist(B,B') < e / &2 ==> 
        homo_dist(A - B,A' - B') < e`,
    REPEAT GEN_TAC THEN INTRO_TAC "h" THEN 
    FIRST_ASSUM (MP_TAC o MATCH_MP REAL_LT_ADD2) THEN
    METIS_TAC [REAL_HALF;HM_DIST_TRIANGLE_SUB; REAL_LET_TRANS]);;
    
let HM_DIST_MUL = prove
    (`!A:(N)homo B c. homo_dist(c %%% A,c %%% B) = abs(c) * homo_dist(A,B)`,
    REWRITE_TAC[homo_dist; GSYM HM_CMUL_SUB_LDISTRIB; HNORM_MUL]);;

let HM_DIST_LE_0 = prove
    (`!A:(N)homo B. homo_dist(A,B) <= &0 <=> A = B`,
    METIS_TAC[HM_DIST_POS_LE;REAL_LE_ANTISYM;HM_DIST_EQ_0]);;

let HM_DIST_EQ = prove
    (`!A:(N)homo B C D. homo_dist(A,B) = homo_dist(C,D) 
         <=> homo_dist(A,B) pow 2 = homo_dist(C,D) pow 2`,
    REWRITE_TAC[homo_dist; HNORM_POW_2; HNORM_EQ]);;

let HM_DIST_0 = prove
    (`!A:(N)homo.
        homo_dist(A,homo_mat 0) = hnorm A /\ homo_dist(homo_mat 0,A) = hnorm A`,
    METIS_TAC[homo_dist;HM_SUB_RZERO;HM_SUB_LZERO;HM_DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* homogeneous space                                                         *)
(* ------------------------------------------------------------------------- *)

let homo_open = new_definition
  `homo_open s <=> !A:(N)homo. A IN s ==>
        ?e. &0 < e /\ !A'. homo_dist(A',A) < e ==> A' IN s`;;
        
let homo_space = new_definition
 `homo_space = topology homo_open`;;
 
let homo_space_metric = new_definition
  `homo_space_metric = metric ((:(N)homo), homo_dist)`;;
  
let HOMO_OPEN_EMPTY = prove
 (`homo_open {}`,
  REWRITE_TAC[homo_open; NOT_IN_EMPTY]);;

let HOMO_OPEN_UNIV = prove
    (`homo_open(:(N)homo)`,
    REWRITE_TAC[homo_open; IN_UNIV] THEN MESON_TAC[REAL_LT_01]);;
  
let HOMO_OPEN_UNIONS = prove
    (`(!s. s IN f ==> homo_open s) ==> homo_open(UNIONS f)`,
    REWRITE_TAC[homo_open; IN_UNIONS] THEN MESON_TAC[]);;
  
let HOMO_SPACE_METRIC = prove
    (`mdist (homo_space_metric:((N)homo)metric) = homo_dist /\
    mspace homo_space_metric = (:(N)homo)`,
    SUBGOAL_THEN `is_metric_space ((:(N)homo),homo_dist)` MP_TAC THENL
    [REWRITE_TAC[is_metric_space; IN_UNIV; HM_DIST_POS_LE; HM_DIST_EQ_0;
                 HM_DIST_SYM; HM_DIST_TRIANGLE];
    SIMP_TAC[homo_space_metric; MDIST; MSPACE]]);;
   
let OPEN_IN_HOMO_SPACE_METRIC = prove
    (`open_in (mtopology homo_space_metric) = homo_open:((N)homo->bool)->bool`,
    REWRITE_TAC[FUN_EQ_THM; OPEN_IN_MTOPOLOGY; homo_open; HOMO_SPACE_METRIC;
                SUBSET_UNIV; SUBSET; IN_MBALL; IN_UNIV; HM_DIST_SYM]);;
              
let OPEN_IN_HOMO_SPACE = prove
    (`open_in homo_space = homo_open`,
    REWRITE_TAC[homo_space; GSYM OPEN_IN_HOMO_SPACE_METRIC] THEN
    MESON_TAC[topology_tybij]);;
  
let HOMO_OPEN_IN = prove
    (`!s:(N)homo->bool. homo_open s <=> open_in homo_space s`,
    REWRITE_TAC[OPEN_IN_HOMO_SPACE]);;
  
let HOMO_OPEN_SUBOPEN = prove
    (`!s:(N)homo->bool. homo_open s <=> !x. x IN s ==> ?t. homo_open t /\ x IN t /\ t SUBSET s`,
    REWRITE_TAC[HOMO_OPEN_IN; GSYM OPEN_IN_SUBOPEN]);;
  
let MTOPOLOGY_HOMO_SPACE_METRIC = prove
    (`mtopology homo_space_metric = homo_space:((N)homo)topology`,
    REWRITE_TAC[TOPOLOGY_EQ; OPEN_IN_HOMO_SPACE_METRIC; HOMO_OPEN_IN]);;
  
let TOPSPACE_HOMO_SPACE = prove
    (`topspace homo_space = (:(N)homo)`,
    REWRITE_TAC[topspace; EXTENSION; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
    MESON_TAC[HOMO_OPEN_UNIV; IN_UNIV; HOMO_OPEN_IN]);;
  
let TOPSPACE_HOMO_SPACE_SUBTOPOLOGY = prove
    (`!s:(N)homo->bool. topspace (subtopology homo_space s) = s`,
    REWRITE_TAC[TOPSPACE_HOMO_SPACE; TOPSPACE_SUBTOPOLOGY; INTER_UNIV]);;
    
let HOMO_OPEN_IN_OPEN = prove
    (`!s:(N)homo->bool u.
        open_in (subtopology homo_space u) s <=> 
                 ?t. homo_open t /\ (s = u INTER t)`,
    REPEAT STRIP_TAC THEN 
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; GSYM HOMO_OPEN_IN] THEN
    REWRITE_TAC[INTER_ACI]);;

(* ------------------------------------------------------------------------- *)
(* Closed sets in homogeneous space                                               *)
(* ------------------------------------------------------------------------- *)

let homo_closed = new_definition
  `homo_closed(s:(N)homo->bool) <=> homo_open(UNIV DIFF s)`;;
  
let HOMO_CLOSED_IN = prove
    (`!s:(N)homo->bool. homo_closed s <=> closed_in homo_space s`,
    REWRITE_TAC[homo_closed; closed_in; TOPSPACE_HOMO_SPACE; 
                HOMO_OPEN_IN; SUBSET_UNIV]);;

let CLOSED_IN_HOMO_SPACE = prove
    (`closed_in homo_space = homo_closed:((N)homo->bool)->bool`,
    REWRITE_TAC[HOMO_CLOSED_IN; FUN_EQ_THM]);;
  
let HOMO_CLOSED_INTERS = prove
    (`!f. (!s:(N)homo->bool. s IN f ==> homo_closed s) 
            ==> homo_closed(INTERS f)`,
    REWRITE_TAC[HOMO_CLOSED_IN] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `f:((N)homo->bool)->bool = {}` THEN
    ASM_SIMP_TAC[CLOSED_IN_INTERS; INTERS_0] THEN
    REWRITE_TAC[GSYM TOPSPACE_HOMO_SPACE; CLOSED_IN_TOPSPACE]);;
  
let HOMO_CLOSED_EMPTY = prove
    (`homo_closed {}`,
    REWRITE_TAC[HOMO_CLOSED_IN; CLOSED_IN_EMPTY]);;
  
let HOMO_CLOSED_INTER = prove
    (`!s t. homo_closed s /\ homo_closed t ==> homo_closed(s INTER t)`,
    REWRITE_TAC[HOMO_CLOSED_IN; CLOSED_IN_INTER]);;
  
let HOMO_CLOSED_UNIV = prove
    (`homo_closed(UNIV:(N)homo->bool)`,
    REWRITE_TAC[HOMO_CLOSED_IN; GSYM TOPSPACE_HOMO_SPACE; CLOSED_IN_TOPSPACE]);;
  
let HOMO_CLOSED_IN_CLOSED = prove
    (`!s:(N)homo->bool u.
        closed_in (subtopology homo_space u) s <=> 
            ?t. homo_closed t /\ (s = u INTER t)`,
    REPEAT STRIP_TAC THEN 
    REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY; GSYM HOMO_CLOSED_IN] THEN
    REWRITE_TAC[INTER_ACI]);;
  
let HOMO_CLOSED_IN_CLOSED_TRANS = prove
    (`!s t. closed_in (subtopology homo_space t) s /\ homo_closed t 
         ==> homo_closed s`,
    REWRITE_TAC[ONCE_REWRITE_RULE[GSYM SUBTOPOLOGY_UNIV] HOMO_CLOSED_IN] THEN
    REWRITE_TAC[CLOSED_IN_TRANS]);;
  
let HOMO_CLOSED_IN_CLOSED_INTER = prove
    (`!u s. homo_closed s ==> closed_in (subtopology homo_space u) (u INTER s)`,
    REWRITE_TAC[HOMO_CLOSED_IN_CLOSED] THEN MESON_TAC[]);;
  
let HOMO_CLOSED_DIFF = prove
    (`!s t. homo_closed s /\ homo_open t ==> homo_closed(s DIFF t)`,
    REWRITE_TAC[HOMO_OPEN_IN; HOMO_CLOSED_IN; CLOSED_IN_DIFF]);;

(* ------------------------------------------------------------------------- *)
(* Open and closed balls and spheres in homogeneous space                         *)
(* ------------------------------------------------------------------------- *)

let homo_ball = new_definition
  `!x:(N)homo. homo_ball(x,e) = { y | homo_dist(x,y) < e}`;;
  
let IN_HOMO_BALL = prove
    (`!x:(N)homo y e. y IN homo_ball(x,e) <=> homo_dist(x,y) < e`,
    REWRITE_TAC[homo_ball; IN_ELIM_THM]);;
  
let MBALL_HOMO_SPACE = prove
    (`!x:(N)homo r. mball homo_space_metric (x,r) = homo_ball(x,r)`,
    REWRITE_TAC[EXTENSION; IN_MBALL; IN_HOMO_BALL; 
                HOMO_SPACE_METRIC; IN_UNIV]);;
              
let homo_cball = new_definition
  `!x:(N)homo. homo_cball(x,e) = { y | homo_dist(x,y) <= e}`;;
  
let IN_HOMO_CBALL = prove
    (`!x:(N)homo y e. y IN homo_cball(x,e) <=> homo_dist(x,y) <= e`,
    REWRITE_TAC[homo_cball; IN_ELIM_THM]);;
  
let MCBALL_HOMO_SPACE = prove
    (`!x:(N)homo r. mcball homo_space_metric (x,r) = homo_cball(x,r)`,
    REWRITE_TAC[EXTENSION; IN_MCBALL; IN_HOMO_CBALL; 
                HOMO_SPACE_METRIC; IN_UNIV]);;
              
let homo_sphere = new_definition
  `!x:(N)homo. homo_sphere(x,e) = { y | homo_dist(x,y) = e}`;;
  
let IN_HOMO_SPHERE = prove
    (`!x:(N)homo y e. y IN homo_sphere(x,e) <=> homo_dist(x,y) = e`,
    REWRITE_TAC[homo_sphere; IN_ELIM_THM]);;
  
let HOMO_OPEN_BALL = prove
    (`!x:(N)homo e. homo_open(homo_ball(x,e))`,
    REWRITE_TAC[homo_open; homo_ball; IN_ELIM_THM] THEN 
    ONCE_REWRITE_TAC[HM_DIST_SYM] THEN
    MESON_TAC[REAL_SUB_LT; REAL_LT_SUB_LADD; REAL_ADD_SYM; REAL_LET_TRANS;
              HM_DIST_TRIANGLE_ALT]);;

let CENTRE_IN_HOMO_BALL = prove
    (`!x:(N)homo e. x IN homo_ball(x,e) <=> &0 < e`,
    MESON_TAC[IN_HOMO_BALL; HM_DIST_REFL]);;
  
let CENTRE_IN_HOMO_CBALL = prove
    (`!x e. x IN homo_cball(x,e) <=> &0 <= e`,
    MESON_TAC[IN_HOMO_CBALL; HM_DIST_REFL]);;
  
let HOMO_OPEN_CONTAINS_BALL = prove
    (`!s. homo_open s <=> !x. x IN s ==> ?e. &0 < e /\ homo_ball(x,e) SUBSET s`,
    REWRITE_TAC[homo_open; SUBSET; IN_HOMO_BALL] THEN 
    REWRITE_TAC[HM_DIST_SYM]);;
            
let HOMO_BALL_SUBSET_CBALL = prove
    (`!x e. homo_ball(x,e) SUBSET homo_cball(x,e)`,
    REWRITE_TAC[IN_HOMO_BALL; IN_HOMO_CBALL; SUBSET] THEN REAL_ARITH_TAC);;
  
let HOMO_OPEN_CONTAINS_CBALL = prove
    (`!s. homo_open s <=> 
            !x. x IN s ==> ?e. &0 < e /\ homo_cball(x,e) SUBSET s`,
    GEN_TAC THEN REWRITE_TAC[HOMO_OPEN_CONTAINS_BALL] THEN EQ_TAC THENL
    [ALL_TAC; ASM_MESON_TAC[SUBSET_TRANS; HOMO_BALL_SUBSET_CBALL]] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC[SUBSET; IN_HOMO_BALL; IN_HOMO_CBALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    SUBGOAL_THEN `e / &2 < e` (fun th -> ASM_MESON_TAC[th; REAL_LET_TRANS]) THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* limit of the homogeneous matrix                                           *)
(* ------------------------------------------------------------------------- *)
  
make_overloadable "->->->" `:A->B->C->bool`;;

overload_interface ("->->->",` homotendsto:(A->(N)homo)->(N)homo->(A)net->bool`);;

parse_as_infix("->->->",(12,"right"));;

let homotendsto = new_definition
  `((f:A->(N)homo) ->->-> l) net <=> !e. &0 < e ==> 
            eventually (\x. homo_dist(f(x),l) < e) net`;;
            
let homo_lim = new_definition  
   `! (f:A->(N)homo) net. homo_lim net f = (@l. (f ->->-> l) net)`;;
   
let LIMIT_HOMO_SPACE = prove
 (`!f:A->(N)homo x net. limit homo_space f x net <=> (f ->->-> x) net`,
  REWRITE_TAC[LIMIT_METRIC; GSYM MTOPOLOGY_HOMO_SPACE_METRIC] THEN
  REWRITE_TAC[HOMO_SPACE_METRIC; IN_UNIV; homotendsto]);;
  
let HOMO_LIM_UNIQUE = prove
 (`!net:(A)net f:A->(N)homo l:(N)homo l'.
      ~(trivial_limit net) /\ (f ->->-> l) net /\ (f ->->-> l') net ==> (l = l')`,
  REWRITE_TAC[GSYM LIMIT_HOMO_SPACE; GSYM MTOPOLOGY_HOMO_SPACE_METRIC] THEN
  REWRITE_TAC[LIMIT_METRIC_UNIQUE]);;
  
let HOMO_LIM_SEQUENTIALLY = prove
 (`!s l:(N)homo. (s ->->-> l) sequentially <=>
          !e. &0 < e ==> ?N. !n. N <= n ==> homo_dist(s(n),l) < e`,
  REWRITE_TAC[homotendsto; EVENTUALLY_SEQUENTIALLY] THEN MESON_TAC[]);;
  
let HOMO_LIM_EQ_PAIR_LIM = prove
    (`!s:A->(N)homo l:(N)homo. (s ->->-> l) net <=>
        (((\x. FST (homo_pair (s x))) --> (FST (homo_pair l))) net /\
         ((\x. SND (homo_pair (s x))) ->-> (SND (homo_pair l))) net)`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[homotendsto;matrixtendsto;tendsto] THEN
    REWRITE_TAC[homo_dist;matrix_dist;dist;GSYM HOMO_PAIR_SUB] THEN
    EQ_TAC THENL
    [MESON_TAC[EVENTUALLY_MONO;HNORM_TRIANGLE_LT_FST;HNORM_TRIANGLE_LT_SND];
     ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF;GSYM IMP_CONJ;GSYM EVENTUALLY_AND] THEN
    MESON_TAC[EVENTUALLY_MONO;HNORM_TRIANGLE_HALF_LT_PAIR]);;
    
let HOMO_LIM_EQ_ALT = prove
    (`!x:num->real^N R:num->real^N^N x1 R1 net. 
        ((\n. homo_trans (x n) (R n)) ->-> (homo_trans x1 R1)) net <=> 
         ((\n. homo (homo_trans (x n) (R n))) ->->-> (homo (homo_trans x1 R1))) net`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[HOMO_LIM_EQ_PAIR_LIM;matrixtendsto;tendsto] THEN
    REWRITE_TAC[HOMO_PAIR;FST;SND] THEN EQ_TAC THENL 
    [MESON_TAC[EVENTUALLY_MONO;HOMO_TRANS_DIST_TRIANGLE_LT_FST;
               HOMO_TRANS_DIST_TRIANGLE_LT_SND]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF;GSYM IMP_CONJ;GSYM EVENTUALLY_AND] THEN
    MESON_TAC[EVENTUALLY_MONO;HOMO_TRANS_DIST_TRIANGLE_HALF_LT]);;
    
let LIMIT_HOMO_SPACE_EQ_PAIR_SPACE = prove
    (`!f:A->(N)homo l net. 
        limit homo_space f l net <=>
        limit euclidean (\x. FST (homo_pair (f x))) (FST (homo_pair l)) net /\
        limit matrix_space (\x. SND (homo_pair (f x))) (SND (homo_pair l)) net`,
    REWRITE_TAC[LIMIT_HOMO_SPACE;LIMIT_MATRIX_SPACE;LIMIT_EUCLIDEAN;HOMO_LIM_EQ_PAIR_LIM]);;      

let HOMO_LIMIT_COMPONENTWISE_REAL = prove
    (`!net (f:A->(N)homo) l.
     limit homo_space f l net <=>
    (!i. 1 <= i /\ i <= dimindex (:N)
        ==> limit euclideanreal (\x. FST (homo_pair (f x))$i) (FST (homo_pair l)$i)
                  net) /\
    (!i j. (1 <= i /\ i <= dimindex (:N)) /\ 1 <= j /\ j <= dimindex (:N)
    ==> limit euclideanreal (\x. SND (homo_pair (f x))$i$j) (SND (homo_pair l)$i$j)
                  net)`,
    REWRITE_TAC[LIMIT_HOMO_SPACE_EQ_PAIR_SPACE;MATRIX_LIMIT_COMPONENTWISE_REAL;LIMIT_COMPONENTWISE_REAL]);;
                 
let HOMO_LIMIT_COMPONENTWISE_VECTOR = prove
    (`!net (f:A->(N)homo) l.
    limit homo_space f l net <=>
    limit euclidean (\x. FST (homo_pair (f x))) (FST (homo_pair l)) net /\
    (!i. 1 <= i /\ i <= dimindex (:N)
        ==> limit euclidean (\x. SND (homo_pair (f x))$i) (SND (homo_pair l)$i)
                  net)`,
    REWRITE_TAC[LIMIT_HOMO_SPACE_EQ_PAIR_SPACE;MATRIX_LIMIT_COMPONENTWISE_VECTOR]);;
   
let HOMO_CONTINUOUS_MAP_COMPONENTWISE_VECTOR = prove
    (`!top (f:A->(N)homo).
        continuous_map (top,homo_space) f <=>
        continuous_map (top,euclidean) (\x. FST (homo_pair (f x))) /\
        (!i. 1 <= i /\ i <= dimindex (:N)
        ==> continuous_map (top,euclidean) (\x. SND (homo_pair (f x))$i))`,
    REWRITE_TAC[CONTINUOUS_MAP_ATPOINTOF; HOMO_LIMIT_COMPONENTWISE_VECTOR] THEN
    MESON_TAC[]);;
                         
let HOMO_LIM_COMPONENTWISE_REAL = prove
    (`!net f:A->(N)homo l.
        (f ->->-> l) net <=>
        (!i. 1 <= i /\ i <= dimindex (:N)
        ==> limit euclideanreal (\x. FST (homo_pair (f x))$i) (FST (homo_pair l)$i)
                  net) /\
    (!i j. (1 <= i /\ i <= dimindex (:N)) /\ 1 <= j /\ j <= dimindex (:N)
    ==> limit euclideanreal (\x. SND (homo_pair (f x))$i$j) (SND (homo_pair l)$i$j)
                  net)`,
    REWRITE_TAC[GSYM LIMIT_HOMO_SPACE; HOMO_LIMIT_COMPONENTWISE_REAL]);;
  
let HOMO_LIM_COMPONENTWISE_VECTOR = prove
    (`!net f:A->(N)homo l.
        (f ->->-> l) net <=>
        limit euclidean (\x. FST (homo_pair (f x))) (FST (homo_pair l)) net /\
        (!i. 1 <= i /\ i <= dimindex (:N)
        ==> limit euclidean (\x. SND (homo_pair (f x))$i) (SND (homo_pair l)$i)
                  net)`,
    REWRITE_TAC[GSYM LIMIT_HOMO_SPACE; HOMO_LIMIT_COMPONENTWISE_VECTOR]);;
    
let HOMO_LIM_CONST = prove
    (`!net A:(N)homo. ((\x:A. A) ->->-> A) net`,
    SIMP_TAC[homotendsto; HM_DIST_REFL; EVENTUALLY_TRUE]);;
  
let HOMO_LIM_CMUL = prove
    (`!net:(A)net f:A->(N)homo l c.
        (f ->->-> l) net ==> ((\x. c %%% f x) ->->-> c %%% l) net`,
    REWRITE_TAC[HOMO_LIM_COMPONENTWISE_REAL;HOMO_PAIR_CMUL;
                MATRIX_CMUL_COMPONENT;VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[LIMIT_REAL_LMUL]);;
  
let HOMO_LIM_CMUL_EQ = prove
    (`!net:(A)net f:A->(N)homo l c.
        ~(c = &0) ==> (((\x. c %%% f x) ->->-> c %%% l) net <=> (f ->->-> l) net)`,
    REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[HOMO_LIM_CMUL] THEN
    DISCH_THEN(MP_TAC o SPEC `inv c:real` o MATCH_MP HOMO_LIM_CMUL) THEN
    ASM_SIMP_TAC[HM_CMUL_ASSOC; REAL_MUL_LINV; HM_CMUL_LID; ETA_AX]);;
  
let HOMO_LIM_NEG = prove
    (`!net:(A)net f:A->(N)homo l. 
        (f ->->-> l) net ==> ((\x. --(f x)) ->->-> --l) net`,
    REWRITE_TAC[HOMO_LIM_COMPONENTWISE_REAL;HOMO_PAIR_NEG;MATRIX_NEG_COMPONENT;VECTOR_NEG_COMPONENT] THEN
    SIMP_TAC[LIMIT_REAL_NEG]);;
  
let HOMO_LIM_NEG_EQ = prove
    (`!net:(A)net f:A->(N)homo l. 
        ((\x. --(f x)) ->->-> --l) net <=> (f ->->-> l) net`,
    REPEAT GEN_TAC THEN EQ_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMO_LIM_NEG) THEN
    REWRITE_TAC[HM_NEG_NEG; ETA_AX]);;
  
let HOMO_LIM_ADD = prove
    (`!net:(A)net f:A->(N)homo g:A->(N)homo l m.
    (f ->->-> l) net /\ (g ->->-> m) net ==> ((\x. f(x) + g(x)) ->->-> l + m) net`,
    REWRITE_TAC[HOMO_LIM_COMPONENTWISE_REAL;HOMO_PAIR_ADD;MATRIX_ADD_COMPONENT;VECTOR_ADD_COMPONENT] THEN
    SIMP_TAC[LIMIT_REAL_ADD]);;
  
let HOMO_LIM_SUB = prove
    (`!net:(A)net f:A->(N)homo g l m.
    (f ->->-> l) net /\ (g ->->-> m) net ==> ((\x. f(x) - g(x)) ->->-> l - m) net`,
    REWRITE_TAC[HM_SUB] THEN ASM_SIMP_TAC[HOMO_LIM_ADD; HOMO_LIM_NEG]);;

let HOMO_LIM_TRANSFORM = prove
    (`!net:(A)net f:A->(N)homo g l.
        ((\x. f x - g x) ->->-> homo_mat 0) net /\ (f ->->-> l) net
        ==> (g ->->-> l) net`,
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP HOMO_LIM_SUB) THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMO_LIM_NEG) THEN SIMP_TAC[HM_SUB_SUB;HM_SUB_LZERO;HM_NEG_NEG] THEN
    MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN BINOP_TAC THEN REWRITE_TAC[FUN_EQ_THM]);;

let HOMO_LIM_EVENTUALLY = prove
    (`!net:(A)net f:A->(N)homo l. eventually (\x. f x = l) net ==> (f ->->-> l) net`,
    SIMP_TAC[homotendsto] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        EVENTUALLY_MONO)) THEN
    ASM_SIMP_TAC[HM_DIST_REFL]);;
  
let HOMO_LIM_TRANSFORM_EVENTUALLY = prove
    (`!net:(A)net f:A->(N)homo g l.
        eventually (\x. f x = g x) net /\ (f ->->-> l) net ==> (g ->->-> l) net`,
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM HM_SUB_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP HOMO_LIM_EVENTUALLY) MP_TAC) THEN
    MESON_TAC[HOMO_LIM_TRANSFORM]);;
  
let HOMO_LIM_HNORM_UBOUND = prove
    (`!net:(A)net f (l:(N)homo) b.
      ~(trivial_limit net) /\
      (f ->->-> l) net /\
      eventually (\x. hnorm(f x) <= b) net
      ==> hnorm(l) <= b`,
    let th1 = MESON [HM_SUB_ADD] `!x:(N)homo y. x = (x - y) + y` in
    let th2 = SPECL [`l:(N)homo`; `f(x:A):(N)homo`] th1 in
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISJ_CASES_TAC(REAL_ARITH `hnorm(l:(N)homo) <= b \/ b < hnorm l`) THEN
    ASM_REWRITE_TAC[homotendsto] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `hnorm(l:(N)homo) - b`) MP_TAC) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT; IMP_IMP; GSYM EVENTUALLY_AND] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EVENTUALLY_HAPPENS) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `b < hnorm(l:(N)homo)` THEN
    REWRITE_TAC [homo_dist] THEN ONCE_REWRITE_TAC [HNORM_SUB_SYM] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[th2] THEN 
    W(MP_TAC o PART_MATCH lhand HNORM_TRIANGLE o lhand o snd) THEN
    REWRITE_TAC[GSYM th2] THEN ASM_ARITH_TAC);;
  
let HOMO_LIM_TRIVIAL = prove
    (`!net (f:A->(N)homo) l. trivial_limit net ==> (f ->->-> l) net`,
    SIMP_TAC[GSYM LIMIT_HOMO_SPACE; LIMIT_TRIVIAL; 
             TOPSPACE_HOMO_SPACE; IN_UNIV]);;
  
let HOMO_LIM_NULL = prove
    (`!net f l. (f ->->-> l) net <=> ((\x. f(x) - l) ->->-> homo_mat 0) net`,
    REWRITE_TAC[homotendsto; homo_dist; HM_SUB_RZERO]);;
    
(* ------------------------------------------------------------------------- *)
(* limit point of homogeneous space                                          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("homo_limit_point_of",(12,"right"));;

let homo_limit_point_of = new_definition
 `!x:(N)homo. x homo_limit_point_of s <=>
        !t. x IN t /\ homo_open t ==> ?y. ~(y = x) /\ y IN s /\ y IN t`;;
        
let HOMO_LIMPT_APPROACHABLE = prove
 (`!x:(N)homo s. x homo_limit_point_of s <=>
                !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ homo_dist(x',x) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homo_limit_point_of] THEN
  MESON_TAC[homo_open; HM_DIST_SYM; HOMO_OPEN_BALL; 
            CENTRE_IN_HOMO_BALL; IN_HOMO_BALL]);;

let [HOMO_LIMPT_SEQUENTIAL; HOMO_LIMPT_SEQUENTIAL_INJ; 
     HOMO_LIMPT_SEQUENTIAL_DECREASING] =
  (CONJUNCTS o prove)
  (`(!x:(N)homo s.
        x homo_limit_point_of s <=>
        ?f. (!n. f(n) IN (s DELETE x)) /\ (f ->->-> x) sequentially) /\
    (!x:(N)homo s.
        x homo_limit_point_of s <=>
        ?f. (!n. f(n) IN (s DELETE x)) /\
            (!m n. f m = f n <=> m = n) /\
            (f ->->-> x) sequentially) /\
    (!x:(N)homo s.
        x homo_limit_point_of s <=>
        ?f. (!n. f(n) IN (s DELETE x)) /\
            (!m n. m < n ==> homo_dist(f n,x) < homo_dist(f m,x)) /\
            (f ->->-> x) sequentially)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT
   `(s ==> r) /\ (r ==> q) /\ (q ==> p) /\ (p ==> s)
    ==> (p <=> q) /\ (p <=> r) /\ (p <=> s)`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:num->(N)homo` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WLOG_LT THEN ASM_MESON_TAC[REAL_LT_REFL];
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    REWRITE_TAC[HOMO_LIMPT_APPROACHABLE; HOMO_LIM_SEQUENTIALLY; IN_DELETE] THEN
    MESON_TAC[LE_REFL];
    REWRITE_TAC[HOMO_LIMPT_APPROACHABLE] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?f:num->(N)homo.
        (!n. (f n) IN s /\ ~(f n = x) /\ homo_dist(f n,x) < inv(&n + &1)) /\
       (!n. homo_dist(f(SUC n),x) < homo_dist(f n,x))`
    MP_TAC THENL
     [MATCH_MP_TAC DEPENDENT_CHOICE THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `z:(N)homo`] THEN
      STRIP_TAC THEN REWRITE_TAC[GSYM CONJ_ASSOC; GSYM REAL_LT_MIN] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_INV_EQ; GSYM HM_DIST_NZ] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num->(N)homo` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        REWRITE_TAC[HOMO_LIM_SEQUENTIALLY] THEN MATCH_MP_TAC FORALL_POS_MONO_1 THEN
        CONJ_TAC THENL [MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
        X_GEN_TAC `N:num` THEN EXISTS_TAC `N:num` THEN
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        TRANS_TAC REAL_LTE_TRANS `inv(&n + &1)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN
        ASM_ARITH_TAC]]]);;

let HOMO_SPACE_DERIVED_SET_OF_IFF_LIMIT_POINT_OF = prove
    (`!s. homo_space derived_set_of s = 
                          {x:(N)homo | x homo_limit_point_of s}`,
    GEN_TAC THEN
    REWRITE_TAC[GSYM MTOPOLOGY_HOMO_SPACE_METRIC; METRIC_DERIVED_SET_OF;
                HOMO_SPACE_METRIC; IN_UNIV; homo_limit_point_of; EXTENSION;
                IN_ELIM_THM; MBALL_HOMO_SPACE] THEN
    GEN_TAC THEN EQ_TAC THENL
    [INTRO_TAC "hp; !t; x t" THEN HYP_TAC "t" (REWRITE_RULE[homo_open]) THEN
     HYP_TAC "t: @r. r t" (C MATCH_MP (ASSUME `x:(N)homo IN t`)) THEN
     HYP_TAC "hp: @y. neq y homo_dist" (C MATCH_MP (ASSUME `&0 < r`)) THEN
     EXISTS_TAC `y:(N)homo` THEN HYP REWRITE_TAC "neq y" [] THEN
     REMOVE_THEN "t" MATCH_MP_TAC THEN REMOVE_THEN "homo_dist" MP_TAC THEN
     REWRITE_TAC[IN_HOMO_BALL; HM_DIST_SYM];
     INTRO_TAC "hp; !r; r" THEN REMOVE_THEN "hp" MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[CENTRE_IN_HOMO_BALL; HOMO_OPEN_BALL]]);;

let HOMO_LIMIT_POINT_IN_DERIVED_SET = prove
    (`!s x:(N)homo. x homo_limit_point_of s <=> 
                  x IN homo_space derived_set_of s`,
    REWRITE_TAC[HOMO_SPACE_DERIVED_SET_OF_IFF_LIMIT_POINT_OF; IN_ELIM_THM]);;
  
let HOMO_CLOSED_LIMPT = prove
    (`!s. homo_closed s <=> !x. x homo_limit_point_of s ==> x IN s`,
    REWRITE_TAC[homo_closed] THEN ONCE_REWRITE_TAC[HOMO_OPEN_SUBOPEN] THEN
    REWRITE_TAC[homo_limit_point_of; IN_DIFF; IN_UNIV; SUBSET] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Interior of a homo set.                                                 *)
(* ------------------------------------------------------------------------- *)

let homo_interior = new_definition
  `homo_interior s = {x | ?t. homo_open t /\ x IN t /\ t SUBSET s}`;;
  
let HOMO_SPACE_INTERIOR_OF = prove
 (`!s:(N)homo->bool. homo_space interior_of s = homo_interior s`,
  REWRITE_TAC[interior_of; homo_interior; HOMO_OPEN_IN]);;
  
let HOMO_INTERIOR_EQ = prove
 (`!s:(N)homo->bool. (homo_interior s = s) <=> homo_open s`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; homo_interior; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [HOMO_OPEN_SUBOPEN] THEN MESON_TAC[SUBSET]);;
  
let HOMO_OPEN_INTERIOR = prove
 (`!s:(N)homo->bool. homo_open(homo_interior s)`,
  GEN_TAC THEN REWRITE_TAC[homo_interior] THEN 
  GEN_REWRITE_TAC I [HOMO_OPEN_SUBOPEN] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;
  
let HOMO_INTERIOR_OPEN = prove
 (`!s:(N)homo->bool. homo_open s ==> (homo_interior s = s)`,
  MESON_TAC[HOMO_INTERIOR_EQ]);;
  
let HOMO_INTERIOR_EMPTY = prove
 (`homo_interior {} = {}`,
  SIMP_TAC[HOMO_INTERIOR_OPEN; HOMO_OPEN_EMPTY]);;
  
let HOMO_INTERIOR_SUBSET = prove
 (`!s:(N)homo->bool. (homo_interior s) SUBSET s`,
  REWRITE_TAC[SUBSET; homo_interior; IN_ELIM_THM] THEN MESON_TAC[]);;
  
let HOMO_INTERIOR_MAXIMAL = prove
 (`!s t. t SUBSET s /\ homo_open t ==> t SUBSET (homo_interior s)`,
  REWRITE_TAC[homo_interior; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;
  
let HOMO_INTERIOR_UNIQUE = prove
 (`!s t:(N)homo->bool. t SUBSET s /\ homo_open t /\ 
         (!t'. t' SUBSET s /\ homo_open t' ==> t' SUBSET t)
         ==> (homo_interior s = t)`,
  MESON_TAC[SUBSET_ANTISYM; HOMO_INTERIOR_MAXIMAL; HOMO_INTERIOR_SUBSET;
            HOMO_OPEN_INTERIOR]);;
            
let IN_HOMO_INTERIOR = prove
 (`!x s. x IN homo_interior s <=> ?e. &0 < e /\ homo_ball(x,e) SUBSET s`,
  REWRITE_TAC[homo_interior; IN_ELIM_THM] THEN
  MESON_TAC[HOMO_OPEN_CONTAINS_BALL; SUBSET_TRANS; 
            CENTRE_IN_HOMO_BALL; HOMO_OPEN_BALL]);;
    
(* ------------------------------------------------------------------------- *)
(* Closure of a set in homogeneous space                                                        *)
(* ------------------------------------------------------------------------- *)

let homo_closure = new_definition
  `homo_closure s = s UNION {x:(N)homo | x homo_limit_point_of s}`;;
  
let HOMO_SPACE_CLOSURE_OF = prove
    (`!s:(N)homo->bool. homo_space closure_of s = homo_closure s`,
    GEN_TAC THEN
    REWRITE_TAC[homo_closure; CLOSURE_OF; TOPSPACE_HOMO_SPACE; INTER_UNIV;
                HOMO_SPACE_DERIVED_SET_OF_IFF_LIMIT_POINT_OF]);;

let HOMO_CLOSURE_INTERIOR = prove
    (`!s:(N)homo->bool. homo_closure s = UNIV DIFF (homo_interior (UNIV DIFF s))`,
    REWRITE_TAC[EXTENSION; homo_closure; IN_UNION; IN_DIFF; IN_UNIV; homo_interior;
                IN_ELIM_THM; homo_limit_point_of; SUBSET] THEN
    MESON_TAC[]);;
               
let HOMO_CLOSED_CLOSURE = prove
    (`!s:(N)homo->bool. homo_closed(homo_closure s)`,
    REWRITE_TAC[homo_closed; HOMO_CLOSURE_INTERIOR; 
                COMPL_COMPL; HOMO_OPEN_INTERIOR]);;
  
let HOMO_CLOSURE_SEQUENTIAL = prove
    (`!s l:(N)homo.
     l IN homo_closure(s) <=> ?x. (!n. x(n) IN s) /\ (x ->->-> l) sequentially`,
    REWRITE_TAC[homo_closure; IN_UNION; HOMO_LIMPT_SEQUENTIAL; 
                IN_ELIM_THM; IN_DELETE] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
    `((b ==> c) /\ (~a /\ c ==> b)) /\ (a ==> c) ==> (a \/ b <=> c)`) THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    EXISTS_TAC `\n:num. l:(N)homo` THEN
    ASM_REWRITE_TAC[HOMO_LIM_CONST]);;
  
let HOMO_CLOSURE_HULL = prove
    (`!s. homo_closure s = homo_closed hull s`,
    GEN_TAC THEN MATCH_MP_TAC(GSYM HULL_UNIQUE) THEN
    REWRITE_TAC[HOMO_CLOSED_CLOSURE; SUBSET] THEN
    REWRITE_TAC[homo_closure; IN_UNION; IN_ELIM_THM; HOMO_CLOSED_LIMPT] THEN
    MESON_TAC[homo_limit_point_of]);;
  
let HOMO_CLOSURE_EQ = prove
    (`!s. (homo_closure s = s) <=> homo_closed s`,
    SIMP_TAC[HOMO_CLOSURE_HULL; HULL_EQ; HOMO_CLOSED_INTERS]);;
  
let HOMO_CLOSURE_CLOSED = prove
    (`!s. homo_closed s ==> (homo_closure s = s)`,
    MESON_TAC[HOMO_CLOSURE_EQ]);;
  
let HOMO_CLOSURE_EMPTY = prove
    (`homo_closure {} = {}`,
    SIMP_TAC[HOMO_CLOSURE_CLOSED; HOMO_CLOSED_EMPTY]);;
  
let HOMO_CLOSURE_SUBSET = prove
    (`!s. s SUBSET (homo_closure s)`,
    REWRITE_TAC[HOMO_CLOSURE_HULL; HULL_SUBSET]);;
  
let HOMO_CLOSURE_MINIMAL = prove
    (`!s t. s SUBSET t /\ homo_closed t ==> (homo_closure s) SUBSET t`,
    REWRITE_TAC[HULL_MINIMAL; HOMO_CLOSURE_HULL]);;
  
let HOMO_CLOSED_SEQUENTIAL_LIMITS = prove
    (`!s:(N)homo->bool. homo_closed s <=>
       !x l. (!n. x(n) IN s) /\ (x ->->-> l) sequentially ==> l IN s`,
    MESON_TAC[HOMO_CLOSURE_SEQUENTIAL; HOMO_CLOSURE_CLOSED;
              HOMO_CLOSED_LIMPT; HOMO_LIMPT_SEQUENTIAL; IN_DELETE]);;

(* ------------------------------------------------------------------------- *)
(* Compactness of the homogeneous space 
       (the definition is the one based on convegent subsequences).          *)
(* ------------------------------------------------------------------------- *)

let homo_compact = new_definition
  `homo_compact s <=>
        !f:num->(N)homo.
            (!n. f(n) IN s)
            ==> ?l r. l IN s /\ (!m n:num. m < n ==> r(m) < r(n)) /\
                      ((f o r) ->->-> l) sequentially`;;
                                            
let HOMO_COMPACT_EMPTY = prove
 (`homo_compact {}`,
  REWRITE_TAC[homo_compact; NOT_IN_EMPTY]);;
                      
let COMPACT_IN_HOMO_SPACE = prove
 (`!s:(N)homo->bool. compact_in homo_space s <=> homo_compact s`,
  REWRITE_TAC[homo_compact; GSYM LIMIT_HOMO_SPACE] THEN
  REWRITE_TAC[GSYM MTOPOLOGY_HOMO_SPACE_METRIC; COMPACT_IN_SEQUENTIALLY] THEN
  REWRITE_TAC[homo_compact; HOMO_SPACE_METRIC; SUBSET_UNIV]);;
    
let HOMO_COMPACT_IMP_CLOSED = prove
 (`!s:(N)homo->bool. homo_compact s ==> homo_closed s`,
  GEN_TAC THEN REWRITE_TAC[HOMO_CLOSED_IN; GSYM COMPACT_IN_HOMO_SPACE] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] COMPACT_IN_IMP_CLOSED_IN) THEN
  REWRITE_TAC[GSYM MTOPOLOGY_HOMO_SPACE_METRIC] THEN
  REWRITE_TAC[HAUSDORFF_SPACE_MTOPOLOGY]);;
  
(* ------------------------------------------------------------------------- *)
(* homogeneous space boundedness.                                                              *)
(* ------------------------------------------------------------------------- *)

let homo_bounded = new_definition
  `homo_bounded s <=> ?a. !x:(N)homo. x IN s ==> hnorm(x) <= a`;;
  
let HOMO_BOUNDED_EMPTY = prove
    (`homo_bounded {}`,
    REWRITE_TAC[homo_bounded; NOT_IN_EMPTY]);;
  
let MBOUNDED_HOMO_SPACE = prove
    (`!s:(N)homo->bool. mbounded homo_space_metric s <=> homo_bounded s`,
    let th1 = MESON [HM_SUB_ADD] `!x:(N)homo y. x = (x - y) + y` in
    let th2 = SPECL [`x:(N)homo`; `c:(N)homo`] th1 in
    let lem1 = REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS in
    let lem = ONCE_REWRITE_RULE 
           [TAUT `p ==> q ==> r <=> q ==> p ==> r`] lem1 in
    GEN_TAC THEN REWRITE_TAC[mbounded; homo_bounded; MCBALL_HOMO_SPACE] THEN
    EQ_TAC THEN REWRITE_TAC[SUBSET; IN_HOMO_CBALL; LEFT_IMP_EXISTS_THM] THENL
    [MAP_EVERY X_GEN_TAC [`c:(N)homo`; `b:real`] THEN DISCH_TAC THEN
     EXISTS_TAC `hnorm(c:(N)homo) + b`;
     X_GEN_TAC `b:real` THEN DISCH_TAC THEN
     MAP_EVERY EXISTS_TAC [`homo_mat 0:(N)homo`; `b:real`]] THEN
    POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    SIMP_TAC[homo_dist] THEN ONCE_REWRITE_TAC [HNORM_SUB_SYM] THENL
    [STRIP_TAC THEN ONCE_REWRITE_TAC [th2] THEN
     W(MP_TAC o PART_MATCH lhand HNORM_TRIANGLE o lhand o snd) THEN
     MATCH_MP_TAC lem THEN REWRITE_TAC [GSYM th2] THEN
     ASM_ARITH_TAC;
     ASM_SIMP_TAC[HM_SUB_RZERO]]);;
   
let HOMO_BOUNDED_CLOSURE = prove
    (`!s:(N)homo->bool. homo_bounded s ==> homo_bounded(homo_closure s)`,
    REWRITE_TAC[homo_bounded; HOMO_CLOSURE_SEQUENTIAL] THEN
    GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    DISCH_TAC THEN X_GEN_TAC `y:(N)homo` THEN
    DISCH_THEN(X_CHOOSE_TAC `x:num->(N)homo`) THEN
    MATCH_MP_TAC(ISPEC `sequentially` HOMO_LIM_HNORM_UBOUND) THEN
    EXISTS_TAC `x:num->(N)homo` THEN
    ASM_SIMP_TAC[EVENTUALLY_TRUE; TRIVIAL_LIMIT_SEQUENTIALLY]);;
  
let HOMO_BOUNDED_POS = prove
    (`!s:(N)homo->bool. homo_bounded s <=> 
            ?b. &0 < b /\ !x. x IN s ==> hnorm(x) <= b`,
    REWRITE_TAC[homo_bounded] THEN
    MESON_TAC[REAL_ARITH `&0 < &1 + abs(y) /\ (x <= y ==> x <= &1 + abs(y))`]);;
  
let HOMO_BOUNDED_SUBSET = prove
    (`!s t:(N)homo->bool. homo_bounded t /\ s SUBSET t ==> homo_bounded s`,
    MESON_TAC[homo_bounded; SUBSET]);;
  
let HOMO_BOUNDED_INTER = prove
    (`!s t:(N)homo->bool. homo_bounded s \/ homo_bounded t 
          ==> homo_bounded (s INTER t)`,
    MESON_TAC[HOMO_BOUNDED_SUBSET; INTER_SUBSET]);;
  
let HOMO_BOUNDED_CBALL = prove
    (`!x:(N)homo e. homo_bounded(homo_cball(x,e))`,
    let th1 = MESON [HM_SUB_ADD] `!x:(N)homo y. x = (x - y) + y` in
    let th2 = SPECL [`x':(N)homo`; `x:(N)homo`] th1 in
    REPEAT GEN_TAC THEN REWRITE_TAC[homo_bounded] THEN
    EXISTS_TAC `hnorm(x:(N)homo) + e` THEN 
    REWRITE_TAC[IN_HOMO_CBALL; homo_dist] THEN
    ONCE_REWRITE_TAC[HNORM_SUB_SYM] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `hnorm(x' - x) + hnorm((x:(N)homo))` THEN
    SIMP_TAC[th2;HNORM_TRIANGLE_SUB;REAL_ADD_SYM] THEN
    ASM_MESON_TAC[REAL_ADD_SYM;REAL_LE_ADD2;REAL_LE_REFL]);;
  
let HOMO_COMPACT_IMP_BOUNDED = prove
    (`!s:(N)homo->bool. homo_compact s ==> homo_bounded s`,
    REWRITE_TAC[GSYM COMPACT_IN_HOMO_SPACE; GSYM MBOUNDED_HOMO_SPACE] THEN
    REWRITE_TAC[GSYM MTOPOLOGY_HOMO_SPACE_METRIC; COMPACT_IN_IMP_MBOUNDED]);;
            
let HOMO_BOUNDED_UNION = prove
    (`!s:(N)homo->bool t.
        homo_bounded (s UNION t) <=> homo_bounded s /\ homo_bounded t`,
    REWRITE_TAC[homo_bounded; IN_UNION] THEN MESON_TAC[REAL_LE_MAX]);;
  
let HOMO_CLOSED_UNION = prove
    (`!s:(N)homo->bool t. homo_closed s /\ homo_closed t 
                        ==> homo_closed(s UNION t)`,
    REWRITE_TAC[HOMO_CLOSED_IN; CLOSED_IN_UNION]);;

let HOMO_COMPACT_EQ_BOLZANO_WEIERSTRASS = prove
    (`!s:(N)homo->bool.
        homo_compact s <=>
           !t. INFINITE t /\ t SUBSET s ==> 
               ?x. x IN s /\ x homo_limit_point_of t`,
    REWRITE_TAC[GSYM COMPACT_IN_HOMO_SPACE] THEN
    REWRITE_TAC[GSYM MTOPOLOGY_HOMO_SPACE_METRIC] THEN
    REWRITE_TAC[COMPACT_IN_EQ_BOLZANO_WEIERSTRASS] THEN
    REWRITE_TAC[HOMO_SPACE_METRIC; SUBSET_UNIV] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; 
                MTOPOLOGY_HOMO_SPACE_METRIC] THEN
    REWRITE_TAC[GSYM HOMO_LIMIT_POINT_IN_DERIVED_SET] THEN MESON_TAC[]);;           
           
let HOMO_BOLZANO_WEIERSTRASS_IMP_CLOSED = prove
    (`!s:(N)homo->bool.
        (!t. INFINITE t /\ t SUBSET s ==> 
         ?x. x IN s /\ x homo_limit_point_of t)
             ==> homo_closed s`,
    REWRITE_TAC[GSYM HOMO_COMPACT_EQ_BOLZANO_WEIERSTRASS; 
                HOMO_COMPACT_IMP_CLOSED]);;
           
let HOMO_FINITE_IMP_CLOSED = prove
    (`!s. FINITE s ==> homo_closed s`,
    MESON_TAC[HOMO_BOLZANO_WEIERSTRASS_IMP_CLOSED; INFINITE; FINITE_SUBSET]);;
  
let HOMO_FINITE_IMP_BOUNDED = prove
    (`!s:(N)homo->bool. FINITE s ==> homo_bounded s`,
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[HOMO_BOUNDED_EMPTY] THEN
    REWRITE_TAC[homo_bounded; IN_INSERT] THEN 
    X_GEN_TAC `x:(N)homo` THEN GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `hnorm(x:(N)homo) + abs B` THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[HNORM_POS_LE; REAL_ARITH
    `(y <= b /\ &0 <= x ==> y <= x + abs b) /\ x <= x + abs b`]);;
    
(* ------------------------------------------------------------------------- *)
(* homogeneous space completeness.                                                              *)
(* ------------------------------------------------------------------------- *)  
  
let homo_cauchy = new_definition
  `homo_cauchy (s:num->(N)homo) <=>
     !e. &0 < e ==> ?N. !m n. m >= N /\ n >= N ==> homo_dist(s m,s n) < e`;;
     
let homo_complete = new_definition
  `homo_complete s <=>
     !f:num->(N)homo. (!n. f n IN s) /\ homo_cauchy f
                      ==> ?l. l IN s /\ (f ->->-> l) sequentially`;;
     
let CAUCHY_IN_HOMO_SPACE = prove
    (`!s:num->(N)homo. cauchy_in homo_space_metric s <=> homo_cauchy s`,
    REWRITE_TAC[homo_cauchy; cauchy_in; HOMO_SPACE_METRIC; IN_UNIV; GE]);;
  
let HOMO_CAUCHY = prove
    (`!s:num->(N)homo.
      homo_cauchy s <=> !e. &0 < e ==> ?N. !n. n >= N 
            ==> homo_dist(s n,s N) < e`,
    REPEAT GEN_TAC THEN REWRITE_TAC[homo_cauchy; GE] THEN EQ_TAC THENL
    [MESON_TAC[LE_REFL]; DISCH_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    MESON_TAC[HM_DIST_TRIANGLE_HALF_L]);;
     
let HOMO_CONVERGENT_IMP_CAUCHY = prove
    (`!s:num->(N)homo l. (s ->->-> l) sequentially ==> homo_cauchy s`,
    REWRITE_TAC[GSYM LIMIT_HOMO_SPACE; GSYM CAUCHY_IN_HOMO_SPACE] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MTOPOLOGY_HOMO_SPACE_METRIC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONVERGENT_IMP_CAUCHY_IN) THEN
    REWRITE_TAC[HOMO_SPACE_METRIC; IN_UNIV]);;

let HOMO_CAUCHY_IMP_BOUNDED = prove
    (`!s:num->(N)homo. homo_cauchy s ==> homo_bounded {y | ?n. y = s n}`,
    GEN_TAC THEN REWRITE_TAC[GSYM CAUCHY_IN_HOMO_SPACE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP CAUCHY_IN_IMP_MBOUNDED) THEN
    REWRITE_TAC[MBOUNDED_HOMO_SPACE] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN SET_TAC[]);;
  
let HOMO_CAUCHY_CONVERGENT_SUBSEQUENCE = prove
    (`!x:num->(N)homo r.
        homo_cauchy x /\ (!m n. m < n ==> r m < r n) /\ ((x o r) ->->-> l) sequentially
        ==> (x ->->-> l) sequentially`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] HOMO_LIM_ADD)) THEN
    DISCH_THEN(MP_TAC o SPEC `\n. (x:num->(N)homo)(n) - x(r n)`) THEN
    DISCH_THEN(MP_TAC o SPEC `homo_mat 0: (N)homo`) THEN ASM_REWRITE_TAC[o_THM] THEN
    REWRITE_TAC[HM_ADD_RID; HM_SUB_ADD2; ETA_AX] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homo_cauchy]) THEN
    REWRITE_TAC[GE; HOMO_LIM_SEQUENTIALLY; homo_dist; HM_SUB_RZERO] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MONOTONE_BIGGER) THEN
    ASM_MESON_TAC[LE_TRANS]);;

let HOMO_CAUCHY_IMP_PAIR_CAUCHY = prove
    (`!s:num->(N)homo. 
        homo_cauchy s ==> cauchy (\n. FST (homo_pair (s n))) /\ matrix_cauchy (\n. SND (homo_pair (s n)))`,
    REWRITE_TAC[HOMO_CAUCHY;CAUCHY;MATRIX_CAUCHY] THEN
    REWRITE_TAC[homo_dist;dist;matrix_dist;GSYM HOMO_PAIR_SUB] THEN
    MESON_TAC[HNORM_TRIANGLE_LT_FST;HNORM_TRIANGLE_LT_SND]);;
  
let MATRIX_CAUCHY_IMP_HOMO_CAUCHY = prove
    (`!x:num->real^N R:num->real^N^N. matrix_cauchy (\n. homo_trans (x n) (R n)) ==>
      homo_cauchy (\n. homo (homo_trans (x n) (R n)))`,
    REPEAT GEN_TAC THEN REWRITE_TAC[HOMO_CAUCHY] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `matrix_cauchy (\n. homo_trans ((x:num->real^N) n) (R n))` THEN
    REWRITE_TAC[MATRIX_CAUCHY] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_SIMP_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_SIMP_TAC[homo_dist] THEN DISCH_TAC THEN
    MATCH_MP_TAC HNORM_TRIANGLE_HALF_LT_PAIR THEN
    REWRITE_TAC[HOMO_PAIR_SUB;GSYM dist;GSYM matrix_dist;HOMO_PAIR;FST;SND] THEN
    ASM_MESON_TAC[REAL_LET_TRANS;HOMO_TRANS_DIST_TRIANGLE_FST;
                  HOMO_TRANS_DIST_TRIANGLE_SND]);;
    
let HOMO_CAUCHY_IMP_MATRIX_CAUCHY = prove
    (`!x:num->real^N R:num->real^N^N. homo_cauchy (\n. homo (homo_trans (x n) (R n))) ==> matrix_cauchy (\n. homo_trans (x n) (R n))`,
    let lem1 = prove 
    (`!x:num->real^N R:num->real^N^N n N. fnorm(R n - R N) = fnorm(SND (homo_pair (homo (homo_trans (x n) (R n)) - homo (homo_trans (x N) (R N)))))`,
    REWRITE_TAC[HOMO_PAIR;SND;HOMO_PAIR_SUB]) in
    let lem2 = prove 
    (`!x:num->real^N R:num->real^N^N n N. norm(x n - x N) = norm(FST (homo_pair (homo (homo_trans (x n) (R n)) - homo (homo_trans (x N) (R N)))))`,
    REWRITE_TAC[HOMO_PAIR;FST;HOMO_PAIR_SUB]) in
    REPEAT GEN_TAC THEN REWRITE_TAC[MATRIX_CAUCHY] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `homo_cauchy (\n. homo (homo_trans ((x:num->real^N) n) (R n)))` THEN
    REWRITE_TAC[HOMO_CAUCHY] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_SIMP_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_SIMP_TAC[homo_dist] THEN DISCH_TAC THEN
    MATCH_MP_TAC HOMO_TRANS_DIST_TRIANGLE_HALF_LT THEN
    REWRITE_TAC[matrix_dist;dist;lem1;lem2] THEN
    ASM_MESON_TAC[REAL_LET_TRANS; FST_LE_HNORM;SND_LE_HNORM]);;
    
let HOMO_CAUCHY_EQ_ALT = prove
    (`!x:num->real^N R:num->real^N^N. matrix_cauchy (\n. homo_trans (x n) (R n)) <=>
      homo_cauchy (\n. homo (homo_trans (x n) (R n)))`,
    REPEAT GEN_TAC THEN EQ_TAC THEN
    REWRITE_TAC[MATRIX_CAUCHY_IMP_HOMO_CAUCHY;HOMO_CAUCHY_IMP_MATRIX_CAUCHY]);;
    
let HOMO_SPACE_COMPACT_IMP_COMPLETE = prove
    (`!s:(N)homo->bool. homo_compact s ==> homo_complete s`,
    GEN_TAC THEN REWRITE_TAC[homo_complete; homo_compact] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `f:num->(N)homo` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMO_CAUCHY_CONVERGENT_SUBSEQUENCE THEN
    ASM_MESON_TAC[]);;
 
(* ------------------------------------------------------------------------- *)
(* euclidean group                                                           *)
(* ------------------------------------------------------------------------- *)

let euclidean_group = new_definition
    `euclidean_group (x:real^N) (R:real^N^N) = group ({(homo_trans x R) | orthogonal_matrix R /\ x IN (:real^N)}, mat 1:(real^(N,1)finite_sum^(N,1)finite_sum), matrix_inv, matrix_mul)`;;
 
let EUCLIDEAN_GROUP = prove
    (`(!x:real^N R:real^N^N. group_carrier(euclidean_group x R) = {(homo_trans x R) | orthogonal_matrix R /\ x IN (:real^N)}) /\
    (!x:real^N R:real^N^N. group_id(euclidean_group x R) = mat 1:real^(N,1)finite_sum^(N,1)finite_sum) /\
    (!x:real^N R:real^N^N. group_inv(euclidean_group x R) = matrix_inv) /\
    (!x:real^N R:real^N^N. group_mul(euclidean_group x R) = matrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl euclidean_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM euclidean_group] THEN ANTS_TAC THENL
    [SIMP_TAC[MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RID] THEN
     SIMP_TAC[IN_ELIM_THM;IN_UNIV] THEN
     CONJ_TAC THENL
     [EXISTS_TAC `(vec 0):real^N` THEN EXISTS_TAC `(mat 1):real^N^N` THEN
      SIMP_TAC[ORTHOGONAL_MATRIX_ID;HOMO_TRANS_EQ_MAT;INVERTIBLE_I]; ALL_TAC] THEN
     CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN 
      EXISTS_TAC `(--matrix_inv (R:real^N^N) ** x')` THEN
      EXISTS_TAC `matrix_inv (R:real^N^N)` THEN
      ASM_SIMP_TAC[ORTHOGONAL_MATRIX_INV_EQ;ORTHOGONAL_MATRIX_IMP_INVERTIBLE;
                   GSYM MATRIX_INV_HOMO_TRANS]; ALL_TAC] THEN
     CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      EXISTS_TAC `(x' + (R:real^N^N) ** x'')` THEN 
      EXISTS_TAC `((R:real^N^N) ** (R':real^N^N))` THEN
      ASM_SIMP_TAC[ORTHOGONAL_MATRIX_MUL;GSYM HOMO_TRANS_MUL_TRANS]; ALL_TAC] THEN
     GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_INV;INVERTIBLE_HOMO_TRANS;ORTHOGONAL_MATRIX_IMP_INVERTIBLE]; ALL_TAC] THEN
     SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);;  

let EUCLIDEAN_SUBGROUP_OF_GENERAL = prove
    (`!x:real^N R:real^N^N g:real^(N,1)finite_sum^(N,1)finite_sum. (group_carrier (euclidean_group x R)) subgroup_of (general_linear_group g)`,
    SIMP_TAC[subgroup_of;EUCLIDEAN_GROUP;GENERAL_LINEAR_GROUP;
             SUBSET;IN_ELIM_THM;IN_UNIV] THEN
    CONJ_TAC THENL [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[INVERTIBLE_HOMO_TRANS;ORTHOGONAL_MATRIX_IMP_INVERTIBLE]; ALL_TAC] THEN
    CONJ_TAC THENL
    [EXISTS_TAC `(vec 0):real^N` THEN EXISTS_TAC `(mat 1):real^N^N` THEN
     SIMP_TAC[ORTHOGONAL_MATRIX_ID;HOMO_TRANS_EQ_MAT;INVERTIBLE_I]; ALL_TAC] THEN
    CONJ_TAC THENL
    [GEN_TAC THEN STRIP_TAC THEN 
     EXISTS_TAC `(--matrix_inv (R:real^N^N) ** x')` THEN
     EXISTS_TAC `matrix_inv (R:real^N^N)` THEN
     ASM_SIMP_TAC[ORTHOGONAL_MATRIX_INV_EQ;ORTHOGONAL_MATRIX_IMP_INVERTIBLE;
                  GSYM MATRIX_INV_HOMO_TRANS]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    EXISTS_TAC `(x' + (R:real^N^N) ** x'')` THEN 
    EXISTS_TAC `((R:real^N^N) ** (R':real^N^N))` THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_MUL;
                 GSYM HOMO_TRANS_MUL_TRANS;INVERTIBLE_MATRIX_MUL]);;

let MATRIX_CLOSED_HOMO_TRANS_ALT = prove 
    (`matrix_closed {homo_trans (x:real^N) (R:real^N^N) | orthogonal_matrix R /\ x IN (:real^N)}`,
    let lem1 = ISPEC `(\N. homo (homo_trans ((x:num->real^N) N) (R N)))` HOMO_CAUCHY_IMP_PAIR_CAUCHY in
    let lem2 = REWRITE_RULE [HOMO_PAIR;FST;SND;ETA_AX] lem1 in
    let th1 = prove
    (`closed {(x:real^N)| x IN (:real^N)}`,
    SIMP_TAC[SET_RULE `{x | T} = UNIV`;CLOSED_UNIV;IN_UNIV]) in
    REWRITE_TAC[GSYM MATRIX_COMPLETE_EQ_CLOSED;matrix_complete] THEN
    REWRITE_TAC[IN_ELIM_THM;IN_UNIV;SKOLEM_THM;IMP_CONJ] THEN
    GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC `x:num->real^N`) THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `R:num->real^N^N`) THEN
    ASM_REWRITE_TAC[MATRIX_CAUCHY] THEN REWRITE_TAC[GSYM MATRIX_CAUCHY] THEN
    REWRITE_TAC[HOMO_CAUCHY_EQ_ALT] THEN DISCH_TAC THEN
    MP_TAC MATRIX_CLOSED_ORTHOGONAL_MATRIX THEN
    SIMP_TAC[GSYM MATRIX_COMPLETE_EQ_CLOSED;matrix_complete] THEN
    DISCH_THEN(MP_TAC o SPEC `R:num->real^N^N`) THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[lem2]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `R:real^N^N`) THEN
    MP_TAC th1 THEN REWRITE_TAC[GSYM COMPLETE_EQ_CLOSED;complete] THEN
    SIMP_TAC[IN_ELIM_THM;IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `x:num->real^N`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[lem2]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
    SIMP_TAC[LEFT_AND_EXISTS_THM] THEN
    EXISTS_TAC `homo_trans (x:real^N) (R:real^N^N)` THEN
    EXISTS_TAC `(x:real^N)` THEN EXISTS_TAC `(R:real^N^N)` THEN
    ASM_SIMP_TAC[HOMO_TRANS_UNIQUE;matrixtendsto] THEN
    REWRITE_TAC[GSYM matrixtendsto] THEN
    REWRITE_TAC[HOMO_LIM_EQ_ALT;HOMO_LIM_EQ_PAIR_LIM] THEN
    ASM_REWRITE_TAC[HOMO_PAIR;FST;SND;ETA_AX]);;
 
let EUCLIDEAN_GROUP_ISMLG = prove
    (`!x:real^N R:real^N^N. ismlg (group_carrier (euclidean_group x R))`,
    REPEAT GEN_TAC THEN SIMP_TAC[ismlg;euclidean_group] THEN
    SIMP_TAC[GSYM general_linear_group;GSYM euclidean_group] THEN
    SIMP_TAC[EUCLIDEAN_SUBGROUP_OF_GENERAL;EUCLIDEAN_GROUP] THEN
    MESON_TAC[TAUT `(P ==> Q) ==> (P ==> (Q \/ R))`;MATRIX_CLOSED_HOMO_TRANS_ALT;MATRIX_CLOSED_SEQUENTIAL_LIMITS]);;
    
let MLG_GROUP_EQ_EG = prove
    (`!G:((N,1)finite_sum)mlg x:real^N R:real^N^N. 
      (mlg_set G = group_carrier (euclidean_group x R)) <=>
      mlg_group G = (euclidean_group x R)`,
    REWRITE_TAC[GROUPS_EQ;EUCLIDEAN_GROUP;MLG_GROUP]);;
    
let MLG_SET_EQ_EG = prove
    (`!x:real^N R:real^N^N. mlg_set (group_mlg (euclidean_group x R)) = group_carrier (euclidean_group x R)`,
    SIMP_TAC[EUCLIDEAN_GROUP_ISMLG;GSYM mlg_tybij;group_mlg]);;
    
let MLG_INJ_EG = prove
    (`!x:real^N R:real^N^N. mlg_group(group_mlg (euclidean_group x R)) = euclidean_group x R`,
    SIMP_TAC[GSYM MLG_GROUP_BIJ;EUCLIDEAN_GROUP_ISMLG;EUCLIDEAN_GROUP]);;
 
(* ------------------------------------------------------------------------- *)
(* special euclidean group                                                   *)
(* ------------------------------------------------------------------------- *)

let special_euclidean_group = new_definition
    `special_euclidean_group (x:real^N) (R:real^N^N) = group ({(homo_trans x R) | orthogonal_matrix R /\ x IN (:real^N) /\ det (homo_trans x R) = &1}, mat 1:(real^(N,1)finite_sum^(N,1)finite_sum), matrix_inv, matrix_mul)`;;
 
let SPECIAL_EUCLIDEAN_GROUP = prove
    (`(!x:real^N R:real^N^N. group_carrier(special_euclidean_group x R) = {(homo_trans x R) | orthogonal_matrix R /\ x IN (:real^N) /\ det (homo_trans x R) = &1}) /\
    (!x:real^N R:real^N^N. group_id(special_euclidean_group x R) = mat 1:real^(N,1)finite_sum^(N,1)finite_sum) /\
    (!x:real^N R:real^N^N. group_inv(special_euclidean_group x R) = matrix_inv) /\
    (!x:real^N R:real^N^N. group_mul(special_euclidean_group x R) = matrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl special_euclidean_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM special_euclidean_group] THEN ANTS_TAC THENL
    [SIMP_TAC[MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RID] THEN
     SIMP_TAC[IN_ELIM_THM;IN_UNIV] THEN
     CONJ_TAC THENL
     [EXISTS_TAC `(vec 0):real^N` THEN EXISTS_TAC `(mat 1):real^N^N` THEN
      SIMP_TAC[ORTHOGONAL_MATRIX_ID;HOMO_TRANS_EQ_MAT;INVERTIBLE_I;DET_I]; ALL_TAC] THEN
     CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN 
      EXISTS_TAC `(--matrix_inv (R:real^N^N) ** x')` THEN
      EXISTS_TAC `matrix_inv (R:real^N^N)` THEN
      ASM_SIMP_TAC[ORTHOGONAL_MATRIX_INV_EQ;ORTHOGONAL_MATRIX_IMP_INVERTIBLE;
                   GSYM MATRIX_INV_HOMO_TRANS;DET_MATRIX_INV;REAL_INV_1]; ALL_TAC] THEN
     CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      EXISTS_TAC `(x' + (R:real^N^N) ** x'')` THEN 
      EXISTS_TAC `((R:real^N^N) ** (R':real^N^N))` THEN
      ASM_SIMP_TAC[ORTHOGONAL_MATRIX_MUL;GSYM HOMO_TRANS_MUL_TRANS;
                   DET_MUL;REAL_MUL_LID]; ALL_TAC] THEN
     GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_INV;INVERTIBLE_HOMO_TRANS;ORTHOGONAL_MATRIX_IMP_INVERTIBLE]; ALL_TAC] THEN
     SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);;  

let SPECIAL_EUCLIDEAN_SUBGROUP_OF_GENERAL = prove
    (`!x:real^N R:real^N^N g:real^(N,1)finite_sum^(N,1)finite_sum. (group_carrier (special_euclidean_group x R)) subgroup_of (general_linear_group g)`,
    SIMP_TAC[subgroup_of;SPECIAL_EUCLIDEAN_GROUP;GENERAL_LINEAR_GROUP;
             SUBSET;IN_ELIM_THM;IN_UNIV] THEN
    CONJ_TAC THENL [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[INVERTIBLE_HOMO_TRANS;ORTHOGONAL_MATRIX_IMP_INVERTIBLE]; ALL_TAC] THEN
    CONJ_TAC THENL
    [EXISTS_TAC `(vec 0):real^N` THEN EXISTS_TAC `(mat 1):real^N^N` THEN
     SIMP_TAC[ORTHOGONAL_MATRIX_ID;HOMO_TRANS_EQ_MAT;INVERTIBLE_I;DET_I]; ALL_TAC] THEN
    CONJ_TAC THENL
    [GEN_TAC THEN STRIP_TAC THEN 
     EXISTS_TAC `(--matrix_inv (R:real^N^N) ** x')` THEN
     EXISTS_TAC `matrix_inv (R:real^N^N)` THEN
     ASM_SIMP_TAC[ORTHOGONAL_MATRIX_INV_EQ;ORTHOGONAL_MATRIX_IMP_INVERTIBLE;
                  GSYM MATRIX_INV_HOMO_TRANS;DET_MATRIX_INV;REAL_INV_1]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    EXISTS_TAC `(x' + (R:real^N^N) ** x'')` THEN 
    EXISTS_TAC `((R:real^N^N) ** (R':real^N^N))` THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_MUL;GSYM HOMO_TRANS_MUL_TRANS;
                 INVERTIBLE_MATRIX_MUL;DET_MUL;REAL_MUL_LID]);;

let SUM_OVER_PERMUTATIONS_NUMSEG_ALT = prove
    (`!f m n. m <= (n + 1)
           ==> sum {p | p permutes (m..(n + 1))} f =
               sum(m..(n + 1)) (\i. sum {p | p permutes (m..(n + 1 - 1))}
                                  (\q. f(swap((n + 1),i) o q)))`,
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM NUMSEG_RREC] THEN
    SIMP_TAC[ARITH_RULE `n + 1 - 1 = n`;ARITH_RULE `(n + 1) - 1 = n`] THEN
    MATCH_MP_TAC (ISPECL [`f:(num->num)->real`;`(a + 1):num`;`s:num->bool`] SUM_OVER_PERMUTATIONS_INSERT) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ARITH_TAC);; 

let DET_HOMO_TRANS_EQ = prove
    (`!x:real^N R:real^N^N. det (homo_trans x R) = det R`,
    let th1 = prove 
    (`!x:real^N R:real^N^N. sum (1..dimindex (:N))
        (\i. sum {p | p permutes 1..dimindex (:N)}
            (\p. sign (swap (dimindex (:N) + 1,i) o p) *
                product (1..dimindex (:N) + 1)
           (\i'. homo_trans x R$i'$(swap (dimindex (:N) + 1,i) o p) i'))) = &0`, 
    let lem = prove
    (`!x:real^N R:real^N^N i. 
    1 <= i /\ i <= dimindex (:N) /\ x' permutes 1..dimindex (:N) ==> 
    product (1..dimindex (:N) + 1)
    (\i'. homo_trans x R$i'$(swap (dimindex (:N) + 1,i) o x') i') = &0`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[swap;o_THM;permutes;IN_NUMSEG;NOT_LE;DE_MORGAN_THM] THEN
    DISCH_TAC THEN SIMP_TAC[PRODUCT_EQ_0_NUMSEG] THEN
    EXISTS_TAC `dimindex (:N) + 1` THEN
    MP_TAC (ISPECL [`x:real^N`;`R:real^N^N`;`dimindex (:N) + 1`;`i:num`] HOMO_TRANS_COMPONENT) THEN
    ASM_SIMP_TAC[ARITH_RULE `x < x + 1`;ARITH_RULE `1 <= n + 1`;LE_REFL;ARITH_RULE `i <= n ==> i <= n + 1`;ARITH_RULE `n <= n + 1`;ARITH_RULE `i <= n ==> ~(i = n + 1)`]) in
    REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    REPEAT STRIP_TAC THEN SIMP_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_0 THEN SIMP_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_MUL_RZERO;lem]) in
    REPEAT GEN_TAC THEN REWRITE_TAC[det] THEN
    SIMP_TAC[SUM_OVER_PERMUTATIONS_NUMSEG_ALT;ARITH_RULE `1 <= n + 1`;DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    SIMP_TAC[ARITH_RULE `1 <= n + 1`;SUM_ADD_SPLIT;SUM_SING_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `n + 1 - 1 = n`;SWAP_REFL;I_O_ID;th1;REAL_ADD_LID] THEN
    MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM;REAL_EQ_MUL_LCANCEL;SIGN_NZ] THEN
    SIMP_TAC[ARITH_RULE `1 <= n + 1`;PRODUCT_ADD_SPLIT;PRODUCT_SING_NUMSEG] THEN
    GEN_TAC THEN ONCE_SIMP_TAC[PERMUTES_FINITE_INJECTIVE;FINITE_NUMSEG] THEN
    REWRITE_TAC[TAUT `P /\ Q /\ R ==> S <=> R ==> Q ==> P ==> S`] THEN
    REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN DISCH_TAC THEN
    SIMP_TAC[NOT_LE;DE_MORGAN_THM;ARITH_RULE `x < x + 1`] THEN
    SIMP_TAC[ISPECL [`x:real^N`;`R:real^N^N`;`dimindex (:N) + 1`;`dimindex (:N) + 1`] HOMO_TRANS_COMPONENT;ARITH_RULE `1 <= n + 1`;LE_REFL] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN DISCH_TAC THEN
    MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC (ISPECL [`x:real^N`;`R:real^N^N`;`i:num`;`(x':num->num) i`] HOMO_TRANS_COMPONENT) THEN
    ASM_SIMP_TAC[ARITH_RULE `i <= n ==> i <= n + 1`;ARITH_RULE `i <= n ==> ~(i = n + 1)`]);; 
   
let MATRIX_CLOSED_DET_CONSTANT_HOMO = prove
    (`!a:real. matrix_closed {(homo_trans (x:real^N) (R:real^N^N)) | det (homo_trans x R) = a}`,
    let lem1 = ISPEC `(\N. homo (homo_trans ((x:num->real^N) N) (R N)))` HOMO_CAUCHY_IMP_PAIR_CAUCHY in
    let lem2 = REWRITE_RULE [HOMO_PAIR;FST;SND;ETA_AX] lem1 in
    let th1 = prove
    (`closed {(x:real^N)| x IN (:real^N)}`,
    SIMP_TAC[SET_RULE `{x | T} = UNIV`;CLOSED_UNIV;IN_UNIV]) in
    REWRITE_TAC[GSYM MATRIX_COMPLETE_EQ_CLOSED;matrix_complete] THEN
    REWRITE_TAC[IN_ELIM_THM;DET_HOMO_TRANS_EQ;SKOLEM_THM;IMP_CONJ] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC `x:num->real^N`) THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `R:num->real^N^N`) THEN
    ASM_REWRITE_TAC[MATRIX_CAUCHY] THEN REWRITE_TAC[GSYM MATRIX_CAUCHY] THEN
    REWRITE_TAC[HOMO_CAUCHY_EQ_ALT] THEN
    DISCH_TAC THEN
    MP_TAC MATRIX_CLOSED_DET_CONSTANT THEN
    SIMP_TAC[GSYM MATRIX_COMPLETE_EQ_CLOSED;matrix_complete] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real`) THEN
    DISCH_THEN(MP_TAC o SPEC `R:num->real^N^N`) THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[lem2]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `R:real^N^N`) THEN
    MP_TAC th1 THEN REWRITE_TAC[GSYM COMPLETE_EQ_CLOSED;complete] THEN
    SIMP_TAC[IN_ELIM_THM;IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `x:num->real^N`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[lem2]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
    SIMP_TAC[LEFT_AND_EXISTS_THM] THEN
    EXISTS_TAC `homo_trans (x:real^N) (R:real^N^N)` THEN
    EXISTS_TAC `(x:real^N)` THEN EXISTS_TAC `(R:real^N^N)` THEN
    ASM_SIMP_TAC[HOMO_TRANS_UNIQUE;matrixtendsto] THEN
    REWRITE_TAC[GSYM matrixtendsto] THEN
    REWRITE_TAC[HOMO_LIM_EQ_ALT;HOMO_LIM_EQ_PAIR_LIM] THEN
    ASM_REWRITE_TAC[HOMO_PAIR;FST;SND;ETA_AX]);;
                 
let SPECIAL_EUCLIDEAN_GROUP_ISMLG = prove
    (`!x:real^N R:real^N^N. ismlg (group_carrier (special_euclidean_group x R))`,
    REPEAT GEN_TAC THEN SIMP_TAC[ismlg;special_euclidean_group] THEN
    SIMP_TAC[GSYM general_linear_group;GSYM special_euclidean_group] THEN
    SIMP_TAC[SPECIAL_EUCLIDEAN_SUBGROUP_OF_GENERAL;SPECIAL_EUCLIDEAN_GROUP] THEN
    MP_TAC(ISPECL [`{homo_trans (x:real^N) (R:real^N^N) | orthogonal_matrix R /\ x IN (:real^N)}`;`{homo_trans (x:real^N) (R:real^N^N) | det(homo_trans x R) = &1}`] MATRIX_CLOSED_INTER) THEN
    SIMP_TAC[MATRIX_CLOSED_HOMO_TRANS_ALT;MATRIX_CLOSED_DET_CONSTANT_HOMO;MATRIX_CLOSED_SEQUENTIAL_LIMITS] THEN
    SIMP_TAC[INTER;IN_ELIM_THM;IN_UNIV] THEN
    SIMP_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    SIMP_TAC[SKOLEM_THM;IMP_CONJ;LEFT_IMP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `x':num->real^N`) THEN
    DISCH_THEN(MP_TAC o SPEC `R:num->real^N^N`) THEN
    SET_TAC[]);;
    
let MLG_GROUP_EQ_SEG = prove
    (`!G:((N,1)finite_sum)mlg x:real^N R:real^N^N. 
      (mlg_set G = group_carrier (special_euclidean_group x R)) <=>
      mlg_group G = (special_euclidean_group x R)`,
    REWRITE_TAC[GROUPS_EQ;SPECIAL_EUCLIDEAN_GROUP;MLG_GROUP]);;
    
let MLG_SET_EQ_SEG = prove
    (`!x:real^N R:real^N^N. mlg_set (group_mlg (special_euclidean_group x R)) = group_carrier (special_euclidean_group x R)`,
    SIMP_TAC[SPECIAL_EUCLIDEAN_GROUP_ISMLG;GSYM mlg_tybij;group_mlg]);;
    
let MLG_INJ_SEG = prove
    (`!x:real^N R:real^N^N. mlg_group(group_mlg (special_euclidean_group x R)) = special_euclidean_group x R`,
    SIMP_TAC[GSYM MLG_GROUP_BIJ;SPECIAL_EUCLIDEAN_GROUP_ISMLG;SPECIAL_EUCLIDEAN_GROUP]);;

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
  
let matrix_lie_bracket = new_definition
    `matrix_lie_bracket (A:real^N^N) (B:real^N^N) = A ** B - B ** A`;;

let MATRIX_LIE_BRACKET_BILINEAR = prove
    (`bimlinear matrix_lie_bracket`,
    SIMP_TAC [bimlinear; mlinear;matrix_lie_bracket] THEN
    REPEAT STRIP_TAC THEN MATRIX_ARITH_TAC);;
    
let MATRIX_LIE_BRACKET_BILINEAR_ALT = prove
    (`!x y k c.
        matrix_lie_bracket x (k + y) = 
        matrix_lie_bracket x k + matrix_lie_bracket x y /\
        matrix_lie_bracket (x + k) y =
        matrix_lie_bracket x y + matrix_lie_bracket k y /\
        matrix_lie_bracket x (c %% y) = c %% matrix_lie_bracket x y /\
        matrix_lie_bracket (c %% x) y = c %% matrix_lie_bracket x y`,
    SIMP_TAC [matrix_lie_bracket] THEN
    REPEAT STRIP_TAC THEN MATRIX_ARITH_TAC);;
    
let MATRIX_LIE_BRACKET_SSM = prove
    (`!A B:real^N^N. matrix_lie_bracket A B = --(matrix_lie_bracket B A)`,
    SIMP_TAC [matrix_lie_bracket] THEN MATRIX_ARITH_TAC);;
    
let MATRIX_LIE_BRACKET_SSM_ALT = prove
    (`!A B:real^N^N. matrix_lie_bracket A B + matrix_lie_bracket B A = mat 0`,
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [MATRIX_LIE_BRACKET_SSM] THEN MATRIX_ARITH_TAC);;
    
let MATRIX_LIE_BRACKET_REFL = prove
    (`!A:real^N^N. matrix_lie_bracket A A = mat 0`,
    SIMP_TAC [matrix_lie_bracket;MATRIX_SUB_REFL]);;
    
let MATRIX_LIE_BRACKET_JACOBI_I = prove
    (`!A B C:real^N^N. matrix_lie_bracket A (matrix_lie_bracket B C) + matrix_lie_bracket B (matrix_lie_bracket C A) + matrix_lie_bracket C (matrix_lie_bracket A B) = mat 0`,
    SIMP_TAC [matrix_lie_bracket] THEN SIMP_TAC[MATRIX_SUB_LDISTRIB;MATRIX_SUB_RDISTRIB;GSYM MATRIX_MUL_ASSOC] THEN
    SIMP_TAC[MATRIX_ARITH `A1 - A2 - (B1 - C1) + B1 - B2 - (C2 - A2) + C2 - C1 - (A1 - B2) :real^N^N = mat 0`]);;

(* ------------------------------------------------------------------------- *)
(* the lie algebra of matrix lie group                                       *)
(* ------------------------------------------------------------------------- *)

let is_lie_algebra_of_mlg = new_definition
    `is_lie_algebra_of_mlg (G:(N)mlg) (g:(real^N^N,real)lie_algebra) <=>
    !X t. X IN lie_alg_set g ==> (matrix_exp (t %% X)) IN (mlg_set G)`;;

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
(* sl(n) the lie algebra of general linear group                             *)
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
(* o(n) the lie algebra of general linear group                             *)
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
(* so(n) the lie algebra of general linear group                             *)
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

(*
let DET_MATRIX_EXP_EQ_EXP_TRACE = prove
    (`!x:real^N^N t. det(matrix_exp (t %% x)) = exp(trace(t %% x))`,
    
    
    HAS_REAL_DERIVATIVE_ZERO_UNIQUE
    );;
*)     

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

let ORTHOGONAL_MATRIX_EQ = prove
    (`!A:real^N^N. orthogonal_matrix A <=> matrix_inv A = transp A /\ invertible A`,
    GEN_TAC THEN EQ_TAC THENL
    [SIMP_TAC[ORTHOGONAL_MATRIX_INV;ORTHOGONAL_MATRIX_IMP_INVERTIBLE];
     REPEAT STRIP_TAC THEN REWRITE_TAC[orthogonal_matrix] THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[MATRIX_INV]]);;

let IS_LIE_ALGEBRA_OF_OG = prove
    (`!a:real^N^N. is_lie_algebra_of_mlg (group_mlg(orthogonal_group a)) (lie_algebra_of_og (group_mlg(orthogonal_group a)))`,
    REWRITE_TAC[is_lie_algebra_of_mlg;LIE_ALGEBRA_OF_OG;MLG_SET_EQ_OG;ORTHOGONAL_GROUP;IN_ELIM_THM;IN_UNIV] THEN
    SIMP_TAC[ORTHOGONAL_MATRIX_EQ;INVERTIBLE_MATRIX_EXP;TRANSP_TRANS_EXP;MATRIX_EXP_INV;MATRIX_ARITH `!x t. --(t %% x) = t %% (--x)`]);;
     
let IS_LIE_ALGEBRA_OF_SOG = prove
    (`!a:real^N^N. is_lie_algebra_of_mlg (group_mlg(rotation_group a)) (lie_algebra_of_sog (group_mlg(rotation_group a)))`,
    REWRITE_TAC[is_lie_algebra_of_mlg;LIE_ALGEBRA_OF_SOG;MLG_SET_EQ_SOG;ROTATION_GROUP;IN_ELIM_THM;IN_UNIV] THEN
    SIMP_TAC[ORTHOGONAL_MATRIX_EQ;INVERTIBLE_MATRIX_EXP;TRANSP_TRANS_EXP;MATRIX_EXP_INV;MATRIX_CMUL_LNEG;MATRIX_CMUL_RNEG;SSM_IMP_DET_EXP_1]);;

(* ------------------------------------------------------------------------- *)
(* log function in matrix space                                              *)
(* ------------------------------------------------------------------------- *)
    
let matrix_log = new_definition
    `matrix_log (A:real^N^N) = infmsum (from 1) (\n. ((-- &1) pow (n + 1) / &n) %% ((A - mat 1) matrix_pow n))`;;
 
let MATRIX_LOG_1 = prove
    (`matrix_log(mat 1:real^N^N) = mat 0`,
    REWRITE_TAC[matrix_log] THEN MATCH_MP_TAC INFMSUM_UNIQUE THEN 
    MATCH_MP_TAC MSUMS_0 THEN SIMP_TAC[from;IN_ELIM_THM;MATRIX_SUB_REFL] THEN
    MESON_TAC[ARITH_RULE `1 <= n ==> n = SUC (n - 1)`;MATRIX_POW_0;MATRIX_CMUL_RZERO]);;

let MATRIX_LOG_CONVERGES = prove
    (`!A:real^N^N. fnorm(A - mat 1) < &1 ==>
        ((\n. ((-- &1) pow (n + 1) / &n) %% ((A - mat 1) matrix_pow n)) 
          msums matrix_log(A)) (from 1)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[matrix_log; MSUMS_INFSUM; msummable] THEN
    MATCH_MP_TAC MSERIES_RATIO THEN SIMP_TAC [GE;FNORM_MUL] THEN
    REWRITE_TAC[ARITH_RULE `SUC n + 1 = SUC (n + 1)`] THEN
    REWRITE_TAC[REAL_ABS_MUL;real_div;REAL_ABS_INV] THEN
    REWRITE_TAC[REAL_POW_NEG;REAL_POW_ONE;COND_RAND;REAL_ABS_NEG;COND_ID] THEN
    REWRITE_TAC[REAL_ABS_NUM;REAL_MUL_LID;matrix_pow] THEN
    EXISTS_TAC `fnorm((A:real^N^N) - mat 1)` THEN EXISTS_TAC `1` THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x * y * z = y * (x * z)`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[FNORM_POS_LE;FNORM_SUBMULT] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> 0 <= SUC n`;REAL_LE_INV_EQ;REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LE;REAL_OF_NUM_LT] THEN ASM_ARITH_TAC);;
    
let MATRIX_LOG_CONVERGES_UNIQUE = prove
    (`!A:real^N^N B. fnorm(A - mat 1) < &1 ==>
    (((\n. ((-- &1) pow (n + 1) / &n) %% ((A - mat 1) matrix_pow n)) 
          msums B) (from 1) <=> B = matrix_log(A))`,
    REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[MATRIX_LOG_CONVERGES] THEN
    DISCH_THEN(MP_TAC o C CONJ (SPEC `A:real^N^N` MATRIX_LOG_CONVERGES)) THEN
    ASM_REWRITE_TAC [MSERIES_UNIQUE]);;

let MSUMMABLE_MATRIX_LOG = prove
    (`!A:real^N^N. fnorm(A - mat 1) < &1 ==> msummable (from 1) (\n. ((-- &1) pow (n + 1) / &n) %% ((A - mat 1) matrix_pow n))`,
    SIMP_TAC[GSYM MSUMS_INFSUM;GSYM matrix_log;MATRIX_LOG_CONVERGES]);;
  
let MATRIX_LOG_TRANSP = prove
    (`!A:real^N^N. fnorm(A - mat 1) < &1 ==>
        transp (matrix_log A) = matrix_log (transp  A)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC [matrix_log] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC INFMSUM_UNIQUE THEN 
    ONCE_REWRITE_TAC[GSYM TRANSP_MAT] THEN
    REWRITE_TAC[GSYM TRANSP_MATRIX_SUB;GSYM TRANSP_MATRIX_CMUL;
                MATRIX_POW_TRANSP;GSYM MSUMS_TRANSP] THEN 
    ASM_SIMP_TAC[GSYM matrix_log;MATRIX_LOG_CONVERGES;TRANSP_MAT]);;
    
let MATRIX_LOG_CONVERGES_UNIFORMLY_CAUCHY = prove
    (`!R e. &0 < e /\ &0 < R /\ R < &1
         ==> ?N. !m n z:real^N^N. m >= N /\ fnorm(z - mat 1) <= R
    ==> fnorm(msum(m..n) (\i. ((-- &1) pow (i + 1) / &i) %% ((z - mat 1) matrix_pow i))) < e`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`R:real`; `(\i. (&1 / &i) %% (R %% mat 1:real^N^N) matrix_pow i)`; `from 0`] MSERIES_RATIO) THEN 
    REWRITE_TAC[MSERIES_CAUCHY; LEFT_FORALL_IMP_THM] THEN
    MP_TAC(SPEC `&2 * abs (R) :real` REAL_ARCH_SIMPLE) THEN
    SIMP_TAC [MATRIX_POW_CMUL; MATRIX_POW_ONE] THEN 
    REWRITE_TAC[FNORM_MUL; FNORM_MAT; REAL_MUL_LID] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC(TAUT `(a ==> b) /\ (c ==> d) ==> a ==> (b ==> c) ==> d`) THEN
    CONJ_TAC THENL
    [ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN
    SIMP_TAC[real_div;REAL_ABS_MUL] THEN
    SIMP_TAC[REAL_MUL_LID] THEN
    SIMP_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC [REAL_OF_NUM_LE; DIMINDEX_GE_1; SQRT_POS_LE;
              ARITH_RULE `1 <= n ==> 0 <= n`] THEN
    SIMP_TAC[REAL_ARITH `(x * y) * z = y * (x * z)`] THEN    
    SIMP_TAC[REAL_ARITH `x * y * z = x * (y * z)`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_ABS_POS;REAL_LE_INV_EQ;REAL_ARITH `&0 <= &(SUC n)`] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_INV2 THEN
     CONJ_TAC THENL
     [FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE]) THEN 
      ASM_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[real_pow;REAL_ABS_MUL;REAL_ARITH `&0 < R ==> abs R = R`;REAL_LE_REFL];
    ALL_TAC] THEN
     DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
     REWRITE_TAC[FROM_0; INTER_UNIV] THEN
     REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
     DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
     ASM_SIMP_TAC[] THEN
     MATCH_MP_TAC (REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
     REWRITE_TAC[MATRIX_CMUL_ASSOC; GSYM MSUM_MMUL;FNORM_MUL;
                 FNORM_MAT; REAL_MUL_LID] THEN
     SUBGOAL_THEN `abs (sum (m..n) (\i. &1 / &i * R pow i)) =
                  sum (m..n) (\i. &1 / &i * R pow i)`
      SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_LE_MUL;REAL_ARITH `&0 <= &p`;REAL_LE_DIV;REAL_POW_LE;REAL_LT_IMP_LE];ALL_TAC] THEN
      SIMP_TAC[GSYM SUM_RMUL] THEN
      MATCH_MP_TAC MSUM_FNORM_LE THEN REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN REPEAT STRIP_TAC THEN
      ASM_CASES_TAC `i = 0` THENL
      [ASM_SIMP_TAC[matrix_pow;real_pow;real_div;REAL_INV_0;REAL_MUL_RZERO;REAL_MUL_LZERO;MATRIX_CMUL_LZERO;FNORM_0;REAL_LE_REFL];ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `x <= y * z <=> x * &1 <= y * z`] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      SIMP_TAC[FNORM_POS_LE;REAL_ARITH `&0 <= &1`] THEN
      SIMP_TAC[DIMINDEX_GE_1;REAL_OF_NUM_LE;REAL_ARITH `&1 <= &x ==> &1 pow 2 <= &x`;REAL_LE_RSQRT] THEN
      SIMP_TAC[FNORM_MUL;real_div;REAL_ABS_MUL] THEN
      SIMP_TAC[REAL_POW_NEG;REAL_POW_ONE;COND_RAND;REAL_ABS_NEG;REAL_ABS_1;COND_ID] THEN
      SIMP_TAC[REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      SIMP_TAC[REAL_ABS_POS;FNORM_POS_LE] THEN
      CONJ_TAC THENL
      [MESON_TAC[REAL_ABS_REFL;REAL_LE_INV;REAL_ARITH `&0 <= &i`;REAL_LE_REFL];
      ASM_MESON_TAC[REAL_LE_TRANS;FNORM_MATRIX_POW_LE;REAL_POW_LE2;FNORM_POS_LE;LE_1]]);;

let MATRIX_LOG_CONVERGES_UNIFORMLY = prove
    (`!R e. &0 < R /\ &0 < e /\ R < &1
         ==> ?N. !n z:real^N^N. n >= N /\ fnorm(z - mat 1) < R
                       ==> fnorm(msum(1..n) (\i. ((-- &1) pow (i + 1) / &i) %% ((z - mat 1) matrix_pow i)) -
                                matrix_log(z)) <= e`,
    let lem = prove
     (`!n. from 1 INTER (0..n) = (1..n)`,
     REWRITE_TAC[from;INTER;IN_NUMSEG;EXTENSION;IN_ELIM_THM] THEN
     ARITH_TAC) in
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`R:real`; `e / &2`] MATRIX_LOG_CONVERGES_UNIFORMLY_CAUCHY) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^N^N`] THEN STRIP_TAC THEN
    MP_TAC(SPEC `z:real^N^N` MATRIX_LOG_CONVERGES) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[msums;MATRIX_LIM_SEQUENTIALLY;matrix_dist;lem] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `n + (M + 1)`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n + 1`; `n + (M + 1)`; `z:real^N^N`]) THEN
    ASM_SIMP_TAC[ARITH_RULE `(n >= N ==> n + 1 >= N) /\ M <= n + (M + 1)`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; MSUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`] THEN
    CONV_TAC(ONCE_DEPTH_CONV(ALPHA_CONV `i:num`)) THEN 
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM FNORM_NEG] THEN
    MATCH_MP_TAC (REAL_ARITH `c <= a + b ==> a < e / &2 ==> b < e / &2 ==> c <= e`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ` fnorm (--msum (n + 1..n + (M + 1)) (\i:num. ((-- &1) pow (i + 1) / &i) %% ((z:real^N^N) - mat 1) matrix_pow i) + (msum (1..n) (\i. ((-- &1) pow (i + 1) / &i) %% ((z:real^N^N) - mat 1) matrix_pow i) +
   msum (n + 1..n + (M + 1)) (\i. ((-- &1) pow (i + 1) / &i) %% ((z:real^N^N) - mat 1) matrix_pow i)) - matrix_log(z))` THEN CONJ_TAC THENL
   [SIMP_TAC[MATRIX_ARITH `!A B C:real^N^N.(--B) + (A + B) - C = A - C`] THEN
    REAL_ARITH_TAC ;ALL_TAC] THEN SIMP_TAC[GSYM FNORM_TRIANGLE]);;

(* ------------------------------------------------------------------------- *)
(* inv function of (I - A) in matrix space                                   *)
(* ------------------------------------------------------------------------- *)
    
let MSUMMABLE_MATRIX_POW = prove
    (`!A:real^N^N. fnorm(A) < &1 ==> msummable (from 0) (\n. A matrix_pow n)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[msummable] THEN
    MATCH_MP_TAC MSERIES_RATIO THEN SIMP_TAC[GE;matrix_pow] THEN
    MAP_EVERY EXISTS_TAC [`fnorm((A:real^N^N))`;`1`] THEN
    ASM_SIMP_TAC[FNORM_SUBMULT]);;

let MSUMMABLE_MATRIX_POW_SUC = prove
    (`!A:real^N^N. fnorm(A) < &1 ==> msummable (from 0) (\n. A matrix_pow SUC n)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[msummable] THEN
    MATCH_MP_TAC MSERIES_RATIO THEN SIMP_TAC[GE;matrix_pow] THEN
    MAP_EVERY EXISTS_TAC [`fnorm((A:real^N^N))`;`1`] THEN
    ASM_SIMP_TAC[FNORM_SUBMULT]);;

let INVERTIBLE_SUB_CONDITION = prove
    (`!A:real^N^N. fnorm(A) < &1 ==> invertible(mat 1 - A)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[INVERTIBLE_RIGHT_INVERSE] THEN
    EXISTS_TAC `infmsum (from 0) (\n. (A:real^N^N) matrix_pow n)` THEN
    REWRITE_TAC[MATRIX_SUB_RDISTRIB;MATRIX_MUL_LID] THEN
    ASM_SIMP_TAC[GSYM INFMSUM_LMUL;MSUMMABLE_MATRIX_POW] THEN
    ASM_SIMP_TAC[GSYM matrix_pow;GSYM INFMSUM_SUB;MSUMMABLE_MATRIX_POW;MSUMMABLE_MATRIX_POW_SUC] THEN
    MATCH_MP_TAC INFMSUM_UNIQUE THEN REWRITE_TAC[ADD1] THEN
    MATCH_MP_TAC MSERIES_DIFFS THEN MATCH_MP_TAC MSERIES_TERMS_TOZERO THEN
    MAP_EVERY EXISTS_TAC [`infmsum (from 0) (\n. (A:real^N^N) matrix_pow n)`;`0`]  THEN
    ASM_SIMP_TAC[MSUMMABLE_MATRIX_POW;MSUMS_INFSUM]);;

let MATRIX_INV_SUB_CONDITION = prove    
    (`!A:real^N^N. fnorm(A) < &1 ==> matrix_inv(mat 1 - A) = infmsum (from 0) (\n. A matrix_pow n)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `A:real^N^N` INVERTIBLE_SUB_CONDITION) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    ONCE_ASM_SIMP_TAC[GSYM (ISPEC `(mat 1 - A:real^N^N)` MATRIX_MUL_LCANCEL)] THEN 
    ASM_SIMP_TAC[MATRIX_INV] THEN
    REWRITE_TAC[MATRIX_SUB_RDISTRIB;MATRIX_MUL_LID] THEN
    ASM_SIMP_TAC[GSYM INFMSUM_LMUL;MSUMMABLE_MATRIX_POW] THEN
    ASM_SIMP_TAC[GSYM matrix_pow;GSYM INFMSUM_SUB;MSUMMABLE_MATRIX_POW;MSUMMABLE_MATRIX_POW_SUC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INFMSUM_UNIQUE THEN REWRITE_TAC[ADD1] THEN
    MATCH_MP_TAC MSERIES_DIFFS THEN MATCH_MP_TAC MSERIES_TERMS_TOZERO THEN
    MAP_EVERY EXISTS_TAC [`infmsum (from 0) (\n. (A:real^N^N) matrix_pow n)`;`0`]  THEN
    ASM_SIMP_TAC[MSUMMABLE_MATRIX_POW;MSUMS_INFSUM]);;
    
let MATRIX_INV_SUB_CONVERGES = prove
    (`!A:real^N^N. fnorm(A) < &1 ==> ((\n. A matrix_pow n) msums matrix_inv(mat 1 - A)) (from 0)`,
    SIMP_TAC[MATRIX_INV_SUB_CONDITION;MSUMMABLE_MATRIX_POW;MSUMS_INFSUM]);;
    
let MATRIX_INV_SUB_CONVERGES_UNIFORMLY_CAUCHY_LMUL1 = prove
    (`!R e A:real^N^N. &0 < e /\ &0 < R /\ R < inv(fnorm A)
         ==> ?N. !m n z:real^1^1. m >= N /\ fnorm(z) <= R
            ==> fnorm(A ** msum(m..n) (\i. (drop_drop z %% A) matrix_pow i)) < e`,
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPECL [`&0`;`R:real`;`inv (fnorm (A:real^N^N))`] REAL_LT_TRANS) THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`R * fnorm(A:real^N^N)`; `(\i. (mat 1:real^N^N) ** ((R * fnorm(A:real^N^N)) %% mat 1:real^N^N) matrix_pow i)`; `from 0`] MSERIES_RATIO) THEN        
    REWRITE_TAC[MSERIES_CAUCHY; LEFT_FORALL_IMP_THM] THEN
    MP_TAC(SPEC `&2 * abs (R) * fnorm (A:real^N^N) :real` REAL_ARCH_SIMPLE) THEN
    SIMP_TAC[MATRIX_POW_CMUL; MATRIX_POW_ONE] THEN
    SIMP_TAC[MATRIX_MUL_RMUL; MATRIX_MUL_RID] THEN
    REWRITE_TAC[FNORM_MUL; FNORM_MAT; REAL_MUL_LID] THEN 
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC(TAUT `(a ==> b) /\ (c ==> d) ==> a ==> (b ==> c) ==> d`) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    CONJ_TAC THENL 
    [MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN
     EXISTS_TAC `inv (fnorm (A:real^N^N))` THEN
     ASM_SIMP_TAC[REAL_MUL_LID;REAL_MUL_RID;REAL_LT_IMP_NZ;REAL_LT_INV;REAL_MUL_RINV;REAL_ARITH `(x * y) * z = x * (y * z)`];ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN         
    REWRITE_TAC[real_pow;REAL_ABS_MUL;REAL_ABS_FNORM] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e / fnorm(A:real^N^N):real`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    REWRITE_TAC[FROM_0; INTER_UNIV] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    FIRST_ASSUM (ASSUME_TAC) THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC [] THEN
    UNDISCH_TAC `&0 < fnorm (A:real^N^N)` THEN SIMP_TAC [IMP_IMP] THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN
    DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_RMUL) THEN
    ASM_SIMP_TAC [REAL_FIELD `&0 < b ==> a / b * b = a`] THEN
    MATCH_MP_TAC (REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
    W(MP_TAC o PART_MATCH lhand FNORM_SUBMULT o lhand o snd) THEN
    MATCH_MP_TAC (REAL_ARITH `!c:real. b <= c ==> a <= b ==> a <= c`) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC [FNORM_POS_LE] THEN
    REWRITE_TAC [MATRIX_CMUL_ASSOC; GSYM MSUM_MMUL;FNORM_MUL;
                 FNORM_MAT; REAL_MUL_LID; MATRIX_MUL_LID] THEN
    SUBGOAL_THEN `abs (sum (m..n) (\i. (R * fnorm (A:real^N^N)) pow i)) = sum (m..n) (\i. (R * fnorm A) pow i)`
      SUBST1_TAC THENL 
      [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
       ASM_SIMP_TAC[REAL_LT_MUL;REAL_LT_IMP_LE;REAL_POW_LE];
       ALL_TAC] THEN
    SIMP_TAC [GSYM SUM_RMUL] THEN   
    MATCH_MP_TAC MSUM_FNORM_LE THEN REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN 
    X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = 0` THENL
    [ASM_SIMP_TAC[real_pow; matrix_pow;MATRIX_CMUL_LID;REAL_MUL_LID;FNORM_MAT; REAL_LE_REFL]; ALL_TAC] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC [REAL_LE_01; REAL_LE_MUL; REAL_ABS_POS; FNORM_POS_LE] THEN
    CONJ_TAC THENL
    [ALL_TAC;
     MESON_TAC [SQRT_1; SQRT_MONO_LE; DIMINDEX_GE_1;REAL_OF_NUM_LE]] THEN
    SIMP_TAC [drop_drop; FNORM_MUL; REAL_ABS_POW;
              GSYM FNORM_REAL; REAL_POW_MUL] THEN         
    ASM_SIMP_TAC[REAL_LE_MUL2;FNORM_POS_LE;REAL_POW_LE;REAL_POW_LE2;FNORM_MATRIX_POW_LE;ARITH_RULE `~(i = 0) ==> 1 <= i`]);;

let MATRIX_INV_SUB_CONVERGES_UNIFORMLY_CAUCHY_LMUL1_ADD = prove
    (`!R e A:real^N^N c:real. &0 < e /\ &0 <= c /\ &0 < R /\ R < inv(fnorm A + c)
         ==> ?N. !m n z:real^1^1. m >= N /\ fnorm(z) <= R
            ==> fnorm(A ** msum(m..n) (\i. (drop_drop z %% A) matrix_pow i)) < e`,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `A = (mat 0:real^N^N)` THENL
    [ASM_SIMP_TAC[MATRIX_MUL_LZERO;FNORM_0];ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE [GSYM FNORM_POS_LT]) THEN
    MP_TAC(ISPECL [`R * fnorm(A:real^N^N)`; `(\i. (mat 1:real^N^N) ** ((R * fnorm(A:real^N^N)) %% mat 1:real^N^N) matrix_pow i)`; `from 0`] MSERIES_RATIO) THEN        
    REWRITE_TAC[MSERIES_CAUCHY; LEFT_FORALL_IMP_THM] THEN
    MP_TAC(SPEC `&2 * abs (R) * fnorm (A:real^N^N) :real` REAL_ARCH_SIMPLE) THEN
    SIMP_TAC[MATRIX_POW_CMUL; MATRIX_POW_ONE] THEN
    SIMP_TAC[MATRIX_MUL_RMUL; MATRIX_MUL_RID] THEN
    REWRITE_TAC[FNORM_MUL; FNORM_MAT; REAL_MUL_LID] THEN 
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC(TAUT `(a ==> b) /\ (c ==> d) ==> a ==> (b ==> c) ==> d`) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    CONJ_TAC THENL 
    [MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `inv (fnorm (A:real^N^N))` THEN
     ASM_SIMP_TAC[REAL_MUL_LID;REAL_MUL_RID;REAL_LT_IMP_NZ;REAL_LT_INV;REAL_MUL_RINV;GSYM REAL_MUL_ASSOC] THEN
     MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv (fnorm (A:real^N^N) + c)` THEN
     ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> x <= x + c`;REAL_LE_INV2]
     ;ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN         
    REWRITE_TAC[real_pow;REAL_ABS_MUL;REAL_ABS_FNORM] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e / fnorm(A:real^N^N):real`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    REWRITE_TAC[FROM_0; INTER_UNIV] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    FIRST_ASSUM (ASSUME_TAC) THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC [] THEN
    UNDISCH_TAC `&0 < fnorm (A:real^N^N)` THEN SIMP_TAC [IMP_IMP] THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN
    DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_RMUL) THEN
    ASM_SIMP_TAC [REAL_FIELD `&0 < b ==> a / b * b = a`] THEN
    MATCH_MP_TAC (REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
    W(MP_TAC o PART_MATCH lhand FNORM_SUBMULT o lhand o snd) THEN
    MATCH_MP_TAC (REAL_ARITH `!c:real. b <= c ==> a <= b ==> a <= c`) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC [FNORM_POS_LE] THEN
    REWRITE_TAC [MATRIX_CMUL_ASSOC; GSYM MSUM_MMUL;FNORM_MUL;
                 FNORM_MAT; REAL_MUL_LID; MATRIX_MUL_LID] THEN
    SUBGOAL_THEN `abs (sum (m..n) (\i. (R * fnorm (A:real^N^N)) pow i)) = sum (m..n) (\i. (R * fnorm A) pow i)`
      SUBST1_TAC THENL 
      [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
       ASM_SIMP_TAC[REAL_LT_MUL;REAL_LT_IMP_LE;REAL_POW_LE];
       ALL_TAC] THEN
    SIMP_TAC [GSYM SUM_RMUL] THEN   
    MATCH_MP_TAC MSUM_FNORM_LE THEN REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN 
    X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = 0` THENL
    [ASM_SIMP_TAC[real_pow; matrix_pow;MATRIX_CMUL_LID;REAL_MUL_LID;FNORM_MAT; REAL_LE_REFL]; ALL_TAC] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC [REAL_LE_01; REAL_LE_MUL; REAL_ABS_POS; FNORM_POS_LE] THEN
    CONJ_TAC THENL
    [ALL_TAC;
     MESON_TAC [SQRT_1; SQRT_MONO_LE; DIMINDEX_GE_1;REAL_OF_NUM_LE]] THEN
    SIMP_TAC [drop_drop; FNORM_MUL; REAL_ABS_POW;
              GSYM FNORM_REAL; REAL_POW_MUL] THEN         
    ASM_SIMP_TAC[REAL_LE_MUL2;FNORM_POS_LE;REAL_POW_LE;REAL_POW_LE2;FNORM_MATRIX_POW_LE;ARITH_RULE `~(i = 0) ==> 1 <= i`]);;        
            
let MATRIX_INV_SUB_CONVERGES_UNIFORMLY_LMUL1 = prove
    (`!R e A:real^N^N. &0 < e /\ &0 < R /\ R < inv(fnorm A)
         ==> ?N. !n z:real^1^1. n >= N /\ fnorm(z) < R
            ==> fnorm(A ** msum(0..n) (\i. (drop_drop z %% A) matrix_pow i) - A ** matrix_inv(mat 1 - (drop_drop z %% A))) <= e`,
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPECL [`&0`;`R:real`;`inv (fnorm (A:real^N^N))`] REAL_LT_TRANS) THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`R:real`;`e / &2`;`A:real^N^N`] MATRIX_INV_SUB_CONVERGES_UNIFORMLY_CAUCHY_LMUL1) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN 
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^1^1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `fnorm(drop_drop (z: real^1^1) %% (A:real^N^N)) < &1` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN
     EXISTS_TAC `inv (fnorm (A:real^N^N))` THEN
     REWRITE_TAC[FNORM_MUL;drop_drop;GSYM FNORM_REAL] THEN
     ASM_SIMP_TAC[REAL_MUL_LID;REAL_MUL_RID;REAL_LT_IMP_NZ;REAL_LT_INV;REAL_MUL_RINV;REAL_ARITH `(x * y) * z = x * (y * z)`] THEN
     MATCH_MP_TAC REAL_LT_TRANS THEN
     EXISTS_TAC `R:real` THEN
     ASM_SIMP_TAC[];ALL_TAC] THEN
    MP_TAC (SPEC `drop_drop (z: real^1^1) %% (A:real^N^N)` MATRIX_INV_SUB_CONVERGES) THEN
    ASM_SIMP_TAC[] THEN 
    DISCH_THEN(fun th -> MP_TAC (ISPEC `A:real^N^N` (MATCH_MP MSERIES_LMUL th))) THEN
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
    EXISTS_TAC ` fnorm (--((A:real^N^N) ** msum (n + 1..n + M + 1) (\i. (drop_drop (z:real^1^1) %% A) matrix_pow i)) + 
    (msum (0..n) (\i. A ** (drop_drop z %% A) matrix_pow i) +
    msum (n + 1..n + M + 1) (\i. A ** (drop_drop z %% A) matrix_pow i)) - 
    A ** matrix_inv (mat 1 - drop_drop z %% A))` THEN CONJ_TAC THEN
    SIMP_TAC[FINITE_NUMSEG;GSYM MSUM_MATRIX_LMUL] THENL
    [SIMP_TAC[MATRIX_ARITH `!A B C:real^N^N.(--B) + (A + B) - C = A - C`;REAL_LE_REFL];
     SIMP_TAC[GSYM FNORM_TRIANGLE]]);;

let MATRIX_INV_SUB_CONVERGES_UNIFORMLY_LMUL1_ADD = prove
    (`!R e A:real^N^N c:real. &0 < e /\ &0 <= c /\ &0 < R /\ R < inv(fnorm A + c)
         ==> ?N. !n z:real^1^1. n >= N /\ fnorm(z) < R
            ==> fnorm(A ** msum(0..n) (\i. (drop_drop z %% A) matrix_pow i) - A ** matrix_inv(mat 1 - (drop_drop z %% A))) <= e`,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `A = (mat 0:real^N^N)` THENL
    [ASM_SIMP_TAC[MATRIX_MUL_LZERO;FNORM_0;MATRIX_SUB_REFL;REAL_LT_IMP_LE];ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE [GSYM FNORM_POS_LT]) THEN
    MP_TAC(SPECL [`R:real`;`e / &2`;`A:real^N^N`;`c:real`] MATRIX_INV_SUB_CONVERGES_UNIFORMLY_CAUCHY_LMUL1_ADD) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN 
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^1^1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `fnorm(drop_drop (z: real^1^1) %% (A:real^N^N)) < &1` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN
     EXISTS_TAC `inv (fnorm (A:real^N^N))` THEN
     REWRITE_TAC[FNORM_MUL;drop_drop;GSYM FNORM_REAL] THEN
     ASM_SIMP_TAC[REAL_MUL_LID;REAL_MUL_RID;REAL_LT_IMP_NZ;REAL_LT_INV;REAL_MUL_RINV;GSYM REAL_MUL_ASSOC] THEN
     MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `R:real` THEN ASM_SIMP_TAC[] THEN
     MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv (fnorm (A:real^N^N) + c)` THEN
     ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> x <= x + c`;REAL_LE_INV2]
     ;ALL_TAC] THEN
    MP_TAC (SPEC `drop_drop (z: real^1^1) %% (A:real^N^N)` MATRIX_INV_SUB_CONVERGES) THEN
    ASM_SIMP_TAC[] THEN 
    DISCH_THEN(fun th -> MP_TAC (ISPEC `A:real^N^N` (MATCH_MP MSERIES_LMUL th))) THEN
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
    EXISTS_TAC ` fnorm (--((A:real^N^N) ** msum (n + 1..n + M + 1) (\i. (drop_drop (z:real^1^1) %% A) matrix_pow i)) + 
    (msum (0..n) (\i. A ** (drop_drop z %% A) matrix_pow i) +
    msum (n + 1..n + M + 1) (\i. A ** (drop_drop z %% A) matrix_pow i)) - 
    A ** matrix_inv (mat 1 - drop_drop z %% A))` THEN CONJ_TAC THEN
    SIMP_TAC[FINITE_NUMSEG;GSYM MSUM_MATRIX_LMUL] THENL
    [SIMP_TAC[MATRIX_ARITH `!A B C:real^N^N.(--B) + (A + B) - C = A - C`;REAL_LE_REFL];
     SIMP_TAC[GSYM FNORM_TRIANGLE]]);;

(* ------------------------------------------------------------------------- *)
(* the derivative of log function in matrix space                            *)
(* ------------------------------------------------------------------------- *)
     
let HAS_M_DERIVATIVE_LOG = prove
    (`!A:real^N^N z:real^1^1. fnorm(drop_drop z %% A) < &1 ==> ((\z. matrix_log (drop_drop z %% A + mat 1)) has_m_derivative (A ** matrix_inv(drop_drop z %% A + mat 1))) (matrix_at z)`, 
     let lem = prove
     (`!n. from 1 INTER (0..n) = (1..n)`,
     REWRITE_TAC[from;INTER;IN_NUMSEG;EXTENSION;IN_ELIM_THM] THEN
     ARITH_TAC) in
     let lem1 = prove
     (`!x y:real. x < y <=> (?c. &0 < c /\ c + x = y)`,
     REPEAT GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_SUB_LT] THEN
     REWRITE_TAC[GSYM REAL_EQ_SUB_LADD] THEN
     SIMP_TAC[UNWIND_THM2;CONJ_SYM]) in
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `A = (mat 0:real^N^N)` THENL
    [ASM_SIMP_TAC[MATRIX_MUL_LZERO;MATRIX_CMUL_RZERO;HAS_M_DERIVATIVE_CONST];ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE [GSYM FNORM_POS_LT]) THEN
    SUBGOAL_THEN `fnorm (z:real^1^1) < inv(fnorm(A:real^N^N))` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN
     EXISTS_TAC `fnorm (A:real^N^N)` THEN
     REWRITE_TAC[GSYM FNORM_MUL;GSYM drop_drop;FNORM_REAL] THEN
     ASM_SIMP_TAC[REAL_MUL_LINV;REAL_LT_IMP_NZ;REAL_LT_INV];ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o ONCE_REWRITE_RULE [lem1]) THEN
    SUBGOAL_THEN `fnorm z < (inv(&2) * (fnorm(z:real^1^1) + inv(fnorm(A:real^N^N)))) /\ (inv(&2) * (fnorm z + inv(fnorm A))) < inv(fnorm A)` ASSUME_TAC THENL
    [FIRST_X_ASSUM(X_CHOOSE_TAC `c:real`) THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_EQ_SUB_LADD]) THEN
    ASM_ARITH_TAC;ALL_TAC] THEN
    MP_TAC(ISPECL
    [`matrix_ball(mat 0:real^1^1,(inv(&2) * (fnorm(z:real^1^1) + inv(fnorm(A:real^N^N)))))`;
    `\n z:real^1^1. ((-- &1) pow (n + 1) / &n) %% (((drop_drop z %% (A:real^N^N) + mat 1) - mat 1) matrix_pow n)`;
    `\n z:real^1^1. if n = 0 then (mat 0:real^N^N)
                    else ((-- &1) pow (n + 1)) %% (A ** (((drop_drop z %% (A:real^N^N) + mat 1) - mat 1) matrix_pow (n - 1)))`;
    `\z:real^1^1. A ** matrix_inv(drop_drop z %% (A:real^N^N) + mat 1)`;
    `(from 1)`]
    HAS_M_DERIVATIVE_SERIES) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE [MATRIX_ADD_SYM] MATRIX_ADD_SUB] THEN
    REWRITE_TAC[MATRIX_CONVEX_BALL; IN_MATRIX_BALL; matrix_dist] THEN 
    SIMP_TAC[HAS_M_DERIVATIVE_WITHIN_OPEN; MATRIX_OPEN_BALL; IN_MATRIX_BALL;
             matrix_dist; MATRIX_SUB_LZERO; FNORM_NEG] THEN
    ANTS_TAC THEN REPEAT CONJ_TAC THENL
    [X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
     COND_CASES_TAC;ALL_TAC;ALL_TAC;ALL_TAC] THENL 
    [ASM_SIMP_TAC[real_div;REAL_INV_0;REAL_MUL_RZERO;MATRIX_CMUL_LZERO;HAS_M_DERIVATIVE_CONST]; ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC] THENL
    [REWRITE_TAC[real_div;GSYM MATRIX_CMUL_ASSOC] THEN
     MATCH_MP_TAC HAS_M_DERIVATIVE_CMUL THEN
     SIMP_TAC[MATRIX_POW_CMUL;MATRIX_MUL_RMUL] THEN
     SIMP_TAC[MESON [GSYM MATRIX_POW_1;MATRIX_POW_ADD] `(A:real^N^N) ** A matrix_pow (n - 1) = A matrix_pow (1 + (n - 1))`] THEN
     ONCE_REWRITE_TAC[ADD_SYM] THEN
     ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> 1 <= n`;SUB_ADD] THEN
     ONCE_REWRITE_TAC[GSYM (ISPEC `drop_drop x pow (n - 1)` REAL_MUL_LID)] THEN
     POP_ASSUM MP_TAC THEN
     SIMP_TAC[REAL_FIELD `!x:real. ~(x = &0) <=> &1 = inv x * x`;GSYM REAL_OF_NUM_EQ] THEN
     STRIP_TAC THEN REWRITE_TAC[GSYM MATRIX_CMUL_ASSOC] THEN
     MATCH_MP_TAC HAS_M_DERIVATIVE_CMUL THEN
     SIMP_TAC[GSYM MATRIX_POW_CMUL;MATRIX_CMUL_ASSOC;HAS_M_DERIVATIVE_POW_AT];
     ALL_TAC;ALL_TAC;ALL_TAC] THENL    
     [REPEAT STRIP_TAC THEN
      SIMP_TAC[lem] THEN
     SIMP_TAC[FINITE_NUMSEG;MSUM_CASES;MSUM_0;MATRIX_ADD_LID] THEN
     REWRITE_TAC[IN_NUMSEG;ARITH_RULE `(1 <= i /\ i <= n) /\ ~(i = 0) <=> (1 <= i /\ i <= n)`] THEN
     REWRITE_TAC[GSYM IN_NUMSEG;SET_RULE `{i | i IN s} = s`] THEN
     MP_TAC(SPECL [`(inv(&2) * (fnorm(z:real^1^1) + inv(fnorm(A:real^N^N))))`; `e:real`;`-- A:real^N^N`] MATRIX_INV_SUB_CONVERGES_UNIFORMLY_LMUL1) THEN
     ANTS_TAC THENL
     [ASM_SIMP_TAC[FNORM_NEG] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `fnorm(z:real^1^1)` THEN
      ASM_SIMP_TAC[FNORM_POS_LE]
     ;ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
     EXISTS_TAC `N + 1` THEN
     REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`n - 1`;`x:real^1^1`]) THEN
     ASM_SIMP_TAC[ARITH_RULE `n >= N + 1 ==> n - 1 >= N`] THEN
     SIMP_TAC[MATRIX_CMUL_RNEG;MATRIX_SUB_RNEG] THEN
     SIMP_TAC[FINITE_NUMSEG;GSYM MSUM_MATRIX_LMUL;GSYM MATRIX_MUL_RMUL] THEN
     SIMP_TAC[GSYM MATRIX_CMUL_LNEG;MATRIX_POW_CMUL;MATRIX_CMUL_ASSOC] THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM FNORM_NEG] THEN
     REWRITE_TAC[GSYM MATRIX_SUB_LDISTRIB;MATRIX_MUL_LNEG;MATRIX_NEG_NEG] THEN
     MATCH_MP_TAC (REAL_ARITH `a = b ==> a <= e ==> b <= e`) THEN
     REPEAT AP_TERM_TAC THEN
     GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [MATRIX_ADD_SYM] THEN
     REWRITE_TAC[MATRIX_ARITH `!A B C:real^N^N. A - B = C - B <=> A = C`] THEN
     SIMP_TAC[CART_EQ;MSUM_COMPONENT] THEN
     REPEAT STRIP_TAC THEN
     MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
     MAP_EVERY EXISTS_TAC [`(\i:num. i + 1)`;`(\i:num. i - 1)`] THEN
     ASM_SIMP_TAC[IN_NUMSEG] THEN
     CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC[ADD_SUB;ARITH_RULE `((x + 1) + 1) = x + 2`] THEN
     REWRITE_TAC[REAL_ARITH `(-- &1) pow 2 = &1`;REAL_POW_ADD;REAL_MUL_RID] THEN
     REWRITE_TAC[GSYM REAL_POW_MUL;REAL_MUL_LID;REAL_MUL_LNEG] THEN
     ASM_ARITH_TAC;ALL_TAC;ALL_TAC] THENL
     [MAP_EVERY EXISTS_TAC [`mat 0:real^1^1`; `(mat 0:real^N^N)`] THEN 
        SIMP_TAC[FNORM_0;DROP2_MAT;MATRIX_CMUL_LZERO] THEN 
        ASM_SIMP_TAC[REAL_LT_INV;REAL_ARITH `&0 < x ==> &0 < x + &1`] THEN
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [num_CONV `1`] THEN
        SIMP_TAC[ADD1;GSYM MSUMS_REINDEX] THEN
        REWRITE_TAC[GSYM ADD1;MATRIX_POW_0;MATRIX_CMUL_RZERO;MSERIES_0] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `fnorm(z:real^1^1)` THEN
      ASM_SIMP_TAC[FNORM_POS_LE];
        ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^1^1->real^N^N` MP_TAC) THEN 
    SUBGOAL_THEN `!x:real^1^1. fnorm x < inv (&2) * (fnorm (z:real^1^1) + inv (fnorm (A:real^N^N))) ==> fnorm (drop_drop x %% A) < &1` ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN
     EXISTS_TAC `inv(fnorm (A:real^N^N))` THEN
     REWRITE_TAC[FNORM_MUL;drop_drop;GSYM FNORM_REAL] THEN
     ASM_SIMP_TAC[REAL_MUL_RINV;REAL_LT_IMP_NZ;REAL_LT_INV;GSYM REAL_MUL_ASSOC;REAL_MUL_LID;REAL_MUL_RID] THEN
     POP_ASSUM MP_TAC THEN
     MATCH_MP_TAC (REAL_ARITH `y < z ==> x < y ==> x < z`) THEN
     ASM_ARITH_TAC
    ;ALL_TAC] THEN
    ASM_SIMP_TAC[REWRITE_RULE [(ONCE_REWRITE_RULE [MATRIX_ADD_SYM] MATRIX_ADD_SUB)] (ISPEC `(drop_drop x %% (A:real^N^N) + mat 1)` MATRIX_LOG_CONVERGES_UNIQUE)] THEN 
    STRIP_TAC THEN
    MATCH_MP_TAC HAS_M_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`g:real^1^1->real^N^N`; `inv (&2) * (fnorm (z:real^1^1) + inv (fnorm (A:real^N^N))) - fnorm (z:real^1^1)`] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
    [POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC `w:real^1^1` THEN MATCH_MP_TAC MONO_IMP THEN SIMP_TAC[] THEN
    ONCE_SIMP_TAC[GSYM (ISPECL [`matrix_dist(w:real^1^1,z)`;`inv (&2) * (fnorm (z:real^1^1) + inv (fnorm (A:real^N^N))) - fnorm z`;`fnorm(z:real^1^1)`] REAL_LT_RADD)] THEN
    SIMP_TAC[matrix_dist;REAL_SUB_ADD] THEN
    MATCH_MP_TAC (REAL_ARITH `x <= y ==> y < z ==> x < z`) THEN
    SIMP_TAC[FNORM_TRIANGLE_SUB;REAL_ADD_SYM];ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^1^1`) THEN ASM_SIMP_TAC[]);;  

let HAS_M_DERIVATIVE_COMPONENTWISE_AT = prove
    (`!f:real^1^1->real^N^M f' x. 
        (f has_m_derivative f') (matrix_at x) <=>
        !i j. (1 <= i /\ i <= dimindex(:M)) /\ (1 <= j /\ j <= dimindex(:N))
        ==> ((\x. lift_lift(f(x)$i$j)) has_matrix_derivative 
                             (\x. lift_lift ((drop_drop x %% f')$i$j))) (matrix_at x)`,
    SIMP_TAC[has_m_derivative;GSYM HAS_MATRIX_DERIVATIVE_COMPONENTWISE_AT]);;

(*
g `!f:real^1^1->real^N^N z f'. 
fnorm(f(z) - mat 1) < &1  /\ (f has_m_derivative f' z) (matrix_at z)
==> ((\z. matrix_log (f z)) has_m_derivative (f'(z) ** matrix_inv(f(z)))) (matrix_at z)`

MP_TAC(ISPECL
   [`matrix_ball(mat 0:real^1^1,(inv(&2) * (fnorm(z:real^1^1) + inv(fnorm((f':real^1^1->real^N^N) z)))))`;
    `\n z:real^1^1. ((-- &1) pow (n + 1) / &n) %% ((((f:real^1^1->real^N^N) z) - mat 1) matrix_pow n)`;
    `\n z:real^1^1. if n = 0 then (mat 0:real^N^N)
                    else ((-- &1) pow (n + 1)) %% (((f':real^1^1->real^N^N) z) ** ((((f:real^1^1->real^N^N) z) - mat 1) matrix_pow (n - 1)))`;
    `\z:real^1^1. ((f':real^1^1->real^N^N) z) ** matrix_inv((f:real^1^1->real^N^N) z)`;
    `(from 1)`]
   HAS_M_DERIVATIVE_SERIES) THEN
   REWRITE_TAC[ONCE_REWRITE_RULE [MATRIX_ADD_SYM] MATRIX_ADD_SUB] THEN
   REWRITE_TAC[MATRIX_CONVEX_BALL; IN_MATRIX_BALL; matrix_dist] THEN 
   SIMP_TAC[HAS_M_DERIVATIVE_WITHIN_OPEN; MATRIX_OPEN_BALL; IN_MATRIX_BALL;
           matrix_dist; MATRIX_SUB_LZERO; FNORM_NEG] THEN
   ANTS_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC;ALL_TAC;ALL_TAC;ALL_TAC] THENL
*)

(* ------------------------------------------------------------------------- *)
(* homogeneous transformation of tangent vector                              *)
(* ------------------------------------------------------------------------- *)

let homo_trans_derivative = new_definition
    `(homo_trans_derivative:real^N->real^N^N->real^(N,1)finite_sum^(N,1)finite_sum) x R = 
     (lambda i j. if i = (dimindex(:N) + 1) then &0
                      else if ~(i = dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then x$i
                           else R$i$j)`;;

let homo_vector = new_definition
    `(homo_vector:real^N->real^(N,1)finite_sum) x = 
     (lambda i. if i = (dimindex(:N) + 1) then &0
                 else x$i )`;;

let HOMO_TRANS_DERIVATIVE_COMPONENT = prove
    (`!x:real^N R:real^N^N i j.
        1 <= i /\ i <= dimindex(:N) + 1 /\
        1 <= j /\ j <= dimindex(:N) + 1 ==>
        (homo_trans_derivative x R)$i$j = 
        (if i = (dimindex(:N) + 1) then &0
                 else if ~(i = dimindex(:N) + 1) /\ (j = dimindex(:N) + 1) then x$i
                           else R$i$j)`,
     SIMP_TAC[homo_trans_derivative;LAMBDA_BETA;DIMINDEX_FINITE_SUM;DIMINDEX_1]);;
                 
let HOMO_TRANS_DERIVATIVE_MUL_VECTOR = prove    
    (`!x y:real^N R:real^N^N. (homo_trans_derivative x R) ** (homo_vector y) = homo_vector (R ** y)`,
    REPEAT GEN_TAC THEN 
    SIMP_TAC[homo_trans_derivative;homo_vector;
             CART_EQ;LAMBDA_BETA;matrix_vector_mul] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;
             ARITH_RULE `x + 1 = SUC x`;ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG;REAL_MUL_RZERO] THEN
    GEN_TAC THEN DISCH_TAC THEN
    COND_CASES_TAC THENL 
    [SIMP_TAC[REAL_MUL_LZERO;SUM_0;REAL_ADD_RID]; ALL_TAC] THEN
    SIMP_TAC[GSYM matrix_vector_mul;REAL_ADD_RID] THEN
    UNDISCH_TAC `1 <= i /\ i <= SUC (dimindex (:N))` THEN
    UNDISCH_TAC `~(i = SUC (dimindex (:N)))` THEN
    SIMP_TAC[TAUT `~P /\ Q /\ (P \/ R) <=> (~P /\ Q /\ R)`;
             GSYM IMP_CONJ;LE;dot;MATRIX_VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN BETA_TAC THEN
    SIMP_TAC[ARITH_RULE `i <= x ==> ~(i = SUC x)`]);;
    
let HOMO_TRANS_DERIVATIVE_MUL_POINT = prove    
    (`!x y:real^N R:real^N^N. (homo_trans_derivative x R) ** (homo_point (mk_point y)) = homo_vector (R ** y + x)`,
    REPEAT GEN_TAC THEN 
    SIMP_TAC[homo_trans_derivative;homo_vector;HOMO_POINT_MK_POINT;
             CART_EQ;LAMBDA_BETA;matrix_vector_mul] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;
             ARITH_RULE `x + 1 = SUC x`;ARITH_RULE `1 <= x ==> 1 <= SUC x`;
             DIMINDEX_GE_1;SUM_CLAUSES_NUMSEG;REAL_MUL_RZERO] THEN
    GEN_TAC THEN DISCH_TAC THEN
    COND_CASES_TAC THENL 
    [SIMP_TAC[REAL_MUL_LZERO;SUM_0;REAL_ADD_RID]; ALL_TAC] THEN
    SIMP_TAC[GSYM matrix_vector_mul;REAL_ADD_RID;VECTOR_ADD_COMPONENT;
             REAL_MUL_RID;REAL_EQ_ADD_RCANCEL] THEN
    UNDISCH_TAC `1 <= i /\ i <= SUC (dimindex (:N))` THEN
    UNDISCH_TAC `~(i = SUC (dimindex (:N)))` THEN
    SIMP_TAC[TAUT `~P /\ Q /\ (P \/ R) <=> (~P /\ Q /\ R)`;
             GSYM IMP_CONJ;LE;dot;MATRIX_VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN BETA_TAC THEN
    SIMP_TAC[ARITH_RULE `i <= x ==> ~(i = SUC x)`]);;
    
let HOMO_TRANS_DERIVATIVE_MUL_TRANS_POINT = prove
    (`!x1 x2 y:real^N R1 R2:real^N^N. 
    (homo_trans_derivative x1 R1) ** (homo_trans_derivative x2 R2) ** (homo_point (mk_point y)) = homo_vector (R1 ** R2 ** y + R1 ** x2)`,
    REWRITE_TAC[HOMO_TRANS_DERIVATIVE_MUL_POINT;HOMO_TRANS_DERIVATIVE_MUL_VECTOR;MATRIX_VECTOR_MUL_ADD_LDISTRIB]);;

let HOMO_TRANS_DERIVATIVE_MUL = prove 
    (`!x1 x2 :real^N R1 R2:real^N^N. (homo_trans_derivative x1 R1) ** (homo_trans_derivative x2 R2) = homo_trans_derivative (R1 ** x2) (R1 ** R2)`,
    SIMP_TAC[MATRIX_EQ_HOMO_POINT;HOMO_TRANS_DERIVATIVE_MUL_POINT;HOMO_TRANS_DERIVATIVE_MUL_TRANS_POINT;GSYM MATRIX_VECTOR_MUL_ASSOC]);;
    
let HOMO_TRANS_DERIVATIVE_POW = prove
    (`!x:real^N R:real^N^N n:num. (homo_trans_derivative x R) matrix_pow n = if n = 0 then mat 1 else homo_trans_derivative (R matrix_pow (n - 1) ** x) (R matrix_pow n)`,
    GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
    [SIMP_TAC[matrix_pow]; ALL_TAC] THEN
    ASM_SIMP_TAC[ADD1;ADD_SUB;matrix_pow;ARITH_RULE `~(n + 1 = 0)`] THEN
    COND_CASES_TAC THENL
    [ASM_SIMP_TAC[matrix_pow;MATRIX_MUL_RID;MATRIX_VECTOR_MUL_LID];ALL_TAC] THEN
    ASM_SIMP_TAC[HOMO_TRANS_DERIVATIVE_MUL;(MESON [ARITH_RULE `~(n = 0) ==> n = 1 + (n - 1)`;GSYM MATRIX_POW_ADD] `~(n = 0) ==> R matrix_pow n = R matrix_pow 1 ** R matrix_pow (n - 1)`);MATRIX_POW_1;MATRIX_VECTOR_MUL_ASSOC]);;
                
let HOMO_TRANS_DERIVATIVE_POW_GE_1 = prove                
    (`!x:real^N R:real^N^N n:num. 1 <= n ==> (homo_trans_derivative x R) matrix_pow n = homo_trans_derivative (R matrix_pow (n - 1) ** x) (R matrix_pow n)`,                 
    SIMP_TAC[ARITH_RULE `(1 <= n) ==> ~( n = 0)`;HOMO_TRANS_DERIVATIVE_POW]);;
                 
let  HOMO_TRANS_DERIVATIVE_LMUL = prove
    (`!x1 x2:real^N R1 R2:real^N^N. homo_trans x1 R1 ** homo_trans_derivative x2 R2 = 
    homo_trans_derivative (R1 ** x2) (R1 ** R2)`,
    REPEAT GEN_TAC THEN
    SIMP_TAC[CART_EQ;LAMBDA_BETA;matrix_mul;homo_trans_derivative;homo_trans;
    MATRIX_VECTOR_MUL_COMPONENT;dot;DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [ASM_SIMP_TAC[] THEN 
    MATCH_MP_TAC SUM_EQ_0 THEN ARITH_TAC;ALL_TAC] THEN COND_CASES_TAC THENL 
    [ASM_SIMP_TAC[] THEN SIMP_TAC[COND_RAND;REAL_MUL_RZERO] THEN 
    ONCE_SIMP_TAC[GSYM COND_SWAP] THEN SIMP_TAC[SUM_ADD_SPLIT;ARITH_RULE `1 <= n + 1`;
    SUM_SING_NUMSEG;REAL_ADD_RID] THEN ASM_SIMP_TAC[matrix_vector_mul;LAMBDA_BETA;
    ARITH_RULE `i <= N + 1 <=> i <= N \/ i = N + 1`;
    ARITH_RULE `~(i = N + 1) /\ (i <= N + 1) ==> i <= N`] THEN 
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN 
    ASM_ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[] THEN SIMP_TAC[COND_RAND;REAL_MUL_RZERO] THEN 
    ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN 
    SIMP_TAC[SUM_ADD_SPLIT;ARITH_RULE `1 <= n + 1`;SUM_SING_NUMSEG;
    REAL_ADD_RID] THEN ASM_SIMP_TAC[LAMBDA_BETA;
    ARITH_RULE `~(i = N + 1) /\ (i <= N + 1) ==> i <= N`] THEN 
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN ARITH_TAC);;
                 
let  HOMO_TRANS_DERIVATIVE_RMUL = prove
    (`!x1 x2:real^N R1 R2:real^N^N. homo_trans_derivative x2 R2 ** homo_trans x1 R1 = 
    homo_trans_derivative (R2 ** x1 + x2) (R2 ** R1) `,
    REPEAT GEN_TAC THEN 
    SIMP_TAC[CART_EQ;LAMBDA_BETA;matrix_mul;homo_trans_derivative;homo_trans;MATRIX_VECTOR_MUL_COMPONENT;dot;VECTOR_ADD_COMPONENT;DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_EQ_0 THEN
    ARITH_TAC;ALL_TAC] THEN COND_CASES_TAC THENL [ASM_SIMP_TAC[] THEN 
    SIMP_TAC[COND_RAND;REAL_MUL_RID] THEN 
    ONCE_SIMP_TAC[GSYM COND_SWAP] THEN SIMP_TAC[SUM_ADD_SPLIT;ARITH_RULE `1 <= n + 1`] THEN 
    SIMP_TAC[SUM_SING_NUMSEG] THEN
    ASM_SIMP_TAC[matrix_vector_mul;LAMBDA_BETA;
    ARITH_RULE `i <= N + 1 <=> i <= N \/ i = N + 1`] THEN
    ASM_SIMP_TAC[matrix_vector_mul;LAMBDA_BETA;
    ARITH_RULE `~(i = N + 1) /\ (i <= N + 1) ==> i <= N`] THEN
    SIMP_TAC[ARITH_RULE `!a b c:real. a +c = b + c <=> a = b `] THEN 
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN ASM_ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[] THEN 
    SIMP_TAC[COND_RAND;REAL_MUL_RZERO] THEN ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN 
    SIMP_TAC[SUM_ADD_SPLIT;ARITH_RULE `1 <= n + 1`] THEN 
    SIMP_TAC[SUM_SING_NUMSEG;REAL_ADD_RID] THEN 
    ASM_SIMP_TAC[LAMBDA_BETA;ARITH_RULE `~(i = N + 1) /\ (i <= N + 1) ==> i <= N`] THEN 
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN ARITH_TAC);;

let HOMO_TRANS_DERIVATIVE_CMUL = prove 
    (`!c:real x:real^N R:real^N^N. c %% homo_trans_derivative x R = 
    homo_trans_derivative (c % x) (c %% R)`,
    REPEAT GEN_TAC THEN SIMP_TAC[CART_EQ;LAMBDA_BETA;homo_trans_derivative;
    MATRIX_CMUL_COMPONENT;VECTOR_MUL_COMPONENT;DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN 
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN COND_CASES_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN ASM_ARITH_TAC);;
    
let HOMO_TRANS_DERIVATIVE_EQ_MAT = prove 
    (`homo_trans_derivative ((vec 0):real^N) (mat 0) = mat 0`,
     MP_TAC (ISPEC `&0` HOMO_TRANS_DERIVATIVE_CMUL) THEN
     SIMP_TAC[MATRIX_CMUL_LZERO;VECTOR_MUL_LZERO;EQ_SYM_EQ]);;
     
let HOMO_TRANS_DERIVATIVE_ADD_MAT = prove 
    (`!x:real^N R:real^N^N. homo_trans_derivative x R + (mat 1:real^(N,1)finite_sum^(N,1)finite_sum) = homo_trans x (R + (mat 1:real^N^N))`,
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM HOMO_TRANS_EQ_MAT] THEN
    SIMP_TAC[CART_EQ;LAMBDA_BETA;HOMO_TRANS_COMPONENT;HOMO_TRANS_DERIVATIVE_COMPONENT;MATRIX_ADD_COMPONENT;VEC_COMPONENT;DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    ARITH_TAC);;
    
let HOMO_TRANS_SUB_MAT = prove 
    (`!x:real^N R:real^N^N. homo_trans x R - (mat 1:real^(N,1)finite_sum^(N,1)finite_sum) = homo_trans_derivative x (R - (mat 1:real^N^N))`,
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM HOMO_TRANS_EQ_MAT] THEN
    SIMP_TAC[CART_EQ;LAMBDA_BETA;HOMO_TRANS_COMPONENT;HOMO_TRANS_DERIVATIVE_COMPONENT;MATRIX_SUB_COMPONENT;VEC_COMPONENT;DIMINDEX_FINITE_SUM;DIMINDEX_1] THEN
    ARITH_TAC);;
                           
let LINEAR_DROP_CMUL = prove
    (`!A:real^N x: real^1. linear (\x. drop x % A)`,
    REPEAT GEN_TAC THEN REWRITE_TAC [linear] THEN 
    SIMP_TAC [DROP_ADD; DROP_CMUL] THEN 
    SIMP_TAC [VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC]);;  
    
(* ------------------------------------------------------------------------- *)
(* the derivative of homogeneous transformation of tangent vector            *)
(* ------------------------------------------------------------------------- *)

let HAS_M_DERIVATIVE_HOMO_TRANS = prove
    (`!x R t:real^1^1 x':real->real^N R':real->real^N^N.
        ((\z. x (drop z)) has_vector_derivative (x' (drop_drop t))) (at (lift(drop_drop t))) /\
        ((\z. R (drop_drop z)) has_m_derivative (R' (drop_drop t))) (matrix_at t) ==>
        ((\z. homo_trans (x (drop_drop z)) (R (drop_drop z))) has_m_derivative
            homo_trans_derivative (x' (drop_drop t)) (R' (drop_drop t)))
            (matrix_at t)`,
    ONCE_SIMP_TAC[HAS_M_DERIVATIVE_COMPONENTWISE_AT;has_vector_derivative] THEN
    ONCE_SIMP_TAC[HAS_DERIVATIVE_COMPONENTWISE_AT] THEN
    SIMP_TAC[MATRIX_CMUL_COMPONENT;VECTOR_MUL_COMPONENT;LIFT_CMUL;LIFT2_CMUL] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `i <= N + 1 <=> i = N + 1 \/ i <= N`] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[HOMO_TRANS_COMPONENT;HOMO_TRANS_DERIVATIVE_COMPONENT;LE_REFL;ARITH_RULE `1 <= N + 1`;ARITH_RULE `i <= N ==> i <= N + 1`;ARITH_RULE `i <= N ==> ~(i = N + 1)`] THEN
    SIMP_TAC[LIFT2_NUM;MATRIX_CMUL_RZERO;HAS_MATRIX_DERIVATIVE_CONST] THEN
    SIMP_TAC[HAS_MATRIX_DERIVATIVE_AT;MLINEAR_DROP2_CMUL] THEN
    FIRST_X_ASSUM(ASSUME_TAC o SPECL [`i:num`;`j:num`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_AT;LINEAR_DROP_CMUL] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN 
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th THEN ASM_SIMP_TAC[]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift(drop_drop x'')`) THEN
    SIMP_TAC[GSYM LIFT_SUB;GSYM LIFT2_SUB;GSYM VECTOR_SUB_COMPONENT] THEN
    SIMP_TAC[LIFT_DROP;GSYM DROP2_SUB] THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[NORM_LIFT;drop_drop;GSYM FNORM_REAL];ALL_TAC] THEN
    MATCH_MP_TAC (REAL_ARITH `a = b ==> (a < e ==> b < e)`) THEN
    SIMP_TAC[real_div;NORM_LIFT;drop_drop;GSYM FNORM_REAL;REAL_EQ_MUL_RCANCEL] THEN
    DISJ1_TAC THEN SIMP_TAC[NORM_REAL;FNORM_REAL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM drop;GSYM drop_drop;DROP_SUB;DROP2_SUB;LIFT_DROP;LIFT_DROP2;DROP_CMUL;DROP2_CMUL]);;
    
let HAS_M_DERIVATIVE_HOMO_TRANS_DERIVATIVE_IMP = prove
    (`!x R t:real^1^1 x':real->real^N R':real->real^N^N.
        ((\z. x (drop z)) has_vector_derivative (x' (drop_drop t))) (at (lift(drop_drop t))) /\
        ((\z. R (drop_drop z)) has_m_derivative (R' (drop_drop t))) (matrix_at t) ==>
        ((\z. homo_trans_derivative (x (drop_drop z)) (R (drop_drop z))) has_m_derivative
            homo_trans_derivative (x' (drop_drop t)) (R' (drop_drop t)))
            (matrix_at t)`,
    ONCE_SIMP_TAC[HAS_M_DERIVATIVE_COMPONENTWISE_AT;has_vector_derivative] THEN
    ONCE_SIMP_TAC[HAS_DERIVATIVE_COMPONENTWISE_AT] THEN
    SIMP_TAC[MATRIX_CMUL_COMPONENT;VECTOR_MUL_COMPONENT;LIFT_CMUL;LIFT2_CMUL] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `i <= N + 1 <=> i = N + 1 \/ i <= N`] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[HOMO_TRANS_DERIVATIVE_COMPONENT;LE_REFL;ARITH_RULE `1 <= N + 1`;ARITH_RULE `i <= N ==> i <= N + 1`;ARITH_RULE `i <= N ==> ~(i = N + 1)`] THEN
    SIMP_TAC[LIFT2_NUM;MATRIX_CMUL_RZERO;HAS_MATRIX_DERIVATIVE_CONST] THEN
    SIMP_TAC[HAS_MATRIX_DERIVATIVE_AT;MLINEAR_DROP2_CMUL] THEN
    FIRST_X_ASSUM(ASSUME_TAC o SPECL [`i:num`;`j:num`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_AT;LINEAR_DROP_CMUL] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN 
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th THEN ASM_SIMP_TAC[]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift(drop_drop x'')`) THEN
    SIMP_TAC[GSYM LIFT_SUB;GSYM LIFT2_SUB;GSYM VECTOR_SUB_COMPONENT] THEN
    SIMP_TAC[LIFT_DROP;GSYM DROP2_SUB] THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[NORM_LIFT;drop_drop;GSYM FNORM_REAL];ALL_TAC] THEN
    MATCH_MP_TAC (REAL_ARITH `a = b ==> (a < e ==> b < e)`) THEN
    SIMP_TAC[real_div;NORM_LIFT;drop_drop;GSYM FNORM_REAL;REAL_EQ_MUL_RCANCEL] THEN
    DISJ1_TAC THEN SIMP_TAC[NORM_REAL;FNORM_REAL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM drop;GSYM drop_drop;DROP_SUB;DROP2_SUB;LIFT_DROP;LIFT_DROP2;DROP_CMUL;DROP2_CMUL]);;
    
let HAS_M_DERIVATIVE_HOMO_TRANS_DERIVATIVE_IMP1 = prove
    (`!x R t:real^1^1 x':real->real^N R':real->real^N^N.
    ((\z. homo_trans_derivative (x (drop_drop z)) (R (drop_drop z))) has_m_derivative
            homo_trans_derivative (x' (drop_drop t)) (R' (drop_drop t)))
            (matrix_at t) ==>
        ((\z. x (drop z)) has_vector_derivative (x' (drop_drop t))) (at (lift(drop_drop t))) /\
        ((\z. R (drop_drop z)) has_m_derivative (R' (drop_drop t))) (matrix_at t)`,
    ONCE_SIMP_TAC[HAS_M_DERIVATIVE_COMPONENTWISE_AT;has_vector_derivative] THEN
    ONCE_SIMP_TAC[HAS_DERIVATIVE_COMPONENTWISE_AT] THEN
    SIMP_TAC[MATRIX_CMUL_COMPONENT;VECTOR_MUL_COMPONENT;LIFT_CMUL;LIFT2_CMUL] THEN
    SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `i <= N + 1 <=> i = N + 1 \/ i <= N`] THEN
    REPEAT STRIP_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `(dimindex (:N) + 1)`]);
     FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`;`j:num`])] THEN
    ASM_SIMP_TAC[HOMO_TRANS_DERIVATIVE_COMPONENT;LE_REFL;ARITH_RULE `1 <= N + 1`;ARITH_RULE `i <= N ==> i <= N + 1`;ARITH_RULE `i <= N ==> ~(i = N + 1)`] THEN
    SIMP_TAC[HAS_MATRIX_DERIVATIVE_AT;MLINEAR_DROP2_CMUL] THEN
    SIMP_TAC[HAS_DERIVATIVE_AT;LINEAR_DROP_CMUL] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN 
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th THEN ASM_SIMP_TAC[]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift_lift(drop x'')`) THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[NORM_REAL;FNORM_REAL;VECTOR_SUB_COMPONENT;MATRIX_SUB_COMPONENT] THEN
    REWRITE_TAC[MATRIX_CMUL_COMPONENT;VECTOR_MUL_COMPONENT;REAL_SUB_RDISTRIB;DROP2_SUB;DROP_SUB] THEN
    SIMP_TAC[GSYM drop_drop;GSYM drop;LIFT_DROP;LIFT_DROP2]);;
    
let HAS_M_DERIVATIVE_HOMO_TRANS_DERIVATIVE_EQ = prove
    (`!x R t:real^1^1 x':real->real^N R':real->real^N^N.
    ((\z. homo_trans_derivative (x (drop_drop z)) (R (drop_drop z))) has_m_derivative
            homo_trans_derivative (x' (drop_drop t)) (R' (drop_drop t)))
            (matrix_at t) <=>
        ((\z. x (drop z)) has_vector_derivative (x' (drop_drop t))) (at (lift(drop_drop t))) /\
        ((\z. R (drop_drop z)) has_m_derivative (R' (drop_drop t))) (matrix_at t)`,
    MESON_TAC[HAS_M_DERIVATIVE_HOMO_TRANS_DERIVATIVE_IMP1;HAS_M_DERIVATIVE_HOMO_TRANS_DERIVATIVE_IMP]);;
    
(* ------------------------------------------------------------------------- *)
(* the exponential of homogeneous transformation of tangent vector           *)
(* ------------------------------------------------------------------------- *)

let INFMSUM_ADD_LEFT = prove
    (`!f:num->real^N^N n. (!m. msummable (from m) f) ==> infmsum (from n) f = f n + infmsum (from (SUC n)) f`,
    ONCE_REWRITE_TAC[GSYM MSUMMABLE_RESTRICT] THEN
    ONCE_REWRITE_TAC[GSYM INFMSUM_RESTRICT] THEN
    REWRITE_TAC[MATRIX_ARITH `!A B C:real^N^N. A = B + C <=> A - C = B`] THEN
    SIMP_TAC[GSYM INFMSUM_SUB] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(\i. (if i IN from n then (f:num->real^N^N) i else mat 0) -
                    (if i IN from (SUC n) then f i else mat 0)) = 
                    (\i. (if i IN {n} then f i else mat 0))` SUBST1_TAC THENL
    [SIMP_TAC[FUN_EQ_THM] THEN
     SIMP_TAC[IN_ELIM_THM;from;IN_SING] THEN GEN_TAC THEN
     COND_CASES_TAC THENL
     [FIRST_X_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [ARITH_RULE `n <= x <=> SUC n <= x \/ (x = n)`]) THEN
      COND_CASES_TAC THENL
      [ASM_SIMP_TAC[ARITH_RULE `SUC n <= x ==> ~(x = n)`;MATRIX_SUB_REFL];
       ASM_SIMP_TAC[ARITH_RULE `(SUC n <= x \/ x = n) /\ ~(SUC n <= x) ==> x = n`;MATRIX_SUB_RZERO]]; ALL_TAC] THEN
     ASM_SIMP_TAC[ARITH_RULE `~(n <= x) ==> ~(SUC n <= x)`;ARITH_RULE `~((n:num) <= x) ==> ~(x = n)`;MATRIX_SUB_RZERO];ALL_TAC] THEN
    REWRITE_TAC[INFMSUM_RESTRICT] THEN
    MATCH_MP_TAC INFMSUM_UNIQUE THEN
    SIMP_TAC[msums;MATRIX_LIM_SEQUENTIALLY] THEN 
    REPEAT STRIP_TAC THEN EXISTS_TAC `n:num` THEN
    ASM_SIMP_TAC[INTER;IN_NUMSEG;IN_SING;LE_0;ARITH_RULE `(n:num) <= m ==> (x = n /\ x <= m <=> x = n)`;SET_RULE `{x | x = n} = {n}`;MSUM_SING;MATRIX_DIST_REFL]);;

let MSERIES_COMPONENT = prove
    (`!f s l:real^N^M i j. (f msums l) s /\
                        1 <= i /\ i <= dimindex (:M) /\ 1 <= j /\ j <= dimindex (:N)
                    ==> ((\n. lift_lift(f(n)$i$j)) msums lift_lift(l$i$j)) s`,
    REPEAT GEN_TAC THEN REWRITE_TAC[msums] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    ASM_SIMP_TAC[GSYM LIFT2_SUM; GSYM MSUM_COMPONENT;
                 FINITE_INTER; FINITE_NUMSEG] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATRIX_LIM_COMPONENTWISE_LIFT2]) THEN
    ASM_SIMP_TAC[o_DEF]);;
    
let MSERIES_COMPONENT_EQ = prove
    (`!f s l:real^N^M. (f msums l) s <=>
        !i j. 1 <= i /\ i <= dimindex (:M) /\ 1 <= j /\ j <= dimindex (:N)
                    ==> ((\n. lift_lift(f(n)$i$j)) msums lift_lift(l$i$j)) s`,
    REPEAT GEN_TAC THEN REWRITE_TAC[msums] THEN
    SIMP_TAC[GSYM (REWRITE_RULE [o_DEF] LIFT2_SUM); GSYM MSUM_COMPONENT] THEN
    SIMP_TAC[GSYM (REWRITE_RULE [GSYM CONJ_ASSOC] MATRIX_LIM_COMPONENTWISE_LIFT2)]);;
    
let MSUMMABLE_COMPONENT = prove
    (`!f:num->real^N^M s i j.
        msummable s f /\ 1 <= i /\ i <= dimindex (:M) /\ 1 <= j /\ j <= dimindex (:N)
        ==> msummable s (\x. lift_lift(f(x)$i$j))`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `l:real^N^M` o REWRITE_RULE[msummable]) THEN
    REWRITE_TAC[msummable] THEN EXISTS_TAC `lift_lift((l:real^N^M)$i$j)` THEN
    ASM_SIMP_TAC[MSERIES_COMPONENT]);;
    
let MSUMMABLE_COLUMN_COMPONENT = prove
    (`!f:num->real^N^M s j.
        msummable s f /\ 1 <= j /\ j <= dimindex (:N)
        ==> summable s (\x. column j (f x))`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `l:real^N^M` o REWRITE_RULE[msummable]) THEN
    REWRITE_TAC[summable] THEN EXISTS_TAC `column j (l:real^N^M)` THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC[msums;MATRIX_LIM_COMPONENTWISE_REAL] THEN
    ASM_SIMP_TAC[column;LAMBDA_BETA;sums;LIM_COMPONENTWISE_REAL;VSUM_COMPONENT;MSUM_COMPONENT]);;

let MSUMMABLE_ROW_COMPONENT = prove
    (`!f:num->real^N^M s i.
        msummable s f /\ 1 <= i /\ i <= dimindex (:M)
        ==> summable s (\x. row i (f x))`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `l:real^N^M` o REWRITE_RULE[msummable]) THEN
    REWRITE_TAC[summable] THEN EXISTS_TAC `row i (l:real^N^M)` THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC[msums;MATRIX_LIM_COMPONENTWISE_REAL] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[row;LAMBDA_BETA;sums;LIM_COMPONENTWISE_REAL;VSUM_COMPONENT;MSUM_COMPONENT]);;

let TENDSTO_REAL_MATRIX = prove
    (`(s ---> l) = ((lift_lift o s) ->-> lift_lift l)`,
    REWRITE_TAC[FUN_EQ_THM; matrixtendsto; tendsto_real; o_THM; MATRIX_DIST_LIFT2]);;
  
let REAL_SUMS_MSUMS = prove
    (`(f real_sums l) = ((lift_lift o f) msums (lift_lift l))`,
    REWRITE_TAC[FUN_EQ_THM; msums; real_sums; TENDSTO_REAL_MATRIX] THEN
    SIMP_TAC[LIFT2_SUM; FINITE_INTER_NUMSEG; o_DEF]);;

let REAL_SUMMABLE_MSUMMABLE = prove
    (`real_summable s f <=> msummable s (lift_lift o f)`,
    REWRITE_TAC[real_summable; msummable; REAL_SUMS_MSUMS; GSYM EXISTS_LIFT2]);;

let INFMSUM_COMPONENT = prove
    (`!f:num->real^N^M s i j. 1 <= i /\ i <= dimindex (:M) /\ 1 <= j /\ j <= dimindex (:N) /\ msummable s f ==> (infmsum s f)$i$j = real_infsum s (\x. f(x)$i$j)`,
    REWRITE_TAC[GSYM MSUMS_INFSUM] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPECL [`f:num->real^N^M`;`s:num->bool`;`(infmsum s (f:num->real^N^M))`;`i:num`;`j:num`] MSERIES_COMPONENT) THEN
    ASM_SIMP_TAC[GSYM o_DEF;GSYM REAL_SUMS_MSUMS] THEN
    STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN ASM_SIMP_TAC[]);;
    
let INFSUM_COMPONENT = prove
    (`!f:num->real^N s k. 1 <= k /\ k <= dimindex (:N) /\ summable s f ==> (infsum s f)$k = real_infsum s (\x. f(x)$k)`,
    REWRITE_TAC[GSYM SUMS_INFSUM] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPECL [`f:num->real^N`;`s:num->bool`;`(infsum s (f:num->real^N))`;`k:num`] SERIES_COMPONENT) THEN
    ASM_SIMP_TAC[GSYM o_DEF;GSYM REAL_SUMS] THEN
    STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN ASM_SIMP_TAC[]);;

let HOMO_TRANS_DERIVATIVE_INFMSUM = prove
    (`!x:num->real^N R:num->real^N^N n:num.
    msummable (from n) (\n. homo_trans_derivative (x n) (R n)) ==> 
    infmsum (from n) (\n. homo_trans_derivative (x n) (R n)) = homo_trans_derivative (infsum (from n) (\n. x n)) (infmsum (from n) (\n. R n))`,
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;HOMO_TRANS_DERIVATIVE_COMPONENT;DIMINDEX_FINITE_SUM;DIMINDEX_1;INFMSUM_COMPONENT] THEN
    REWRITE_TAC[ARITH_RULE `i <= N + 1 <=> i = N + 1 \/ i <= N`] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_INFSUM_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `i <= N ==> ~(i = N + 1)`] THEN
    CONV_TAC SYM_CONV THEN SIMP_TAC[ETA_AX] THENL
    [MATCH_MP_TAC INFSUM_COMPONENT THEN
     MP_TAC (ISPECL [`(\n. homo_trans_derivative (x n) (R n)):num->real^(N,1)finite_sum^(N,1)finite_sum`;`from n`;`i':num`] MSUMMABLE_COLUMN_COMPONENT) THEN
     ASM_SIMP_TAC[DIMINDEX_FINITE_SUM;DIMINDEX_1;LE_REFL;ARITH_RULE `1 <= N + 1`] THEN
     SIMP_TAC[summable;SERIES_FROM;LIM_COMPONENTWISE_REAL;VSUM_COMPONENT] THEN
     DISCH_THEN(X_CHOOSE_TAC `l:real^(N,1)finite_sum`) THEN
     EXISTS_TAC `(lambda i. (l:real^(N,1)finite_sum)$i):real^N` THEN
     X_GEN_TAC `k:num` THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `k:num`);
     MATCH_MP_TAC INFMSUM_COMPONENT THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [msummable]) THEN
     ASM_SIMP_TAC[msummable;MSERIES_FROM;MATRIX_LIM_COMPONENTWISE_REAL;MSUM_COMPONENT] THEN
     DISCH_THEN(X_CHOOSE_TAC `l:real^(N,1)finite_sum^(N,1)finite_sum`) THEN
     EXISTS_TAC `(lambda i j. (l:real^(N,1)finite_sum^(N,1)finite_sum)$i$j):real^N^N` THEN
     MAP_EVERY X_GEN_TAC [`ki:num`;`kj:num`] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`ki:num`;`kj:num`])] THEN
    ASM_SIMP_TAC[column;LAMBDA_BETA;HOMO_TRANS_DERIVATIVE_COMPONENT;DIMINDEX_FINITE_SUM;DIMINDEX_1;LE_REFL;ARITH_RULE `1 <= N + 1`;ARITH_RULE `i <= N ==> i <= N + 1`;ARITH_RULE `i <= N ==> ~(i = N + 1)`]);;
    
let MSUM_VECTOR_MATRIX_MUL = prove  
   (`!f:num->real^N^M x:real^M s. 
        FINITE s ==> x ** (msum s f) = vsum s (\A. x ** f(A))`,
    GEN_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN 
    SIMP_TAC[VECTOR_MATRIX_MUL_TRANSP;MSUM_CLAUSES;VSUM_CLAUSES;TRANSP_MAT;MATRIX_VECTOR_MUL_LZERO;MATRIX_VECTOR_MUL_ADD_RDISTRIB;TRANSP_MATRIX_ADD]);;
        
let MSUM_MATRIX_VECTOR_MUL = prove  
   (`!f:num->real^N^M x:real^N s. 
        FINITE s ==> (msum s f) ** x = vsum s (\A. f(A) ** x)`,
    GEN_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN 
    SIMP_TAC[MSUM_CLAUSES;VSUM_CLAUSES;MATRIX_VECTOR_MUL_LZERO;MATRIX_VECTOR_MUL_ADD_RDISTRIB]);;

let MATRIX_LIM_VECTOR_LMUL = prove
    (`!net:(A)net f:A->real^N^M l x:real^M. (f ->-> l) net ==> 
        ((\A.  (x ** (f A))) -->  (x ** l)) net`,
    REPEAT GEN_TAC THEN 
    REWRITE_TAC[MATRIX_LIM_COMPONENTWISE_REAL;VECTOR_MATRIX_MUL_TRANSP] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT;LIM_COMPONENTWISE_REAL;dot;TRANSP_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LIMIT_REAL_SUM THEN 
    SIMP_TAC [FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN 
    MATCH_MP_TAC LIMIT_REAL_MUL THEN 
    ASM_SIMP_TAC[LIMIT_EQ_LIFT;LIMIT_EUCLIDEAN;o_DEF] THEN
    MATCH_MP_TAC LIM_COMPONENT THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN
    SIMP_TAC[EVENTUALLY_TRUE]);;
              
let MATRIX_LIM_VECTOR_RMUL = prove
    (`!net:(A)net f:A->real^N^M l x:real^N. (f ->-> l) net ==> 
        ((\A.  ((f A) ** x)) -->  (l ** x)) net`,
    REPEAT GEN_TAC THEN 
    REWRITE_TAC[MATRIX_LIM_COMPONENTWISE_REAL] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT;LIM_COMPONENTWISE_REAL;dot] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LIMIT_REAL_SUM THEN 
    SIMP_TAC [FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN 
    MATCH_MP_TAC LIMIT_REAL_MUL THEN 
    ASM_SIMP_TAC[LIMIT_EQ_LIFT;LIMIT_EUCLIDEAN;o_DEF] THEN
    MATCH_MP_TAC LIM_COMPONENT THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN
    SIMP_TAC[EVENTUALLY_TRUE]);;
    
let MSERIES_VECTOR_LMUL = prove
    (`!A:num->real^N^M A0 x:real^M s. (A msums A0) s ==> ((\n. x ** (A n)) sums (x ** A0)) s`,
    SIMP_TAC [msums;sums;FINITE_INTER_NUMSEG;GSYM MSUM_VECTOR_MATRIX_MUL; MATRIX_LIM_VECTOR_LMUL]);;
 
let MSERIES_VECTOR_RMUL = prove
    (`!A:num->real^N^M A0 x:real^N s. (A msums A0) s ==> ((\n. (A n) ** x) sums (A0 ** x)) s`,
    SIMP_TAC [msums;sums;FINITE_INTER_NUMSEG;GSYM MSUM_MATRIX_VECTOR_MUL; MATRIX_LIM_VECTOR_RMUL]);;

let INFMSUM_VECTOR_LMUL = prove
    (`!s A:num->real^N^M x:real^M. msummable s A ==>
        infsum s (\n. x ** (A n)) = x ** (infmsum s A)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INFSUM_UNIQUE THEN
    MATCH_MP_TAC MSERIES_VECTOR_LMUL THEN ASM_REWRITE_TAC[MSUMS_INFSUM]);;
 
let INFMSUM_VECTOR_RMUL = prove
    (`!s A:num->real^N^M x:real^N. msummable s A ==>
        infsum s (\n. (A n) ** x) = (infmsum s A) ** x`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INFSUM_UNIQUE THEN
    MATCH_MP_TAC MSERIES_VECTOR_RMUL THEN ASM_REWRITE_TAC[MSUMS_INFSUM]);;
    
let MSUMMABLE_EXP1 = prove    
    (`!A:real^N^N n:num. msummable (from n) (\n. &1 / &(FACT n) %% A matrix_pow (n - 1))`,
    let lem = MESON [REAL_ABS_REFL] `!x. &0 <= x ==> abs x = x` in
    let lem1 = prove
    (`!A:real^N^N n:num. num_of_real(fnorm (A:real^N^N)) + 1 <= n ==> fnorm (A matrix_pow (SUC n - 1)) = fnorm (A matrix_pow (SUC (n - 1)))`,
    REPEAT STRIP_TAC THEN REPEAT AP_TERM_TAC THEN
    MATCH_MP_TAC (ARITH_RULE `num_of_real(fnorm (A:real^N^N)) + 1 <= n ==> (SUC n - 1) = SUC (n - 1)`) THEN ASM_SIMP_TAC[]) in
    REPEAT GEN_TAC THEN REWRITE_TAC[msummable] THEN
    MATCH_MP_TAC MSERIES_RATIO THEN SIMP_TAC [GE;FNORM_MUL] THEN
    EXISTS_TAC `fnorm(A:real^N^N) * inv (fnorm(A) + &1)` THEN 
    EXISTS_TAC `num_of_real (fnorm(A:real^N^N)) + 1` THEN
    SIMP_TAC[FACT; matrix_pow;real_div;REAL_MUL_LID;lem1] THEN 
    SIMP_TAC[GSYM real_div] THEN 
    SIMP_TAC[FNORM_POS_LE; REAL_ARITH `&0 <= a ==> &0 < a + &1`;
             REAL_LT_LDIV_EQ] THEN CONJ_TAC THENL
    [REAL_ARITH_TAC; ALL_TAC] THEN GEN_TAC THEN
    SIMP_TAC[GSYM REAL_OF_NUM_LE; NUM_OF_REAL_ADD] THEN 
    SIMP_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUC] THEN 
    SIMP_TAC[FNORM_POS_LE; lem; REAL_LE_INV;LE_0;
             REAL_OF_NUM_LE; REAL_LE_ADD; REAL_ABS_MUL;REAL_INV_MUL;
             GSYM REAL_MUL_ASSOC] THEN 
    STRIP_TAC THEN 
    ONCE_REWRITE_TAC [REAL_ARITH `!c:real. a * b * c = b * a * c`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [SIMP_TAC[REAL_LT_INV; REAL_OF_NUM_LT; REAL_LE_LT; FACT_LT];ALL_TAC]
    THEN SIMP_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN 
    ONCE_REWRITE_TAC [REAL_ARITH `!c:real. a * b * c = b * a * c`] THEN 
    MATCH_MP_TAC REAL_LE_MUL2 THEN 
    SIMP_TAC[FNORM_SUBMULT; REAL_LE_ADD; REAL_OF_NUM_LE;
             FNORM_POS_LE;REAL_LE_INV; LE_0] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN 
    SIMP_TAC[FNORM_POS_LE; REAL_ARITH `&0 <= a ==> &0 < a + &1`] THEN
    MP_TAC (CONJUNCT2 (SPEC `fnorm (A:real^N^N)` FLOOR)) THEN
    ASM_ARITH_TAC);;

let HOMO_TRANS_DERIVATIVE_IMP_MSUMMABLE = prove
    (`!x:num->real^N R n. summable (from n) (\n. x n) /\ msummable (from n) (\n. R n) ==> msummable (from n) (\n. homo_trans_derivative (x n) (R n))`,
    SIMP_TAC[summable;msummable;SERIES_FROM;MSERIES_FROM] THEN
    SIMP_TAC[MATRIX_LIM_COMPONENTWISE_REAL;LIM_COMPONENTWISE_REAL;MSUM_COMPONENT;VSUM_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `homo_trans_derivative (l:real^N) (l':real^N^N)` THEN
    SIMP_TAC[HOMO_TRANS_DERIVATIVE_COMPONENT;LAMBDA_BETA;DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `i <= N + 1 <=> i <= N \/ i = N + 1`] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `i <= N ==> ~(i = N + 1)`;SUM_0;LIMIT_REAL_CONST]);;

let MATRIX_EXP_HOMO_TRAN_DERIVATIVE_EQ = prove
    (`!x:real^N R:real^N^N. matrix_exp (homo_trans_derivative x R) = homo_trans ((infmsum (from 1) (\n. &1 / &(FACT n) %% (R matrix_pow (n - 1)))) ** x) (matrix_exp R)`,
    REPEAT GEN_TAC THEN REWRITE_TAC[matrix_exp] THEN
    MP_TAC (ISPECL [`(\n. &1 / &(FACT n) %% (homo_trans_derivative (x:real^N) R) matrix_pow n)`;`0`] INFMSUM_ADD_LEFT) THEN
    MP_TAC (ISPECL [`(\n. &1 / &(FACT n) %% (R:real^N^N) matrix_pow n)`;`0`] INFMSUM_ADD_LEFT) THEN
    SIMP_TAC[MSUMMABLE_EXP;FACT;REAL_DIV_1;matrix_pow;MATRIX_CMUL_LID;GSYM (num_CONV `1`)] THEN 
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MATRIX_ADD_SYM] THEN
    SIMP_TAC[GSYM HOMO_TRANS_DERIVATIVE_ADD_MAT] THEN
    SIMP_TAC[MATRIX_ARITH `(A:real^(N,1)finite_sum^(N,1)finite_sum) + B = C + B <=> A = C`] THEN
    SIMP_TAC[GSYM INFMSUM_VECTOR_RMUL;MSUMMABLE_EXP1] THEN
    MP_TAC (GSYM (ISPECL [`(\n. &1 / &(FACT n) %% (R:real^N^N) matrix_pow (n - 1) ** (x:real^N))`;`(\n. &1 / &(FACT n) %% (R:real^N^N) matrix_pow n)`;`1`] HOMO_TRANS_DERIVATIVE_INFMSUM)) THEN
    ANTS_TAC THENL
    [SIMP_TAC[] THEN
     MATCH_MP_TAC HOMO_TRANS_DERIVATIVE_IMP_MSUMMABLE THEN
     SIMP_TAC[MSUMMABLE_EXP] THEN
     MP_TAC (ISPECL [`R:real^N^N`;`1`] MSUMMABLE_EXP1) THEN
     REWRITE_TAC[msummable;summable] THEN
     STRIP_TAC THEN EXISTS_TAC `(l:real^N^N) ** (x:real^N)` THEN
     MATCH_MP_TAC MSERIES_VECTOR_RMUL THEN ASM_SIMP_TAC[];ALL_TAC] THEN
    SIMP_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC INFMSUM_EQ THEN SIMP_TAC[MSUMMABLE_EXP] THEN
    CONJ_TAC THENL
    [REWRITE_TAC[msummable] THEN
     ONCE_REWRITE_TAC[GSYM MSERIES_RESTRICT] THEN 
     SIMP_TAC[IN_FROM;MATRIX_VECTOR_LMUL;GSYM HOMO_TRANS_DERIVATIVE_CMUL;GSYM HOMO_TRANS_DERIVATIVE_POW_GE_1] THEN
     SIMP_TAC[GSYM IN_FROM;MSERIES_RESTRICT] THEN 
     SIMP_TAC[GSYM msummable;MSUMMABLE_EXP];ALL_TAC] THEN
    SIMP_TAC[IN_FROM;MATRIX_VECTOR_LMUL;GSYM HOMO_TRANS_DERIVATIVE_CMUL;GSYM HOMO_TRANS_DERIVATIVE_POW_GE_1]);;

(* ------------------------------------------------------------------------- *)
(* e(n) the lie algebra of euclidean group                                   *)
(* ------------------------------------------------------------------------- *)

let lie_algebra_of_eg = new_definition
 `lie_algebra_of_eg (group_mlg(euclidean_group (x:real^N) R)) = lie_algebra ({ homo_trans_derivative (x:real^N) R| transp R = --R /\ x IN (:real^N)},matrix_lie_bracket,matrix_add,(%%):real->real^(N,1)finite_sum^(N,1)finite_sum->real^(N,1)finite_sum^(N,1)finite_sum,(mat 0 :real^(N,1)finite_sum^(N,1)finite_sum))`;; 
 
let LIE_ALGEBRA_OF_EG = prove
    (`(!x R:real^N^N. lie_alg_set (lie_algebra_of_eg (group_mlg(euclidean_group x R))) = { homo_trans_derivative (x:real^N) R| transp R = --R /\ x IN (:real^N)}) /\
    (!x R:real^N^N. lie_bracket (lie_algebra_of_eg (group_mlg (euclidean_group x R))) = matrix_lie_bracket) /\
    (!x R:real^N^N. lie_alg_add (lie_algebra_of_eg (group_mlg (euclidean_group x R))) = matrix_add) /\
    (!x R:real^N^N. lie_alg_mul (lie_algebra_of_eg (group_mlg (euclidean_group x R))) = (%%)) /\
    (!x R:real^N^N. lie_alg_zero (lie_algebra_of_eg (group_mlg (euclidean_group x R))) = mat 0)`,
    REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN 
    MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl lie_algebra_of_eg)))))
   (CONJUNCT2 lie_algebra_tybij)))) THEN
    REWRITE_TAC[GSYM lie_algebra_of_eg] THEN 
    SIMP_TAC[MATRIX_LIE_BRACKET_BILINEAR_ALT;MATRIX_LIE_BRACKET_SSM_ALT;MATRIX_LIE_BRACKET_JACOBI_I;GSYM MATRIX_ADD_ASSOC] THEN
    SIMP_TAC[lie_alg_set; lie_bracket; lie_alg_add; lie_alg_mul;lie_alg_zero]);;

(* ------------------------------------------------------------------------- *)
(* se(n) the lie algebra of special euclidean group                          *)
(* ------------------------------------------------------------------------- *)

let lie_algebra_of_seg = new_definition
 `lie_algebra_of_seg (group_mlg(special_euclidean_group (x:real^N) R)) = lie_algebra ({ homo_trans_derivative (x:real^N) R| transp R = --R /\ x IN (:real^N)},matrix_lie_bracket,matrix_add,(%%):real->real^(N,1)finite_sum^(N,1)finite_sum->real^(N,1)finite_sum^(N,1)finite_sum,(mat 0 :real^(N,1)finite_sum^(N,1)finite_sum))`;; 
 
let LIE_ALGEBRA_OF_SEG = prove
    (`(!x R:real^N^N. lie_alg_set (lie_algebra_of_seg (group_mlg(special_euclidean_group x R))) = { homo_trans_derivative (x:real^N) R| transp R = --R /\ x IN (:real^N)}) /\
    (!x R:real^N^N. lie_bracket (lie_algebra_of_seg (group_mlg (special_euclidean_group x R))) = matrix_lie_bracket) /\
    (!x R:real^N^N. lie_alg_add (lie_algebra_of_seg (group_mlg (special_euclidean_group x R))) = matrix_add) /\
    (!x R:real^N^N. lie_alg_mul (lie_algebra_of_seg (group_mlg (special_euclidean_group x R))) = (%%)) /\
    (!x R:real^N^N. lie_alg_zero (lie_algebra_of_seg (group_mlg (special_euclidean_group x R))) = mat 0)`,
    REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN 
    MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl lie_algebra_of_seg)))))
   (CONJUNCT2 lie_algebra_tybij)))) THEN
    REWRITE_TAC[GSYM lie_algebra_of_seg] THEN 
    SIMP_TAC[MATRIX_LIE_BRACKET_BILINEAR_ALT;MATRIX_LIE_BRACKET_SSM_ALT;MATRIX_LIE_BRACKET_JACOBI_I;GSYM MATRIX_ADD_ASSOC] THEN
    SIMP_TAC[lie_alg_set; lie_bracket; lie_alg_add; lie_alg_mul;lie_alg_zero]);;

(* ------------------------------------------------------------------------- *)
(* related properties of the lie algebra of matrix lie group                 *)
(* ------------------------------------------------------------------------- *)
 
let IS_LIE_ALGEBRA_OF_EG = prove
    (`!x:real^N R:real^N^N. is_lie_algebra_of_mlg (group_mlg(euclidean_group x R)) (lie_algebra_of_eg (group_mlg(euclidean_group x R)))`,
    REWRITE_TAC[is_lie_algebra_of_mlg;LIE_ALGEBRA_OF_EG;MLG_SET_EQ_EG;EUCLIDEAN_GROUP;IN_ELIM_THM;IN_UNIV] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_EQ] THEN
    EXISTS_TAC `((infmsum (from 1) (\n. &1 / &(FACT n) %% t pow n %% (R:real^N^N) matrix_pow (n - 1))) ** (x:real^N))` THEN
    EXISTS_TAC `matrix_exp(t %% R):real^N^N` THEN
    ASM_SIMP_TAC[MATRIX_EXP_INV;GSYM MATRIX_CMUL_RNEG;MATRIX_EXP_TRANSP;TRANSP_MATRIX_CMUL;INVERTIBLE_MATRIX_EXP] THEN
    SIMP_TAC[HOMO_TRANS_DERIVATIVE_CMUL;MATRIX_EXP_HOMO_TRAN_DERIVATIVE_EQ;HOMO_TRANS_UNIQUE] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL;GSYM MATRIX_VECTOR_LMUL] THEN
    MATCH_MP_TAC (MESON [MATRIX_EQ] `(A:real^N^N) = B ==> A ** (x:real^N) = B ** x`) THEN
    SIMP_TAC[GSYM INFMSUM_CMUL;MSUMMABLE_EXP1] THEN
    ONCE_REWRITE_TAC[GSYM INFMSUM_RESTRICT] THEN
    REWRITE_TAC[IN_FROM;MATRIX_POW_CMUL;MATRIX_CMUL_ASSOC;real_div;REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c = b * (a * c)`] THEN
    SIMP_TAC[REAL_FIELD `x * x pow (n - 1) = x pow (1 + n - 1)`;ARITH_RULE `1 <= n ==> 1 + n - 1 = n`]);;

let TRACE_SSM_IMP_0 = prove
    (`!A:real^N^N. transp A = -- A ==> trace A = &0`,
    GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `trace:real^N^N->real`) THEN
    SIMP_TAC[TRACE_TRANSP;TRACE_NEG] THEN ARITH_TAC);;
    
let TRACE_HOMO_TRANS_DERIVATIVE = prove
    (`!x R:real^N^N. trace(homo_trans_derivative x R) = trace R`,
    REPEAT GEN_TAC THEN
    SIMP_TAC[trace;SUM_ADD_SPLIT;DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `1 <= N + 1`;SUM_SING_NUMSEG] THEN
    SIMP_TAC[HOMO_TRANS_DERIVATIVE_COMPONENT;LE_REFL;ARITH_RULE `1 <= N + 1`;REAL_ADD_RID] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[HOMO_TRANS_DERIVATIVE_COMPONENT;DIMINDEX_GE_1;ARITH_RULE `i <= N ==> i <= N + 1`;ARITH_RULE `i <= N ==> ~(i = N + 1)`]);;
    
let TRACE_HOMO_TRANS = prove
    (`!x R:real^N^N. trace(homo_trans x R) = trace R + &1`,
    REPEAT GEN_TAC THEN
    SIMP_TAC[trace;SUM_ADD_SPLIT;DIMINDEX_FINITE_SUM;DIMINDEX_1;ARITH_RULE `1 <= N + 1`;SUM_SING_NUMSEG] THEN
    SIMP_TAC[HOMO_TRANS_COMPONENT;LE_REFL;ARITH_RULE `1 <= N + 1`;REAL_ARITH `x + &1 = y + &1 <=> x = y`] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[HOMO_TRANS_COMPONENT;DIMINDEX_GE_1;ARITH_RULE `i <= N ==> i <= N + 1`;ARITH_RULE `i <= N ==> ~(i = N + 1)`]);;
    
let IS_LIE_ALGEBRA_OF_SEG = prove
    (`!x:real^N R:real^N^N. is_lie_algebra_of_mlg (group_mlg(special_euclidean_group x R)) (lie_algebra_of_seg (group_mlg(special_euclidean_group x R)))`,
    REWRITE_TAC[is_lie_algebra_of_mlg;LIE_ALGEBRA_OF_SEG;MLG_SET_EQ_SEG;SPECIAL_EUCLIDEAN_GROUP;IN_ELIM_THM;IN_UNIV] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_EQ] THEN
    EXISTS_TAC `((infmsum (from 1) (\n. &1 / &(FACT n) %% t pow n %% (R:real^N^N) matrix_pow (n - 1))) ** (x:real^N))` THEN
    EXISTS_TAC `matrix_exp(t %% R):real^N^N` THEN
    ASM_SIMP_TAC[MATRIX_EXP_INV;GSYM MATRIX_CMUL_RNEG;MATRIX_EXP_TRANSP;TRANSP_MATRIX_CMUL;INVERTIBLE_MATRIX_EXP] THEN
    SUBGOAL_THEN `homo_trans
        (infmsum (from 1) (\n. &1 / &(FACT n) %% t pow n %% (R:real^N^N) matrix_pow (n - 1)) **
        (x:real^N)) (matrix_exp (t %% R)) = matrix_exp (t %% homo_trans_derivative x R)` SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN
     SIMP_TAC[HOMO_TRANS_DERIVATIVE_CMUL;MATRIX_EXP_HOMO_TRAN_DERIVATIVE_EQ;HOMO_TRANS_UNIQUE] THEN
     REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL;GSYM MATRIX_VECTOR_LMUL] THEN
     MATCH_MP_TAC (MESON [MATRIX_EQ] `(A:real^N^N) = B ==> A ** (x:real^N) = B ** x`) THEN
     SIMP_TAC[GSYM INFMSUM_CMUL;MSUMMABLE_EXP1] THEN
     ONCE_REWRITE_TAC[GSYM INFMSUM_RESTRICT] THEN
     REWRITE_TAC[IN_FROM;MATRIX_POW_CMUL;MATRIX_CMUL_ASSOC;real_div;REAL_MUL_LID] THEN
     ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c = b * (a * c)`] THEN
     SIMP_TAC[REAL_FIELD `x * x pow (n - 1) = x pow (1 + n - 1)`;ARITH_RULE `1 <= n ==> 1 + n - 1 = n`];ALL_TAC] THEN
     ASM_SIMP_TAC[SSM_IMP_DET_EXP_1;MATRIX_EXP_HOMO_TRAN_DERIVATIVE_EQ;DET_HOMO_TRANS_EQ;HOMO_TRANS_DERIVATIVE_CMUL]);;

     
(* examples (2) OR (3) *)
(*        
let homo_trans_m2 = new_definition
    `(homo_trans_m2:real^2->real^2^2->real^3^3) x R = 
     vector [vector[R$1$1; R$1$2; x$1];
             vector[R$2$1; R$2$2; x$2];
             vector[&0; &0; &1]]:real^3^3`;;
                           
let homo_trans_m3 = new_definition
    `(homo_trans_m3:real^3->real^3^3->real^4^4) x R = 
     vector [vector[R$1$1; R$1$2; R$1$3; x$1];
            vector[R$2$1; R$2$2; R$2$3; x$2];
            vector[R$3$1; R$3$2; R$3$3; x$3];
            vector[&0; &0; &0; &1]]:real^4^4`;;
*)            
(*    
(*unitary group*)

let unitary_group = new_definition
 `unitary_group (a:real^N^N) = group ({A:real^N^N | invertible A /\ matrix(adjoint (\x. A ** x)) = matrix_inv A}, mat 1:real^N^N, matrix_inv, matrix_mul)`;;

let UNITARY_GROUP = prove
 (`(!a:real^N^N. group_carrier(unitary_group a) = {A:real^N^N | invertible A /\ matrix(adjoint (\x. A ** x)) = matrix_inv A}) /\
   (!a:real^N^N. group_id(unitary_group a) = mat 1:real^N^N) /\
   (!a:real^N^N. group_inv(unitary_group a) =matrix_inv) /\
   (!a:real^N^N. group_mul(unitary_group a) = matrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl unitary_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM unitary_group] THEN SIMP_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_LINEAR;MATRIX_ADJOINT;MATRIX_OF_MATRIX_VECTOR_MUL] THEN
    SIMP_TAC[INVERTIBLE_I;MATRIX_INV_I;TRANSP_MAT;
             INVERTIBLE_MATRIX_INV;TRANSP_MATRIX_INV;MATRIX_INV_EQ;
             MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RID;MATRIX_INV;
             MATRIX_TRANSP_MUL;MATRIX_INV_MUL;INVERTIBLE_MATRIX_MUL] THEN
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);; 

(*special unitary group*)

let special_unitary_group = new_definition
 `special_unitary_group (a:real^N^N) = group ({A:real^N^N | invertible A /\ matrix(adjoint (\x. A ** x)) = matrix_inv A /\ det(A) = &1}, mat 1:real^N^N, matrix_inv, matrix_mul)`;;

let SPECIAL_UNITARY_GROUP = prove
 (`(!a:real^N^N. group_carrier(special_unitary_group a) = {A:real^N^N | invertible A /\ matrix(adjoint (\x. A ** x)) = matrix_inv A /\ det(A) = &1}) /\
   (!a:real^N^N. group_id(special_unitary_group a) = mat 1:real^N^N) /\
   (!a:real^N^N. group_inv(special_unitary_group a) =matrix_inv) /\
   (!a:real^N^N. group_mul(special_unitary_group a) = matrix_mul)`,
    REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
    (ISPEC(rand(rand(snd(strip_forall(concl special_unitary_group)))))
    (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM special_unitary_group] THEN SIMP_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_LINEAR;MATRIX_ADJOINT;MATRIX_OF_MATRIX_VECTOR_MUL] THEN
    SIMP_TAC[INVERTIBLE_I;MATRIX_INV_I;TRANSP_MAT;DET_I;
             INVERTIBLE_MATRIX_INV;DET_MATRIX_INV;REAL_INV_1;
             TRANSP_MATRIX_INV;MATRIX_INV_EQ;
             MATRIX_MUL_ASSOC;MATRIX_MUL_LID;MATRIX_MUL_RID;MATRIX_INV;
             MATRIX_TRANSP_MUL;MATRIX_INV_MUL;DET_MUL;REAL_MUL_LID;
             INVERTIBLE_MATRIX_MUL] THEN
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]);; 
*)

