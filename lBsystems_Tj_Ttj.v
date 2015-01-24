(** * Operations T_j and Tt_j defined by operations T and Tt. 

by Vladimir Voevodsky, started on Jan. 22, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_T_Tt.


(** Definition of operations T_j that are iterated operations T *)

Lemma T_j_int { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
      ( j : nat ) { A X1 X2 : BB } ( e : ll X1 = ll A + j ) 
      ( e' : A = ftn j X1 ) ( isov : isover X1 A ) ( isab : isabove X2 A ) : BB .
Proof .
  intros BB T ax1b j . induction j as [ | j IHj ] .
  intros . exact A .

  intros .
  assert ( inn : T_dom ( ftn j X1 ) X2 ) .
  refine ( T_dom_constr _ _ ) . 
  rewrite ll_ftn . 
  rewrite e .
  rewrite natassocpmeq . 
  change ( S j - j ) with ( ( 1 + j ) - j ) .  rewrite ( plusminusnmm 1 j ) .
  rewrite natpluscomm . exact ( natgthsn0 _ ) . 

  exact ( natgehsnn _ ) .
  
  change (ft (ftn j X1)) with ( ftn ( S j ) X1 ) . 
  rewrite <- e' .
  exact isab . 

  refine ( IHj ( ftn j X1 ) X1 ( T ( ftn j X1 ) X2 inn ) _ _ _ _ ) .
  rewrite ll_ftn . 
  assert (gte : ll X1 >= j ) . 
  rewrite e .  exact ( istransnatgeh _ _ _ ( natgehplusnmm _ _ ) ( natgehsnn _ ) ) . 

  exact ( ! ( minusplusnmm _ _ gte ) ) . 

  exact ( idpath _ ) .

  exact ( isover_X_ftnX _ _ ) .
 
  exact ( ax1b _ _ _ ) .

Defined.


Definition T_j { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
      { A X1 X2 : BB } ( isov : isover X1 A ) ( isab : isabove X2 A ) : BB .
Proof .
  intros .
  set ( j := ll X1 - ll A ) .
  refine ( T_j_int ax1b j _ _ isov isab ) .
  unfold j . 
  rewrite natpluscomm . 
  refine ( ! ( minusplusnmm _ _ _ ) ) . 
  exact ( isover_geh isov ) . 

  unfold isover in isov .
  exact isov . 

Defined.









  
(* End of the file lBsystems_Tj_Ttj.v *)