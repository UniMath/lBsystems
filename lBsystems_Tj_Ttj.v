(** * Operations T_j and Tt_j defined by operations T and Tt. 

by Vladimir Voevodsky, started on Jan. 22, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_T_Tt.


(** Definition of operations T_j that are iterated operations T *)

Lemma T_j_int { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
      ( j : nat ) { A X1 X2 : BB } ( ell : ll X1 = ll A + j ) 
      ( e : A = ftn j X1 ) ( isov : isover X1 A ) ( isab : isabove X2 A ) : BB .
Proof .
  intros BB T ax1b j . induction j as [ | j IHj ] .
  intros . exact X2 .

  intros .
  assert ( inn : T_dom ( ftn j X1 ) X2 ) .
  refine ( T_dom_constr _ _ ) . 
  rewrite ll_ftn . 
  rewrite ell .
  rewrite natassocpmeq . 
  change ( S j - j ) with ( ( 1 + j ) - j ) .  rewrite ( plusminusnmm 1 j ) .
  rewrite natpluscomm . exact ( natgthsn0 _ ) . 

  exact ( natgehsnn _ ) .
  
  change (ft (ftn j X1)) with ( ftn ( S j ) X1 ) . 
  rewrite <- e .
  exact isab . 

  refine ( IHj ( ftn j X1 ) X1 ( T ( ftn j X1 ) X2 inn ) _ _ _ _ ) .
  rewrite ll_ftn . 
  assert (gte : ll X1 >= j ) . 
  rewrite ell .  exact ( istransnatgeh _ _ _ ( natgehplusnmm _ _ ) ( natgehsnn _ ) ) . 

  exact ( ! ( minusplusnmm _ _ gte ) ) . 

  exact ( idpath _ ) .

  exact ( isover_X_ftnX _ _ ) .
 
  exact ( ax1b _ _ _ ) .

Defined.


Lemma T_j_int_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
      { A X1 X2 : BB }
      ( j j' : nat ) 
      ( ell : ll X1 = ll A + j ) ( ell' : ll X1 = ll A + j' )
      ( e : A = ftn j X1 ) ( e' : A = ftn j' X1 ) 
      ( isov isov' : isover X1 A ) ( isab isab' : isabove X2 A ) :
  T_j_int ax1b j ell e isov isab = T_j_int ax1b j' ell' e' isov' isab' .
Proof .
  intros BB T ax1b A X1 X2 j j' ell ell' .
  assert ( eqj : j = j' ) . apply ( natpluslcan _ _ ( ll A ) ) .
  exact ( ( ! ell ) @ ell' ) .

  generalize ell. 
  clear ell . 
  generalize ell'.
  clear ell'.
  rewrite eqj . 
  clear eqj . 

  intros ell ell' .
  assert ( eqell : ell = ell' ) . apply isasetnat . 
  rewrite eqell . 
  clear ell eqell .

  intros e e'.
  assert ( eqe : e = e' ) . apply isasetB . 
  rewrite eqe . 
  clear e eqe .

  intros isov isov' . assert ( eqov : isov = isov' ) . apply isaprop_isover . rewrite eqov . 

  intros isab isab' . assert ( eqab : isab = isab' ) . apply isaprop_isabove . rewrite eqab .

  apply idpath . 

Defined.

  


  

Lemma isabove_T_j_int { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
      ( j : nat ) { A X1 X2 : BB } ( e : ll X1 = ll A + j ) 
      ( e' : A = ftn j X1 ) ( isov : isover X1 A ) ( isab : isabove X2 A ) :
  isabove ( T_j_int ax1b j e e' isov isab ) X1 .
Proof.
  intros BB T ax1b j . induction j as [ | j IHj ] .
  intros . 
  simpl .
  assert ( eq : X1 = A ) . 
  unfold isover in isov . 
  rewrite natplusr0 in e . 
  rewrite e in isov . 
  rewrite natminusnn in isov . 
  exact ( ! isov ) . 

  rewrite eq .
  exact isab .

  intros . 
  simpl . 
  






  
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

Lemma isabove_T_j { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
      { A X1 X2 : BB } ( isov : isover X1 A ) ( isab : isabove X2 A ) :
  isabove ( T_j ax1b isov isab ) X1 .
Proof .
  intros .
  unfold T_j . 
  








  
(* End of the file lBsystems_Tj_Ttj.v *)