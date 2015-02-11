(** ** The functions of the over-towers defined by T and their iterations. 

by Vladimir Voevodsky, started on Jan. 22, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_T_Tt .


(** *** The definition of an extended operation T and its elementary properties. *)

Definition T_ext_dom { BB : lBsystem_carrier } ( X1 X2 : BB ) :=
  dirprod ( ll X1 > 0 ) ( isover X2 ( ft X1 ) ) .

Definition T_ext_dom_gt0 { BB : lBsystem_carrier } { X1 X2 : BB } ( inn : T_ext_dom X1 X2 ) :=
  pr1 inn .

Definition T_ext_dom_isov { BB : lBsystem_carrier } { X1 X2 : BB } ( inn : T_ext_dom X1 X2 ) :=
  pr2 inn .

Definition T_ext { BB : lBsystem_carrier } ( T : T_ops_type BB )
           { X1 X2 : BB } ( inn : T_ext_dom X1 X2 ) : BB .
Proof .
  intros. set ( gt0 := pr1 inn ) . set ( isov := pr2 inn ) . 
  destruct ( ovab_choice isov ) as [ isab | eq ] . 
  exact ( T _ _ ( dirprodpair gt0 isab ) ) . 

  exact X1 .

Defined.

Lemma isover_T_ext { BB : lBsystem_carrier }
      ( T : T_ops_type BB ) ( ax1b : T_ax1b_type T )
      { X1 X2 : BB } ( inn : T_ext_dom X1 X2 ) :
  isover ( T_ext T inn ) X1 .
Proof .
  intros .
  unfold T_ext . 
  destruct ( ovab_choice (pr2 inn) ) as [ isab | eq ] .
  exact ( ax1b _ _ _ ) . 

  exact ( isover_XX _ ) . 

Defined.


  

Lemma isover_T_ext_T_ext_2 { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 :  T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T )
      { X1 X2 X2' : BB } ( inn : T_ext_dom X1 X2 ) ( inn' : T_ext_dom X1 X2' )
      ( is : isover X2 X2' ) : isover ( T_ext T inn ) ( T_ext T inn' ) .
Proof .
  intros . unfold T_ext .
  destruct ( ovab_choice (pr2 inn) ) as [ isab | eq ] .
  destruct ( ovab_choice (pr2 inn') ) as [ isab' | eq' ] .
  apply ( isover_T_T_2 ax0 ax1a _ _ is ) . 

  exact ( ax1b _ _ _ ) . 

  destruct ( ovab_choice (pr2 inn') ) as [ isab' | eq' ] .
  assert ( absd : empty ) .
  rewrite eq in is . 
  assert ( ge := isover_geh is ) .  
  assert ( gt := isabove_gth isab' ) . 
  exact ( ge gt ) . 

  destruct absd . 

  exact ( isover_XX _ ) . 

Defined.



(** *** The function T_fun of the over-towers defined by the extended operation T *)



Definition T_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
      { X1 : BB } ( gt0 : ll X1 > 0 ) ( X2' : ltower_over ( ft X1 ) ) : ltower_over X1 .
Proof .
  intros .
  set ( X2 := pr1 X2' ) . set ( isov := pr2 X2' : isover X2 ( ft X1 ) ) .
  split with ( T_ext T ( dirprodpair gt0 isov ) )  .

  apply ( isover_T_ext T ax1b ) .

Defined.


Lemma isovmonot_T_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T )
      { X1 : BB } ( gt0 : ll X1 > 0 )
      ( X3' X2' : ltower_over ( ft X1 ) ) ( isov : isover X3' X2' ) :
  isover ( T_fun ax1b gt0 X3' ) ( T_fun ax1b gt0 X2' ) .
Proof .
  intros .
  apply isinvovmonot_pocto .
  unfold T_fun . simpl .
  apply ( isover_T_ext_T_ext_2 ax0 ax1a ax1b ) .
  apply isovmonot_pocto . 
  exact isov . 

Defined.

Lemma ll_T_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      { X1 : BB } ( gt0 : ll X1 > 0 ) ( X2' : ltower_over ( ft X1 ) ) :
  ll ( T_fun ax1b gt0 X2' ) = ll X2' .
Proof.
  intros. 
  change _ with ( ll ( T_ext T ( dirprodpair gt0 ( pr2 X2' ) ) ) - ll X1 = ll X2' ) .
  change ( ll X2' ) with ( ll ( pr1 X2' ) - ll ( ft X1 ) ) . 
  unfold T_ext . 
  destruct (ovab_choice (pr2 (dirprodpair gt0 (pr2 X2')))) as [ isab | eq ] . 
  rewrite ax0 . 
  rewrite ll_ft .
  assert ( ge : ll (pr1 X2') >= ll X1 ) .
  apply natgthminus1togeh . 
  rewrite <- ll_ft . 
  apply ( isabove_gth isab ) . 
  
  rewrite <- natassocmpeq . 
  rewrite ( natpluscomm _ 1 ) . 
  apply natassocpmeq . 
  apply ge .

  apply ge .

  apply ( @natgthminus1togeh 1 _ gt0 ) .
  rewrite natminusnn . 
  rewrite eq . 
  rewrite natminusnn . 
  apply idpath .

Defined.

  
Lemma isllmonot_T_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      { X1 : BB } ( gt0 : ll X1 > 0 ) : isllmonot ( T_fun ax1b gt0 ) .
Proof.
  intros. unfold isllmonot . 
  intros X Y .
  repeat rewrite ( ll_T_fun ax0 ) . 
  apply idpath . 

Defined.

Lemma isbased_T_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      { X1 : BB } ( gt0 : ll X1 > 0 ) : isbased ( T_fun ax1b gt0 ) .
Proof.
  intros. unfold isbased.  intros X eq0 . 
  rewrite ll_T_fun . 
  exact eq0.

  exact ax0.

Defined.


Definition ltower_T_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T )
      { X1 : BB } ( gt0 : ll X1 > 0 ) :
  ltower_fun ( ltower_over ( ft X1 ) ) ( ltower_over X1 ) :=
  ltower_fun_constr ( isovmonot_T_fun ax0 ax1a ax1b gt0 )
                    ( isllmonot_T_fun ax0 ax1b gt0 )
                    ( isbased_T_fun ax0 ax1b gt0 ) .   


  


(** *** Definition of Tj_fun as iterations of the functions T_fun *)

(** **** Construction of Tj *)

Lemma Tj_fun_int_l0 { BB : lBsystem_carrier }
      { A X1 : BB } ( isov : isover X1 A )
      ( ell : ll X1 - ll A = 0 ) : X1 = A .
Proof .
  intros .
  destruct ( ovab_choice isov ) as [ isab | eq ] .
  assert ( absd : empty ) . 
  assert ( gt := isabove_gth isab ) .
  assert ( gt0 := minusgth0 _ _ gt ) . 
  rewrite ell in gt0 . 
  exact ( negnatgthnn _ gt0 ) . 

  destruct absd .

  exact eq .

Defined.


Lemma Tj_fun_int_l1 { BB : lBsystem_carrier }
      ( j : nat )
      { A X1 : BB } ( isov : isover X1 A )
      ( ell : ll X1 - ll A = S j ) :
  isover ( ft X1 ) A .
Proof .
  intros .
  assert ( gth : ll X1 > ll A ) .  
  apply minusgth0inv .
  rewrite ell . 
  exact ( natgthsn0 _ ) . 

  exact ( isover_ft' ( isabove_constr gth isov ) ) . 

Defined.

Opaque  Tj_fun_int_l1 .

Lemma Tj_fun_int_l2 { BB : lBsystem_carrier }
      ( j : nat )
      { A X1 : BB } ( isov : isover X1 A )
      ( ell : ll X1 - ll A = S j ) :
  ll ( ft X1 ) - ll A = j .
Proof .
  intros .
  rewrite ll_ft . 
  rewrite natminuscomm . 
  rewrite ell . 
  simpl . 
  exact ( natminuseqn _ ) .

Defined.

Opaque Tj_fun_int_l2 .

Lemma Tj_fun_int_l3 { BB : lBsystem_carrier }
      ( j : nat )
      { A X1 : BB } 
      ( ell : ll X1 - ll A = S j ) : ll X1 > 0 . 
Proof .

  intros .
  refine ( natgehgthtrans _ ( ll X1 - ll A ) _ ( natminuslehn _ _ ) _ ) .  
  rewrite ell . 
  exact ( natgthsn0 _ ) .

Defined.

Opaque Tj_fun_int_l3 . 

      
Definition Tj_fun_int { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
           { A : BB }
           ( j : nat )
           { X1 : BB } ( isov : isover X1 A )
           ( ell : ll X1 - ll A = j )
           ( X2' : ltower_over A ) : ltower_over X1 .
Proof .
  intros BB T ax1b A j . induction j as [ | j IHj ] .
  intros .
  assert ( eq := Tj_fun_int_l0 isov ell ) .
  split with ( pr1 X2' ) .
  rewrite eq .
  exact ( pr2 X2' ) . 

  intros . 
  assert ( Tprev := IHj ( ft X1 ) ( Tj_fun_int_l1 j isov ell ) (  Tj_fun_int_l2 j isov ell ) X2' ) .
  exact ( T_fun ax1b ( Tj_fun_int_l3 j ell ) Tprev ) . 

Defined.


Definition Tj_fun { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
           { A X1 : BB } ( isov : isover X1 A ) : ltower_over A -> ltower_over X1 :=
  fun X2' => Tj_fun_int ax1b ( ll X1 - ll A ) isov ( idpath _ ) X2' .



(** **** Proof of monotonicity of Tj relative to the predicate isover *)         

Lemma isovmonot_Tj_fun_int { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T )
      { A : BB }
      ( j : nat )
      { X1 : BB } ( isov : isover X1 A )
      ( ell : ll X1 - ll A = j )
      ( X2' X3' : ltower_over A ) ( isov' : isover X3' X2' ) :
  isover ( Tj_fun_int ax1b j isov ell X3' ) ( Tj_fun_int ax1b j isov ell X2' ) .
Proof .
  intros BB T ax0 ax1a ax1b A . induction j as [ | j IHj ] . 
  intros .
  assert ( eq := Tj_fun_int_l0 isov ell ) .
  unfold Tj_fun_int . 
  simpl . 
  apply isinvovmonot_pocto . 
  simpl .
  apply isovmonot_pocto . 
  exact isov' . 

  intros . 
  simpl . 
  unfold T_fun .
  apply isinvovmonot_pocto .
  simpl . 
  apply ( isover_T_ext_T_ext_2 ax0 ax1a ax1b ) . 
  apply isovmonot_pocto . 
  apply IHj . 
  exact isov' . 

Defined.

  
  


Lemma isovmonot_Tj_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T )
      { X1 A : BB } ( isov : isover X1 A )
      ( X2' X3' : ltower_over A ) ( isov' : isover X2' X3' ) :
  isover ( Tj_fun ax1b isov X2' ) ( Tj_fun ax1b isov X3' ) .
Proof .
  intros .
  apply ( isovmonot_Tj_fun_int ax0 ax1a ax1b ) . 
  exact isov' .

Defined.



(** **** Functions Tj and the length function ll *)

Lemma ll_Tj_fun_int { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      { A : BB }
      ( j : nat )
      { X1 : BB } ( isov : isover X1 A )
      ( ell : ll X1 - ll A = j )
      ( X2' : ltower_over A ) :
  ll ( Tj_fun_int ax1b j isov ell X2' ) = ll X2' .
Proof .
  intros BB T ax0 ax1b A j .
  induction j as [ | j IHj ] . intros . 
  simpl .
  change _ with ( ll ( pr1 X2' ) - ll X1 = ll ( pr1 X2' ) - ll A ) . 
  assert ( eq : ll X1 = ll A ) . apply natminusmequalsn .
  apply ( isover_geh isov ) . 

  apply ell .

  rewrite eq . apply idpath .

  simpl .

  intros .  rewrite ll_T_fun . 
  apply IHj .

  apply ax0 .

Defined.


Lemma ll_Tj_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      { A X1 : BB } ( isov : isover X1 A )
      ( X2' : ltower_over A ) :
  ll ( Tj_fun ax1b isov X2' ) = ll X2' .
Proof.
  intros.
  apply ll_Tj_fun_int .

  apply ax0 . 

Defined.


Lemma isllmonot_Tj_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      { A X1 : BB } ( isov : isover X1 A ) : isllmonot ( Tj_fun ax1b isov ) . 
Proof.
  intros .
  unfold isllmonot . 
  intros X Y .
  repeat rewrite ll_Tj_fun . 
  apply idpath .

  apply ax0.

  apply ax0.

Defined.



Lemma isbased_Tj_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      { A X1 : BB } ( isov : isover X1 A ) : isbased ( Tj_fun ax1b isov ) .
Proof.
  intros. unfold isbased. intros X eq0 .
  rewrite ll_Tj_fun . 
  exact eq0.

  exact ax0.

Defined.


Definition ltower_Tj_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T )
      { A X1 : BB } ( isov : isover X1 A ) :
  ltower_fun ( ltower_over A ) ( ltower_over X1 ) :=
  ltower_fun_constr ( isovmonot_Tj_fun ax0 ax1a ax1b isov )
                    ( isllmonot_Tj_fun ax0 ax1b isov )
                    ( isbased_Tj_fun ax0 ax1b isov ) . 




(** *** Function Tt_fun *)

(* Definition Tt_fun { BB : lBsystem_carrier }
           ( T : T_ops_type BB ) ( Tt : Tt_ops_type BB )
           ( X : BB ) : *)
      
  






(** *** Function Tprod for pointed l-Bsystems *)


Definition Tprod_fun { BB : lBsystem_carrier } 
           { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
           ( X1 : BB ) ( X2 : BB ) : ltower_over X1 .
Proof .
  intros .
  set ( X2' := @to_ltower_over BB X2 ) .
  exact ( Tj_fun ax1b ( isoverll0 ( ll_cntr BB ) X1 ) X2' ) .  

Defined.


Lemma isovmonot_Tprod_fun { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T )  ( ax1b : T_ax1b_type T )
           ( X1 : BB ) : isovmonot ( Tprod_fun ax1b X1 ) . 
Proof .
  intros .
  unfold isovmonot . 
  intros X Y isov .
  set ( X' := @to_ltower_over BB X ) . set ( Y' := @to_ltower_over BB Y ) .
  set ( isov' := isovmonot_to_ltower_over isov ) . 
  exact ( isovmonot_Tj_fun ax0 ax1a ax1b ( isoverll0 ( ll_cntr BB ) X1 ) X' Y' isov' ) .  

Defined.


Definition Tprod_ovmonotfun { BB : lBsystem_carrier } 
           { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T )  ( ax1b : T_ax1b_type T )
           ( X1 : BB ) : ovmonot_fun BB ( ltower_over X1 ) :=
  ovmonot_fun_constr ( Tprod_fun ax1b X1 ) ( isovmonot_Tprod_fun ax0 ax1a ax1b X1 ) . 




Lemma ll_Tprod_fun { BB : lBsystem_carrier } 
           { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
           ( X1 : BB ) ( X2 : BB ) : ll ( Tprod_fun ax1b X1 X2 ) = ll X2 .
Proof .
  intros .
  unfold Tprod_fun . 
  rewrite ll_Tj_fun .
  rewrite (@ll_to_ltower_over BB).
  apply idpath . 

  apply ax0 . 

Defined.

Lemma isllmonot_Tprod_fun { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
           ( X1 : BB ) : isllmonot ( Tprod_fun ax1b X1 ) .
Proof .
  intros . unfold isllmonot .  intros X Y . 
  repeat rewrite ll_Tprod_fun . apply idpath . 

  apply ax0 .

  apply ax0 .

Defined.

  

Lemma isbased_Tprod_fun { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
           ( X1 : BB ) : isbased ( Tprod_fun ax1b X1 ) .
Proof.
  intros. unfold isbased . intros X eq0 .
  rewrite ll_Tprod_fun . 

  exact eq0.

  exact ax0.

Defined.


Definition ltower_Tprod_fun { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T )
           ( X1 : BB ) :
  ltower_fun BB ( ltower_over X1 ) :=
  ltower_fun_constr ( isovmonot_Tprod_fun ax0 ax1a ax1b X1 )
                    ( isllmonot_Tprod_fun ax0 ax1b X1 )
                    ( isbased_Tprod_fun ax0 ax1b X1 ) .













(*  
  

Definition isabove_Tj { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      { A X1 X2 : BB } ( isov : isover X1 A ) ( isab : isabove X2 A ) :
  isabove ( Tj ax0 ax1b isov isab ) X1 :=
  pr1 ( pr2 ( Tj_int_package ax0 ax1b ( ll X1 - ll A ) isov ( idpath _ ) isab ) ) . 

Opaque isabove_Tj .

Definition ll_Tj { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      { A X1 X2 : BB } ( isov : isover X1 A ) ( isab : isabove X2 A ) :
  ll ( Tj ax0 ax1b isov isab ) = ll X2 - ll A + ll X1 :=
  pr2 ( pr2 ( Tj_int_package ax0 ax1b ( ll X1 - ll A ) isov ( idpath _ ) isab ) ) . 






*)



  
(* End of the file lBsystems_T_fun_Tj_Ttj.v *)