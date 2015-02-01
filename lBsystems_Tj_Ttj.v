(** * Operations Tj and Ttj defined by operations T and Tt. 

by Vladimir Voevodsky, started on Jan. 22, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_T_Tt . 


(** Definition of operations Tj that are iterated operations T *)

Lemma Tj_int_Sj_l1 { BB : lBsystem_carrier }
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

Lemma Tj_int_Sj_l2 { BB : lBsystem_carrier }
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


Lemma Tj_int_package { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      ( j : nat )
      { A X1 : BB } ( isov : isover X1 A )
      ( ell : ll X1 - ll A = j )
      { X2 : BB } ( isab : isabove X2 A ) :
  total2 ( fun Tj : BB =>
             dirprod ( isabove Tj X1 ) ( ll Tj = ll X2 - ll A + ll X1 ) ) .
Proof .
  intros BB T ax0 ax1b j A .
  induction j as [ | j IHj ] .
  intros . split with X2 . 

  split . 
  rewrite isov in isab .
  rewrite ell in isab .
  exact isab .

  assert ( eq : ll X1 = ll A ) .  refine ( natminusmequalsn ( isover_geh isov ) ell ) . 

  rewrite eq .
  refine ( ! ( minusplusnmm _ _ _ ) ) . 
  exact ( isover_geh isab ) . 
  
  intros .
  refine ( tpair _ _ _ ) .
  set ( int1 := Tj_int_Sj_l1 j isov ell ) .
  set ( int2 :=  Tj_int_Sj_l2 j isov ell ) .
  
  refine ( T X1 ( pr1 ( IHj ( ft X1 ) int1 int2 X2 isab ) ) _ ) .
  refine ( T_dom_constr _ _ ) .
  assert ( int : ll X1 >= ll X1 - ll A ) . apply natminuslehn .
  rewrite ell in int . 
  exact ( natgehgthtrans _ _ _ int ( natgthsn0 _ ) ) .

  assert ( int := pr2 ( ( IHj ( ft X1 ) int1 int2 X2 isab ) ) ) . 
  simpl in int . 
  exact ( pr1 int ) . 

  split .
  apply ax1b .

  rewrite ax0 .
  
  rewrite ( pr2 ( pr2 ( IHj ( ft X1 ) _ _ X2 _ ) ) ) . 
  rewrite ll_ft .

  set ( int := ll X2 - ll A ) .
  assert ( gt0 : ll X1 > 0 ) .
  refine ( natgehgthtrans _ ( ll X1 - ll A ) _ ( natminuslehn _ _ ) _ ) .  
  rewrite ell . 
  exact ( natgthsn0 _ ) .

  
  induction ( ll X1 ) as [ | n IHn ] .
  assert ( absd := negnatlthn0 _ gt0 ) . 
  destruct absd . 

  simpl . 
  rewrite natminuseqn . 
  exact ( ! ( natplusnsm int n ) ) .
  
Defined.


Definition Tj_int { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      ( j : nat )
      { A X1 : BB } ( isov : isover X1 A )
      ( ell : ll X1 - ll A = j )
      { X2 : BB } ( isab : isabove X2 A ) : BB :=
  pr1 ( Tj_int_package ax0 ax1b j isov ell isab ) .


(** The inductive property of Tj *)

  
Lemma Tj_int_Sj_l3 { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      ( j : nat )
      { A X1 : BB } ( isov : isover X1 A )
      ( ell : ll X1 - ll A = S j )
      { X2 : BB } ( isab : isabove X2 A ) :
  T_dom X1 ( Tj_int ax0 ax1b j ( Tj_int_Sj_l1 j isov ell ) ( Tj_int_Sj_l2 j isov ell ) isab) . 
Proof .
  intros .
  refine ( T_dom_constr _ _ ) .
  assert ( int : ll X1 >= ll X1 - ll A ) . apply natminuslehn .
  rewrite ell in int . 
  exact ( natgehgthtrans _ _ _ int ( natgthsn0 _ ) ) .

  assert ( int := pr2 ( (Tj_int_package ax0 ax1b j (Tj_int_Sj_l1 j isov ell) (Tj_int_Sj_l2 j isov ell)
        isab) ) ) . 
  simpl in int . 
  exact ( pr1 int ) . 

Defined.
  

Lemma Tj_int_Sj { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      ( j : nat )
      { A X1 : BB } ( isov : isover X1 A )
      ( ell : ll X1 - ll A = S j )
      { X2 : BB } ( isab : isabove X2 A ) :
  Tj_int ax0 ax1b ( S j ) isov ell isab =
  T X1 ( Tj_int ax0 ax1b j
                ( Tj_int_Sj_l1 j isov ell ) ( Tj_int_Sj_l2 j isov ell ) isab )
    ( Tj_int_Sj_l3 ax0 ax1b j isov ell isab ) . 
Proof . 
   intros . 
   apply idpath . 

Defined.


Lemma Tj_int_equals_Tj_int { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      { A X1 X2 : BB }
      { j j' : nat } 
      ( ell : ll X1 - ll A = j ) ( ell' : ll X1 - ll A = j' )
      ( isov isov' : isover X1 A ) ( isab isab' : isabove X2 A ) :
  Tj_int ax0 ax1b j isov ell isab = Tj_int ax0 ax1b j' isov' ell' isab' .
Proof .
  intros BB T ax0 ax1b A X1 X2 j j' ell ell' .
  assert ( eqj : j = j' ) . 
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

  intros isov isov' . assert ( eqov : isov = isov' ) . apply isaprop_isover . rewrite eqov . 

  intros isab isab' . assert ( eqab : isab = isab' ) . apply isaprop_isabove . rewrite eqab .

  apply idpath . 

Defined. 

Opaque Tj_int_equals_Tj_int . 



Definition Tj { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      { X1 A X2 : BB } ( isov : isover X1 A ) ( isab : isabove X2 A ) : BB :=
  Tj_int ax0 ax1b ( ll X1 - ll A ) isov ( idpath _ ) isab . 

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


Lemma T_dom_1_Tj { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      { A X1 X2 : BB } ( isab1 : isabove X1 A ) ( isab2 : isabove X2 A ) :
  T_dom X1 ( Tj ax0 ax1b ( isover_ft' isab1 ) isab2 ) . 
Proof .
  intros .
  refine ( T_dom_constr _ _ ) .
  exact ( isabove_gt0 isab1 ) . 

  exact ( isabove_Tj ax0 ax1b ( isover_ft' isab1 ) isab2 ) . 

Defined.

Opaque T_dom_1_Tj . 


  
Lemma T_1_Tj_int { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      ( j : nat ) 
      { A X1 X2 : BB } ( isab1 : isabove X1 A )
      ( ell : ll X1 - ll A = j )
      ( isab2 : isabove X2 A ) :
  Tj_int ax0 ax1b j isab1 ell isab2 =
  T X1 ( Tj ax0 ax1b ( isover_ft' isab1 ) isab2 ) ( T_dom_1_Tj ax0 ax1b isab1 isab2 ) .   
Proof .
  intros .
  unfold Tj .
  induction j as [ | j IHj ] . 
  assert ( absd : empty ) . 
  assert ( gth := isabove_gth isab1 ) .  
  assert ( gt0 := minusgth0 _ _ gth ) . 
  rewrite ell in gt0 . exact ( isirreflnatgth _ gt0 ) . 
  destruct absd . 

  unfold Tj_int .  unfold Tj_int_package . 
  refine ( T_equals_T T _ _ _ ) . 
  refine ( Tj_int_equals_Tj_int _ _ _ _ _ _ _ _ ) . 

Defined.



(** The predicate isover of expressions of the form Tj *)

Lemma isover_Tj_Tj_int { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T ) ( ax1a : T_ax1a_type T )
      ( j : nat )
      { X1 A : BB } ( isov : isover X1 A )
      ( ell : ll X1 - ll A = j )
      { X2 : BB } ( isab : isabove X2 A )
      { X2' : BB } ( isab' : isabove X2' A )
      ( isov' : isover X2' X2 ) :
  isover ( Tj_int ax0 ax1b j isov ell isab' ) ( Tj_int ax0 ax1b j isov ell isab ) .
Proof .
  intros BB T ax0 ax1b ax1a j .
  induction j as [ | j IHj ] .
  intros . exact isov' .  

  intros .
  rewrite Tj_int_Sj .  rewrite Tj_int_Sj .
  apply ( isover_T_T_2 ax0 ax1a ) .
  apply IHj .
  exact isov' . 

Defined.



  

(** The monotone functions of the over-towers defined by the opration Tj *)

Definition Tj_fun { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T ) ( ax1a : T_ax1a_type T )
      { X1 A : BB } ( isov : isover X1 A ) :
  monotone_fun ( ltower_over A ) ( ltower_over X1 ) .
Proof .
  intros .
  refine ( monotone_fun_constr _ _ ) .
  intro X2ov . 
  set ( X2 := pr1 X2ov ) . set ( isov' := pr2 X2ov ) . 
  destruct ( ovab_choice isov' ) as [ isab | eq ] .
  split with ( Tj ax0 ax1b isov isab ) .

  apply ( isabove_to_isover ( isabove_Tj _ _ isov isab ) ) . 

  exact ( obj_over_constr ( isover_XX X1 ) ) .

  intros X Y isovXY .
  simpl .
  apply to_isover_over . 
  destruct (ovab_choice (pr2 X)) as [ isabX | eqX ] .
  destruct (ovab_choice (pr2 Y)) as [ isabY | eqY ] .
  simpl . 
  apply isover_Tj_Tj_int .
  exact ax1a . 

  exact isovXY . 


(*
Lemma T_1_Tj { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax1b : T_ax1b_type T ) 
      { A X1 X2 : BB } ( isab1 : isabove X1 A ) ( isab2 : isabove X2 A ) :
  Tj ax1b isab1 isab2 =
  T X1 ( Tj ax1b ( isover_ft' isab1 ) isab2 ) ( T_dom_1_Tj ax1b isab1 isab2 ) .   
Proof .
  intros .
  exact ( T_1_Tj_int ax1b ( ll X1 - ll A ) isab1 ( idpath _ ) isab2 ) . 

Defined.



Definition 

*)





(* Lemma T_dom_1_Tj { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
      { A X1 X2 : BB } ( isab1 : isabove X1 A ) ( isab2 : isabove X2 A ) : *)




*)



  
(* End of the file lBsystems_Tj_Ttj.v *)