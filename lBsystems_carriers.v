(** * Carriers of the B-systems defined in terms of two sorts and the length function 

by Vladimir Voevodsky, file created on Jan. 6, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems_prelim.

(** ** Non-unital pre-l-B-systems *)

(** *** l-B-system carriers. *)

(** **** Definitions *)

Definition lBsystem_carrier_0 := total2 ( fun BB : total2 ( fun BtildeB : dirprod hSet hSet =>
                                          dirprod ( pr1 BtildeB -> pr1 BtildeB )
                                                  ( pr2 BtildeB -> pr1 BtildeB ) ) =>
                                            pr1 ( pr1 BB ) -> nat ) .

Definition Btype : lBsystem_carrier_0 -> UU := fun BB => pr1 ( pr1 ( pr1 BB ) ) . 
Coercion Btype : lBsystem_carrier_0 >-> UU .

Definition Tilde : lBsystem_carrier_0 -> UU := fun BB => pr2 ( pr1 ( pr1 BB ) ) .

Definition ft { BB : lBsystem_carrier_0 } : BB -> BB := pr1 ( pr2 ( pr1 BB ) ) .

Definition ftn { BB : lBsystem_carrier_0 } ( n : nat ) : BB -> BB := iteration ( @ft BB ) n . 

Definition dd { BB : lBsystem_carrier_0 } : Tilde BB -> BB := pr2 ( pr2 ( pr1 BB ) ) .

Definition ll { BB : lBsystem_carrier_0 } : BB -> nat := pr2 BB .

Definition isasetB ( BB : lBsystem_carrier_0 ) : isaset BB := pr2 ( pr1 ( pr1 ( pr1 BB ) ) ) .

Definition isasetBt ( BB : lBsystem_carrier_0 ) : isaset ( Tilde BB ) :=
  pr2 ( pr2 ( pr1 ( pr1 BB ) ) ) . 

Definition lBsystem_carrier :=
  total2 ( fun BB :  lBsystem_carrier_0 =>
             dirprod
               ( dirprod ( forall ( X : BB ) ( gt : ll X > 0 ) , 1 + ll ( ft X ) = ll X )
                         ( forall ( X : BB ) ( e : ll X = 0 ) , ft X = X ) )
               ( forall r : Tilde BB , ll ( dd r ) > 0 ) ) .
                                        
Definition lBsystem_carrier_to_carrier_0 : lBsystem_carrier -> lBsystem_carrier_0 := pr1 .
Coercion lBsystem_carrier_to_carrier_0 : lBsystem_carrier >-> lBsystem_carrier_0 .

Definition ft_choice { BB : lBsystem_carrier } ( X : BB ) : coprod ( ll X > 0 ) ( ll X = 0 ) :=
  natgehchoice _ _ ( natgehn0 _ ) . 

Definition inc_ll_ft { BB : lBsystem_carrier } ( X : BB ) ( gt : ll X > 0 ) :
  1 + ll ( ft X ) = ll X := pr1 ( pr1 ( pr2 BB ) ) X gt .

Definition ftX_eq_X { BB : lBsystem_carrier } { X : BB } ( e : ll X = 0 ) : ft X = X :=
  pr2 ( pr1 ( pr2 BB ) ) X e .

Definition ll_dd { BB : lBsystem_carrier } ( r : Tilde BB ) : ll ( dd r ) > 0 :=
  pr2 ( pr2 BB ) r .


(* Lemma ll_ft { BB : lBsystem_carrier } ( X : BB ) : ll ( ft X ) = ll X - 1 .
Proof .
  intros .
  destruct ( ft_choice X ) as [ gt | eq ] .
  apply ( natpluslcan _ _ 1 ) . 
  rewrite ( natpluscomm _ ( ll X - 1 ) ) .
  rewrite minusplusnmm . 
  exact ( inc_ll_ft _ gt ) . 

  exact ( natgthtogehsn _ _ gt ) . 

  rewrite eq . 
  rewrite ( ftX_eq_X eq ) . 
  exact eq . 


Defined. *)


  




(** **** Useful lemmas *)


Definition ftn_choice { BB : lBsystem_carrier } ( n : nat ) ( X : BB ) :
  coprod ( ll X >= n ) ( ll X < n ) .
Proof.
  intros . destruct ( natgthorleh n ( ll X ) ) as [ gt | le ] .
  exact ( ii2 gt ) . 

  exact ( ii1 le ) .

Defined.


Lemma nplus_ll_ftn { BB : lBsystem_carrier } ( n : nat ) ( X : BB ) ( ge :  ll X >= n ) :
  n + ll ( ftn n X ) = ll X .
Proof .
  intros BB n . induction n as [ | n IHn ] .
  intros . apply idpath . 

  *** Unfinished ***
  







  
(* Lemma ll_ftn { BB : lBsystem_carrier } ( n : nat ) ( X : BB ) : ll ( ftn n X ) = ll X - n . 
Proof.
  intros BB n .
  induction n as [ | n IHn ] .
  intro . rewrite natminuseqn . apply idpath . 
  intro . change ( ftn ( S n ) X ) with ( ft ( ftn n X ) ) .  rewrite ( ll_ft _ ) . 
  rewrite ( IHn X ) .  rewrite ( natminusassoc _ _ _ ) .  rewrite ( natpluscomm n 1 ) . 
  apply idpath .
Defined . *)

  
Lemma ftn_ft { BB : lBsystem_carrier_0 } ( n : nat ) ( X : BB ) :
  ftn n ( ft X ) = ftn ( 1 + n ) X .
Proof .
  intros . induction n as [ | n IHn ] .
  apply idpath . 
  apply ( maponpaths ( @ft BB ) IHn ) . 
Defined.

Lemma ftn_ftn { BB : lBsystem_carrier_0 } ( m n : nat ) ( X : BB ) :
  ftn m ( ftn n X ) = ftn ( m + n ) X .
Proof.
  intros .  induction m as [ | m IHm ] . 
  exact ( idpath _ ) .
  apply ( maponpaths ft ) . 
  exact IHm .
Defined.


Lemma llftgehll { BB : lBsystem_carrier } { X1 X2 : BB } ( gt : ll X2 > ll X1 ) :
  ll ( ft X2 ) >= ll X1 .
Proof.
  intros.
  change ( 1 + ll (ft X2) >= 1 + ll X1 ) . 
  assert ( gt' := natgthgehtrans _ _ _ gt ( natgehn0 _ ) ) . 
  rewrite ( inc_ll_ft _ gt' ) . 
  exact ( natgthtogehsn _ _ gt ) . 

Defined .

Lemma inc_ll_ft_geh { BB : lBsystem_carrier } ( X : BB ) : 1 + ll ( ft X ) >= ll X .
Proof .
  intros . destruct ( ft_choice X ) as [ gt | eq ] .
  rewrite ( inc_ll_ft _ gt ) .  apply isreflnatgeh . 

  rewrite eq .
  apply ( natgehn0 _ ) . 

Defined.

Lemma llgehll { BB : lBsystem_carrier } { X1 X2 : BB } ( gt : ll X2 > ll ( ft X1 ) ) :
  ll X2 >= ll X1 .
Proof.
  intros.
  assert ( ge := natgthtogehsn _ _ gt ) .
  exact ( istransnatgeh _ _ _ ge ( inc_ll_ft_geh _ ) ) .

Defined.





Lemma lB_2014_12_07_l1 { m n : nat } ( gt : m > n ) : m - n = 1 + (( m - 1 ) - n ) .
Proof.
  intros. induction m as [ | m IHm ] . induction ( natgehn0 _ gt ) .
  clear IHm. change ( S m - n = S ( m - 0 - n ) ) . rewrite  ( natminuseqn m ) . 
  exact ( nat1plusminusgt gt ) .
Defined.



(* **** The predicate isover and its properties *)


Definition isover { BB : lBsystem_carrier } ( X A : BB ) := ( A = ftn ( ll X - ll A ) X ) .


Lemma isover_geh { BB : lBsystem_carrier } { X A : BB } ( is : isover X A ) :
  ll X >= ll A .
Proof.
  intros . unfold isover in is . 
  assert ( int : ll A = ll ( ftn (ll X - ll A) X ) ) . exact ( maponpaths ll is ) .

  rewrite int . rewrite ll_ftn . exact ( natminuslehn _ _ ) .
  
Defined.

Lemma isover_XX { BB : lBsystem_carrier } ( X : BB ) : isover X X .
Proof.
  intros . unfold isover . rewrite natminusnn . apply idpath . 

Defined.

Lemma isover_trans { BB : lBsystem_carrier } { X A A' : BB } :
  isover X A -> isover A A' -> isover X A' .
Proof.
  intros BB X A A' .  unfold isover in * .
  set ( llA := ll A ) . set ( llA' := ll A' ) . 
  intro is1 . intro is2 .
  assert ( gte1 := isover_geh is1 ) .
  assert ( gte2 := isover_geh is2 ) . 
  rewrite is2 . rewrite is1 .  
  rewrite ftn_ftn . 
  assert (int : (llA - llA' + (ll X - llA)) = (ll X - llA')) .
  rewrite natpluscomm . 
  exact ( ! ( natminusinter gte1 gte2 ) ) . 

  rewrite int .
  apply idpath .
  
Defined.

Lemma isover_X_ftX { BB : lBsystem_carrier } ( X : BB ) : isover X ( ft X ) .
Proof.
  intros . 
  unfold isover .
  destruct ( natgehchoice _ _ ( natgehn0 ( ll X ) ) )  as [ gt | eq ] . 
  rewrite ll_ft . 
  assert ( eq : ll X - ( ll X - 1 ) = 1 ) . refine ( natminusmmk _ ) . 
  exact ( natgthtogehsn _ _ gt ) . 

  rewrite eq .
  apply idpath . 

  rewrite eq . 
  simpl . 
  exact ( ftX_eq_X eq ) . 

Defined.

  
  
Lemma isover_X_ftA { BB : lBsystem_carrier } { X A : BB }
      ( is : isover X A ) : isover X ( ft A ) .
Proof.
  intros. exact ( isover_trans is ( isover_X_ftX _ ) ) . 

Defined.



Lemma isover_ft { BB : lBsystem_carrier } { X A : BB }
      ( is : isover X A ) ( gt : ll X > ll A ) : isover ( ft X ) A .
Proof.
  intros. unfold isover in * . 
  rewrite ftn_ft . rewrite ll_ft . rewrite <- lB_2014_12_07_l1 .
  exact is .

  exact gt .

Defined.

Lemma isover_ftn { BB : lBsystem_carrier } { n : nat } { X A : BB } 
      ( is : isover X A ) ( gte : ll X - ll A >= n ) : isover ( ftn n X ) A .
Proof.
  intros BB n. induction n as [ | n IHn ] .
  intros .  exact is .

  intros . simpl .
  refine ( isover_ft _ _ ) .
  refine ( IHn _ _ _ _ ) . 
  exact is .

  exact ( istransnatgeh _ _ _ gte ( natgehsnn n ) ) .

  rewrite ll_ftn . 
  refine ( natgthleftminus _ _ _ _ ) . 
  assert ( int := natgehgthtrans _ _ _ gte ( natgthsnn n ) ) . 
  rewrite natpluscomm . 
  exact ( natgthrightplus _ _ _ int ) .

Defined .


Lemma isover_choice { BB : lBsystem_carrier } { X A : BB }
      ( is : isover X A ) : coprod ( isover ( ft X ) A ) ( A = X ) .
Proof .
  intros . 
  destruct ( natgehchoice _ _ ( isover_geh is ) ) as [ gt | eq ] . 
  exact ( ii1 ( isover_ft is gt ) ) . 

  unfold isover in is . 
  rewrite eq in is . 
  rewrite natminusnn in is . 
  exact ( ii2 is ) .

Defined.





Lemma isaprop_isover { BB : lBsystem_carrier } ( X A : BB ) : isaprop ( isover X A ) .
Proof .
  intros . exact ( isasetB _ _ _ ) . 

Defined.





  
(** **** The predicate isabove and its properties *)


Definition isabove { BB : lBsystem_carrier } ( X A : BB ) :=
  dirprod ( ll X > ll A ) ( isover X A ) .

Definition isabove_constr { BB : lBsystem_carrier } { X A : BB }
           ( gt : ll X > ll A ) ( isov : isover X A ) : isabove X A :=
  tpair _ gt isov . 

Definition isabove_gth { BB : lBsystem_carrier } { X A : BB } ( is : isabove X A ) :
  ll X > ll A := pr1 is .

Definition isabove_to_isover { BB : lBsystem_carrier } { X A : BB } :
  isabove X A -> isover X A := pr2 .
Coercion isabove_to_isover : isabove >-> isover . 

Lemma isabove_X_ftA { BB : lBsystem_carrier } { X A : BB }
      ( is : isabove X A ) : isabove X ( ft A ) .
Proof .
  intros . refine ( isabove_constr _ _ ) .
  rewrite ll_ft . 
  exact ( natgthgehtrans _ _ _ ( isabove_gth is ) ( natminuslehn _ 1 ) ) . 

  exact (isover_X_ftA is ) .

Defined.


Lemma isabove_trans { BB : lBsystem_carrier } { X A A' : BB } :
  isabove X A -> isabove A A' -> isabove X A' .
Proof.
  intros BB X A A' is is' . refine ( isabove_constr _ _ ) .
  exact ( istransnatgth _ _ _ ( isabove_gth is ) ( isabove_gth is' ) ) .

  exact ( isover_trans is is' ) .

Defined.

Lemma isabov_trans { BB : lBsystem_carrier } { X A A' : BB } :
  isabove X A -> isover A A' -> isabove X A' .
Proof.
  intros BB X A A' is is' . refine ( isabove_constr _ _ ) .
  exact ( natgthgehtrans _ _ _ ( isabove_gth is ) ( isover_geh is' ) ) .

  exact ( isover_trans is is' ) .

Defined.

Lemma isovab_trans { BB : lBsystem_carrier } { X A A' : BB } :
  isover X A -> isabove A A' -> isabove X A' .
Proof.
  intros BB X A A' is is' . refine ( isabove_constr _ _ ) .
  exact ( natgehgthtrans _ _ _ ( isover_geh is ) ( isabove_gth is' ) ) .

  exact ( isover_trans is is' ) .

Defined.


Lemma isover_ft' { BB : lBsystem_carrier } { X A : BB } ( is : isabove X A ) :
  isover ( ft X ) A .
Proof .
  intros . exact ( isover_ft is ( isabove_gth is ) ) . 

Defined.

Lemma isabove_ft_inv { BB : lBsystem_carrier } { X A : BB } ( is : isabove ( ft X ) A ) :
  isabove X A .
Proof .
  intros . exact ( isovab_trans ( isover_X_ftX _ ) is ) .  

Defined.

Lemma isabove_choice { BB : lBsystem_carrier } { X A : BB } ( isab : isabove X A ) :
  coprod ( isabove ( ft X ) A ) ( A = ft X ) . 
Proof.
  intros .
  assert ( isov := isover_ft' isab ) . 
  assert ( gte : ll ( ft X ) >= ll A ) .
  exact ( llftgehll ( isabove_gth isab ) ) .

  destruct ( natgehchoice _ _ gte ) as [ gt | eq ] .
  exact ( ii1 ( isabove_constr gt isov ) ) . 

  unfold isover in isov . 
  rewrite eq in isov . 
  rewrite natminusnn in isov . 
  exact ( ii2 isov ) . 

Defined.

Lemma isabove_choice_n { BB : lBsystem_carrier } ( n : nat ) { X A : BB } ( isab : isabove X A ) :
  coprod ( isabove ( ftn n X ) A ) ( isover A ( ftn n X ) ) .
Proof .
  intros BB n . induction n as [ | n IHn ] .
  intros . 
  exact ( ii1 isab ) . 

  intros . 
  assert ( int := IHn X A isab ) . 
  destruct int as [ isab' | isov ] . 
  destruct ( isabove_choice isab' ) as [ isab'' | iseq ] .
  exact ( ii1 isab'' ) .

  refine ( ii2 _ ) . 
  unfold isover .
  rewrite iseq . 
  rewrite natminusnn . 
  apply idpath . 

  exact ( ii2 ( isover_X_ftA isov ) ) . 

Defined.

  


  

Lemma isaprop_isabove { BB : lBsystem_carrier } ( X A : BB ) : isaprop ( isabove X A ) . 
Proof. 
  intros . 
  apply isapropdirprod . 
  exact ( pr2 ( _ > _ ) ) .

  exact ( isaprop_isover _ _ ) . 

Defined.

   
(* End of the file lBsystems_carriers.v *)

