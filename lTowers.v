(** * Presentation of towers through the length function

by Vladimir Voevodsky, started on Jan. 22, 2015, most material migrated from 
lBsystems_carriers.v 

*)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_prelim.


(** We formalize the sequences of types ...->B_{n+1}->B_n->...->B_0

as one type B with a length function ll and an endomorphism ft. *)


Definition lTower_str_data ( T : UU ) :=  dirprod ( T -> nat ) ( T -> T ) .

Definition lTower_str ( T : UU ) :=
  total2 ( fun str :lTower_str_data T =>
             dirprod 
               ( forall X : T , ( pr1 str ) ( pr2 str X ) = pr1 str X - 1 )
               ( forall ( X : T ) ( e : pr1 str X = 0 ) , pr2 str X = X ) ) .


Definition lTower := total2 ( fun T : UU => lTower_str T ) .

Definition lTower_data_pr1 : lTower -> UU := pr1 .
Coercion lTower_data_pr1 : lTower >-> UU .

Definition ll { X : lTower } : X -> nat := pr1 ( pr1 ( pr2 X ) ) . 

Definition ft { X : lTower } : X -> X := pr2 ( pr1 ( pr2 X ) ) .

Definition ftn { X : lTower } ( n : nat ) : X -> X := iteration ( @ft X ) n . 


Definition ll_ft { T : lTower } ( X : T ) : ll ( ft X ) = ll X - 1 :=
  pr1 ( pr2 ( pr2 T ) ) X .

Definition ftX_eq_X { T : lTower } { X : T } ( e : ll X = 0 ) : ft X = X :=
  pr2 ( pr2 ( pr2 T ) ) X e . 


(** Some useful lemmas about lTower *)

Lemma ll_ftn { BB : lTower } ( n : nat ) ( X : BB ) : ll ( ftn n X ) = ll X - n . 
Proof.
  intros BB n .
  induction n as [ | n IHn ] .
  intro . rewrite natminuseqn . apply idpath . 
  intro . change ( ftn ( S n ) X ) with ( ft ( ftn n X ) ) .  rewrite ( ll_ft _ ) . 
  rewrite ( IHn X ) .  rewrite ( natminusassoc _ _ _ ) .  rewrite ( natpluscomm n 1 ) . 
  apply idpath .
Defined .

  
Lemma ftn_ft { BB : lTower } ( n : nat ) ( X : BB ) :
  ftn n ( ft X ) = ftn ( 1 + n ) X .
Proof .
  intros . induction n as [ | n IHn ] .
  apply idpath . 
  apply ( maponpaths ( @ft BB ) IHn ) . 
Defined.

Lemma ftn_ftn { BB : lTower } ( m n : nat ) ( X : BB ) :
  ftn m ( ftn n X ) = ftn ( m + n ) X .
Proof.
  intros .  induction m as [ | m IHm ] . 
  exact ( idpath _ ) .
  apply ( maponpaths ft ) . 
  exact IHm .
Defined.


Lemma llTowergehll { BB : lTower } { X1 X2 : BB } ( gt : ll X2 > ll X1 ) :
  ll ( ft X2 ) >= ll X1 .
Proof.
  intros. rewrite ( ll_ft X2 ) . apply ( natgthtominus1geh gt ) . 
Defined .

Lemma llgehll { BB : lTower } { X1 X2 : BB } ( gt : ll X2 > ll ( ft X1 ) ) :
  ll X2 >= ll X1 .
Proof.
  intros. rewrite ( ll_ft X1 ) in gt . apply ( natgthminus1togeh gt ) . 
Defined .





Lemma lB_2014_12_07_l1 { m n : nat } ( gt : m > n ) : m - n = 1 + (( m - 1 ) - n ) .
Proof.
  intros. induction m as [ | m IHm ] . induction ( natgehn0 _ gt ) .
  clear IHm. change ( S m - n = S ( m - 0 - n ) ) . rewrite  ( natminuseqn m ) . 
  exact ( nat1plusminusgt gt ) .
Defined.



(* **** The predicate isover and its properties *)


Definition isover { BB : lTower } ( X A : BB ) := ( A = ftn ( ll X - ll A ) X ) .


Lemma isover_geh { BB : lTower } { X A : BB } ( is : isover X A ) :
  ll X >= ll A .
Proof.
  intros . unfold isover in is . 
  assert ( int : ll A = ll ( ftn (ll X - ll A) X ) ) . exact ( maponpaths ll is ) .

  rewrite int . rewrite ll_ftn . exact ( natminuslehn _ _ ) .
  
Defined.

Lemma isover_XX { BB : lTower } ( X : BB ) : isover X X .
Proof.
  intros . unfold isover . rewrite natminusnn . apply idpath . 

Defined.

Lemma isover_trans { BB : lTower } { X A A' : BB } :
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

Lemma isover_X_ftX { BB : lTower } ( X : BB ) : isover X ( ft X ) .
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

  
  
Lemma isover_X_ftA { BB : lTower } { X A : BB }
      ( is : isover X A ) : isover X ( ft A ) .
Proof.
  intros. exact ( isover_trans is ( isover_X_ftX _ ) ) . 

Defined.



Lemma isover_ft { BB : lTower } { X A : BB }
      ( is : isover X A ) ( gt : ll X > ll A ) : isover ( ft X ) A .
Proof.
  intros. unfold isover in * . 
  rewrite ftn_ft . rewrite ll_ft . rewrite <- lB_2014_12_07_l1 .
  exact is .

  exact gt .

Defined.

Lemma isover_ftn { BB : lTower } { n : nat } { X A : BB } 
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


Lemma isover_choice { BB : lTower } { X A : BB }
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








  
(** **** The predicate isabove and its properties *)


Definition isabove { BB : lTower } ( X A : BB ) :=
  dirprod ( ll X > ll A ) ( isover X A ) .

Definition isabove_constr { BB : lTower } { X A : BB }
           ( gt : ll X > ll A ) ( isov : isover X A ) : isabove X A :=
  tpair _ gt isov . 

Definition isabove_gth { BB : lTower } { X A : BB } ( is : isabove X A ) :
  ll X > ll A := pr1 is .

Definition isabove_to_isover { BB : lTower } { X A : BB } :
  isabove X A -> isover X A := pr2 .
Coercion isabove_to_isover : isabove >-> isover .

Lemma isabove_X_ftX { BB : lTower } ( X : BB ) ( gt0 : ll X > 0 ) : isabove X ( ft X ) .
Proof .
  intros .
  refine ( isabove_constr _ _ ) .
  rewrite ll_ft . 
  exact ( natgthnnmius1 gt0 ) . 

  exact ( isover_X_ftX _ ) . 

Defined.

  
Lemma isabove_X_ftA { BB : lTower } { X A : BB }
      ( is : isabove X A ) : isabove X ( ft A ) .
Proof .
  intros . refine ( isabove_constr _ _ ) .
  rewrite ll_ft . 
  exact ( natgthgehtrans _ _ _ ( isabove_gth is ) ( natminuslehn _ 1 ) ) . 

  exact (isover_X_ftA is ) .

Defined.


Lemma isabove_X_ftA' { BB : lTower } { X A : BB }
      ( is : isover X A ) ( gt0 : ll A > 0 ) : isabove X ( ft A ) .
Proof .
  intros . refine ( isabove_constr _ _ ) .
  rewrite ll_ft .
  refine ( natgehgthtrans _ _ _ ( isover_geh is ) _ ) .
  exact ( natgthnnmius1 gt0 ) . 

  exact ( isover_X_ftA is ) . 

Defined.



Lemma isabove_trans { BB : lTower } { X A A' : BB } :
  isabove X A -> isabove A A' -> isabove X A' .
Proof.
  intros BB X A A' is is' . refine ( isabove_constr _ _ ) .
  exact ( istransnatgth _ _ _ ( isabove_gth is ) ( isabove_gth is' ) ) .

  exact ( isover_trans is is' ) .

Defined.

Lemma isabov_trans { BB : lTower } { X A A' : BB } :
  isabove X A -> isover A A' -> isabove X A' .
Proof.
  intros BB X A A' is is' . refine ( isabove_constr _ _ ) .
  exact ( natgthgehtrans _ _ _ ( isabove_gth is ) ( isover_geh is' ) ) .

  exact ( isover_trans is is' ) .

Defined.

Lemma isovab_trans { BB : lTower } { X A A' : BB } :
  isover X A -> isabove A A' -> isabove X A' .
Proof.
  intros BB X A A' is is' . refine ( isabove_constr _ _ ) .
  exact ( natgehgthtrans _ _ _ ( isover_geh is ) ( isabove_gth is' ) ) .

  exact ( isover_trans is is' ) .

Defined.


Lemma isover_ft' { BB : lTower } { X A : BB } ( is : isabove X A ) :
  isover ( ft X ) A .
Proof .
  intros . exact ( isover_ft is ( isabove_gth is ) ) . 

Defined.

Lemma isabove_ft_inv { BB : lTower } { X A : BB } ( is : isabove ( ft X ) A ) :
  isabove X A .
Proof .
  intros . exact ( isovab_trans ( isover_X_ftX _ ) is ) .  

Defined.

Lemma isabove_choice { BB : lTower } { X A : BB } ( isab : isabove X A ) :
  coprod ( isabove ( ft X ) A ) ( A = ft X ) . 
Proof.
  intros .
  assert ( isov := isover_ft' isab ) . 
  assert ( gte : ll ( ft X ) >= ll A ) .
  exact ( llTowergehll ( isabove_gth isab ) ) .

  destruct ( natgehchoice _ _ gte ) as [ gt | eq ] .
  exact ( ii1 ( isabove_constr gt isov ) ) . 

  unfold isover in isov . 
  rewrite eq in isov . 
  rewrite natminusnn in isov . 
  exact ( ii2 isov ) . 

Defined.

Lemma isabove_choice_n { BB : lTower } ( n : nat ) { X A : BB } ( isab : isabove X A ) :
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

  
(** lTowers of sets *)

Definition hSet_lTower := total2 ( fun T : lTower => isaset T ) .

Definition hSet_lTower_pr1 : hSet_lTower -> lTower := pr1 . 
Coercion hSet_lTower_pr1 : hSet_lTower >-> lTower .


Definition isasetB ( X : hSet_lTower ) : isaset X := pr2 X .

Lemma isaprop_isover { BB : hSet_lTower } ( X A : BB ) : isaprop ( isover X A ) .
Proof .
  intros . exact ( isasetB _ _ _ ) . 

Defined.


Lemma isaprop_isabove { BB : hSet_lTower } ( X A : BB ) : isaprop ( isabove X A ) . 
Proof. 
  intros . 
  apply isapropdirprod . 
  exact ( pr2 ( _ > _ ) ) .

  exact ( isaprop_isover _ _ ) . 

Defined.






  


(* End of the file lTowers.v *)