(** * Definition of B-systems using the length function.

Vladimir Voevodsky. 

Started December 3, 2014. 

A companion code to the paper "B-systems". 

*)


Unset Automatic Introduction.

Require Export Foundations.hlevel2.finitesets.


(* To upsetream files *)


Notation isaproptotal2 := ( isofhleveltotal2 1 )  .

Lemma natgthnnmius1 { n : nat } ( gt : n > 0 ) : n > n - 1 .
Proof.
  intros . induction n as [ | n ] . 
  induction ( negnatgthnn _ gt ) . 

  change ( S n > n - 0 ) . 
  rewrite natminuseqn . 
  exact ( natgthsnn _ ) .

Defined.

Lemma natminusnn ( n : nat ) : n - n = 0 .
Proof.
  intro . induction n as [ | n IHn ] .
  exact ( idpath _ ) .

  exact IHn . 

Defined.

Lemma natmiusmius1mminus1 { n m : nat } ( gt1 : n > 0 ) ( gt2 : m > 0 ) :
  ( n - 1 ) - ( m - 1 ) = n - m .
Proof .
  intro n . induction n as [ | n IHn ] .
  intros . 
  destruct ( negnatgthnn _ gt1 ) . 

  intros .
  simpl . rewrite natminuseqn . induction m as [ | m ] .
  destruct ( negnatgthnn _ gt2 ) . 

  simpl . rewrite natminuseqn . apply idpath .

Defined.








  
Lemma natleftplustorightminus ( n m k : nat ) : n + m = k -> n = k - m .
Proof.
  intros n m k e .
  assert ( ge : k >= m ) . rewrite <- e . exact ( natgehplusnmm _ _ ) .  

  apply ( natplusrcan _ _ m ) . rewrite ( minusplusnmm _ _ ge ) . 
  exact e .

Defined.


Lemma natgthtominus1geh { m n : nat } : ( m > n ) -> ( m - 1 >= n ) .
Proof.
  intro m . induction m as [ | m IHm ] .
  intros n gt . induction ( natgehn0 _ gt ) .
  
  intros n gt .
  change ( m - 0 >= n ) . rewrite ( natminuseqn m ) . apply natgthsntogeh . exact gt .
  
Defined .

Lemma natgthminus1togeh { n m : nat } : ( m > n - 1 ) -> ( m >= n ) .
Proof.
  intro n . induction n as [ | n IHn ] .
  intros m gt . exact ( natgehn0 _ ) .
  
  intros m gt .
  change ( S n - 1 ) with ( n - 0 ) in gt . rewrite ( natminuseqn n ) in gt .
  apply natgthtogehsn . exact gt .
  
Defined .


Definition natassocpmeq ( n m k : nat ) ( ge : m >= k ) : (( n + m ) - k ) =  ( n + ( m - k )) .
Proof. intros.  apply ( natplusrcan _ _ k ) . rewrite ( natplusassoc n _ k ) .
       rewrite ( minusplusnmm _ k ge ) .
       set ( ge' := istransnatgeh _ _ _ ( natgehplusnmm n m ) ge ) .
       rewrite ( minusplusnmm _ k ge' ) . apply idpath.
Defined.

Definition natassocmpeq ( n m k : nat ) ( isnm : n >= m ) ( ismk : m >= k ) :
  ( n - m ) + k = n - ( m - k ) .
Proof. intros.  apply ( natplusrcan _ _ ( m - k ) ) . 
       assert ( is' : natleh ( m - k ) n ) .
       apply ( istransnatleh _ _ _ (natminuslehn _ _ ) isnm ) .
       rewrite ( minusplusnmm _ _ is' ) . rewrite (natplusassoc _ k _ ) .
       rewrite ( natpluscomm k _ ) . rewrite ( minusplusnmm _ _ ismk ) .
       rewrite ( minusplusnmm _ _ isnm ) . apply idpath.
Defined.



Lemma natminusind ( m n : nat ) : m - S n = ( m - 1 ) - n . 
Proof . intros .
        induction m as [ | m IHm ] .  apply idpath . simpl .  rewrite ( natminuseqn m ) . 
        apply idpath .
Defined.


Definition natminusassoc ( n m k : nat ) : ( n  - m ) - k = n - ( m + k ) .
Proof. intros n m . revert n . 

       induction m as [ | m IHm ] .  intros  . simpl .  rewrite ( natminuseqn n ) . apply idpath .
       intros .  rewrite ( natminusind n m ) .  rewrite ( IHm ( n - 1 ) k ) .
       rewrite ( ! ( natminusind _ _ ) ) .  apply idpath . 
Defined. 


Lemma nat1plusminusgt { n m : nat } ( gt : 1 + m > n ) : ( 1 + m ) - n = 1 + ( m - n ) .
Proof.
  intros .  assert ( ge : m >= n ) . apply ( natgthsntogeh _ _ gt ) . 
  exact ( natassocpmeq _ _ _ ge ) . 
Defined.


Lemma natminusmmk { m k : nat } ( ge : m >= k ) : m - ( m - k ) = k .
Proof.
  intros .  rewrite ( ! ( natassocmpeq m m k ( isreflnatgeh m ) ge ) ) .
  rewrite ( natminusnn m ) . 
  apply idpath .
Defined.


Definition natminusinter { n m k : nat } ( ge1 : n >= m ) ( ge2 : m >= k ) :
  n - k = ( n - m ) + ( m - k ) .
Proof.
  intros .
  assert ( int1 : n - m + (m - k) = n - ( m - ( m - k ))).   refine ( natassocmpeq _ _ _ _ _ ) . 
  exact ge1 . 

  exact ( natminuslehn _ _ ) . 

  assert ( int2 : m - ( m - k ) = k ) . exact ( natminusmmk ge2 ) .

  rewrite int2 in int1 . exact ( ! int1 ) . 
Defined.


(** [ nateq ] *)

Notation nateqandplusrinv := natplusrcan .

Notation nateqandpluslinv := natpluslcan .

Definition nateqandplusr ( n m k : nat ) : n = m -> n + k = m + k :=
  maponpaths ( fun x => x + k ) .

Definition nateqandplusl ( n m k : nat ) : n = m -> k + n = k + m :=
  maponpaths ( fun x => k + x ) .







  

(* **** Greater and minus *)


Definition natgthrightminus ( n m k : nat ) ( ge : k >= m ) : n + m > k -> n > k - m .
Proof . intros n m k ge gt . apply ( natgthandplusrinv _ _ m ) .
        rewrite ( minusplusnmm _ _ ge ) .
        exact gt .
Defined.

Definition natgthrightplus ( n m k : nat ) : n - m > k -> n > k + m .
Proof .
  intros n m k gt . assert ( ge : n >= m ) . apply natgthtogeh .
  
  apply minusgth0inv .  apply ( natgthgehtrans _ _ _ gt ( natgehn0 k ) ) .
  assert ( gt' : ( n - m ) + m > k + m ) . apply ( natgthandplusr _ _ _ gt ) .
  
  rewrite ( minusplusnmm _ _ ge ) in gt' . exact gt' .
Defined.
  
Definition natgthleftminus ( n m k : nat ) : n > m + k -> n - k > m .
Proof.
  intros n m k gt .  apply ( natgthandplusrinv _ _ k ) .
  assert ( ge' : n >= k ) . apply natgthtogeh .
  exact ( natgthgehtrans _ _ _ gt ( natgehplusnmm _ _ ) ) .
  
  rewrite ( minusplusnmm _ _ ge' ) . 
  exact gt .
Defined.


Definition natgthleftplus ( n m k : nat ) : n > m - k -> n + k > m .
Proof .
  intros n m k gt .
  assert ( gt' : n + k > m - k + k ) .  exact ( natgthandplusr _ _ k gt ) . 
  exact ( natgthgehtrans _ _ _ gt' ( minusplusnmmineq _ _ ) ) . 
Defined .

Definition natgthleftminusminus ( n m k : nat ) : n - m > k -> n - k > m .
Proof .
  intros n m k gt . assert ( gt' : n > k + m ) . exact ( natgthrightplus _ _ _ gt ) .

  rewrite ( natpluscomm _ _ ) in gt' . exact ( natgthleftminus _ _ _ gt' ) . 
Defined.


  

(* **** Greater or equal and minus *)

Definition natgehrightminus ( n m k : nat ) ( ge : k >= m ) : n + m >= k -> n >= k - m .
Proof.
  intros n m k ge ge' . apply ( natgehandplusrinv _ _ m ) .  rewrite ( minusplusnmm _ _ ge ) .
  exact ge' .
Defined.


Definition natgehrightplus ( n m k : nat ) ( ge : n >= m ) : n - m >= k -> n >= k + m .
Proof.
  intros n m k ge ge' .  rewrite ( ! minusplusnmm _ _ ge ) .  apply ( natgehandplusr _ _ _ ) . 
  exact ge' .
Defined.

Definition natgehleftminus ( n m k : nat ) : n >= m + k ->  n - k >= m .
Proof.
  intros n m k ge .  apply ( natgehandplusrinv _ _ k ) .
  assert ( ge' : n >= k ) . exact ( istransnatgeh _ _ _ ge ( natgehplusnmm _ _ ) ) .
  rewrite ( minusplusnmm _ _ ge' ) . 
  exact ge .
Defined.

Definition natgehleftplus ( n m k : nat ) : n >= m - k -> n + k  >= m .
Proof.
  intros n m k ge .
  assert ( ge' : n + k >= m - k + k ) .  exact ( natgehandplusr _ _ k ge ) . 
  exact ( istransnatgeh _ _ _ ge' ( minusplusnmmineq _ _ ) ) . 
Defined .

Definition natgehleftminusminus ( n m k : nat ) ( ge : n >= m ) : n - m >= k -> n - k >= m .
Proof .
  intros n m k ge ge' . assert ( ge'' : n >= k + m ) . exact ( natgehrightplus _ _ _ ge ge' ) .

  rewrite ( natpluscomm _ _ ) in ge'' . exact ( natgehleftminus _ _ _ ge'' ) . 
Defined.


(* Two-sided minus and greater *)

Definition natgthandminusinvr { n m k : nat } ( is : n > m ) ( is' : m >= k ) :
  n - k > m - k .
Proof .
  intro n. induction n as [ | n IHn ] .
  intros . destruct ( negnatgth0n _ is ) .
  
  intro m . induction k as [ | k ] . intros .
  repeat rewrite natminuseqn .
  exact is .

  intros . induction m as [ | m ] .
  destruct ( negnatgeh0sn _ is' ) .

  exact ( IHn m k is is' ) .

Defined.



(* Two-sided minus and greater or equal *) 

Definition natgehandminusl ( n m k : nat ) ( ge : n >= m ) : k - m >= k - n .
Proof.
  intro n. induction n as [ | n IHn ] .
  intros .  rewrite ( nat0gehtois0 _ ge ) . apply isreflnatleh .

  intro m . induction m as [ | m ] . intros . induction k as [ | k ] .
  apply natminuslehn .

  apply natminuslehn .

  intro k . induction k as [ | k ] . intro is .
  apply isreflnatleh .

  intro is .  apply ( IHn m k ) . apply is .

Defined.


Definition natgthandminuslinv { n m k : nat } ( gt : n - k > n - m ) : m > k .
Proof .
  intros .
  apply ( negnatlehtogth _ _ ) . 
  intro ge . 
  assert ( ge' : n - m >= n - k ) . 
  exact ( natgehandminusl _ _ _ ge ) .

  exact ( ge' gt ) . 

Defined.


  

(* Decrement function on nat *)

Definition dec ( n : nat ) : nat :=
  match n with
      O => O |
    S n' => n'
  end .




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
               ( dirprod ( forall X : BB , ll ( ft X ) = ll X - 1 )
                         ( forall ( X : BB ) ( e : ll X = 0 ) , ft X = X ) )
               ( forall r : Tilde BB , ll ( dd r ) > 0 ) ) .
                                        
Definition lBsystem_carrier_to_carrier_0 : lBsystem_carrier -> lBsystem_carrier_0 := pr1 .
Coercion lBsystem_carrier_to_carrier_0 : lBsystem_carrier >-> lBsystem_carrier_0 .

Definition ll_ft { BB : lBsystem_carrier } ( X : BB ) : ll ( ft X ) = ll X - 1 :=
  pr1 ( pr1 ( pr2 BB ) ) X .

Definition ftX_eq_X { BB : lBsystem_carrier } { X : BB } ( e : ll X = 0 ) : ft X = X :=
  pr2 ( pr1 ( pr2 BB ) ) X e .

Definition ll_dd { BB : lBsystem_carrier } ( r : Tilde BB ) : ll ( dd r ) > 0 :=
  pr2 ( pr2 BB ) r .



(** **** Useful lemmas *)



Lemma ll_ftn { BB : lBsystem_carrier } ( n : nat ) ( X : BB ) : ll ( ftn n X ) = ll X - n . 
Proof.
  intros BB n .
  induction n as [ | n IHn ] .
  intro . rewrite natminuseqn . apply idpath . 
  intro . change ( ftn ( S n ) X ) with ( ft ( ftn n X ) ) .  rewrite ( ll_ft _ ) . 
  rewrite ( IHn X ) .  rewrite ( natminusassoc _ _ _ ) .  rewrite ( natpluscomm n 1 ) . 
  apply idpath .
Defined .

  
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
  intros. rewrite ( ll_ft X2 ) . apply ( natgthtominus1geh gt ) . 
Defined .

Lemma llgehll { BB : lBsystem_carrier } { X1 X2 : BB } ( gt : ll X2 > ll ( ft X1 ) ) :
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

   

  
(** *** l-B-sytems operations T, Tt, S, St.

Since we have to work with operations that are not everywhere defined we start by 
naming their domains of definitions and then defining operations as total operations
on the domains of definition. This has the advantage that when we need to state and
prove results that involve compositions of operations we can conveniently package 
the proofs that the compositive operations are defined in definition of functions 
such as the function ??? below. 

*)


(** **** Operation(s) T.

Including constructions related to their domains of definition. *)

(** Domains of definition of operations of type T *)

Definition T_dom { BB : lBsystem_carrier } ( X1 X2 : BB ) :=
  dirprod ( ll X1 > 0 ) ( isabove X2 ( ft X1 ) ) .

Definition T_dom_constr { BB : lBsystem_carrier } { X1 X2 : BB }
           ( gt0 : ll X1 > 0 ) ( isab : isabove X2 ( ft X1 ) ) : T_dom X1 X2 :=
  tpair _ gt0 isab .
  
Definition T_dom_gt0 { BB : lBsystem_carrier } { X1 X2 : BB } ( inn : T_dom X1 X2 ) :
  ll X1 > 0 := pr1 inn .

Definition T_dom_gth { BB : lBsystem_carrier } { X1 X2 : BB } ( inn : T_dom X1 X2 ) :
  ll X2 > ll ( ft X1 ) := isabove_gth ( pr2 inn ) .

Definition T_dom_isabove { BB : lBsystem_carrier } { X1 X2 : BB } ( inn : T_dom X1 X2 ) :
  isabove X2 ( ft X1 ) := pr2 inn . 

Definition T_dom_geh { BB : lBsystem_carrier } { X1 X2 : BB } ( inn : T_dom X1 X2 ) :
  ll X2 >= ll X1 .
Proof .
  intros . assert ( gt := T_dom_gth inn ) . 
  assert ( gte := natgthtogehsn _ _ gt ) . 
  refine ( istransnatgeh _ _ _ gte _ ) . 
  rewrite ll_ft . 
  change ( 1 + ( ll X1 - 1 ) >= ll X1 ) . 
  rewrite natpluscomm . 
  exact ( minusplusnmmineq _ _ ) . 

Defined.

  
  
Lemma isaprop_T_dom { BB : lBsystem_carrier } ( X1 X2 : BB ) : isaprop ( T_dom X1 X2 ) . 
Proof.
  intros . 
  apply isapropdirprod . 
  apply ( pr2 ( _ > _ ) ) .
  
  exact ( isaprop_isabove _ _ ) . 

Defined.

Lemma noparts_T_dom { BB : lBsystem_carrier } { X1 X2 : BB } ( inn1 inn2 : T_dom X1 X2 ) :
  inn1 = inn2 .
Proof .
  intros . apply ( proofirrelevance _ ( isaprop_T_dom X1 X2 ) ) .
Defined .


Definition T_dom_comp { BB : lBsystem_carrier } { X1 X2 X3 : BB }
           ( inn12 : T_dom X1 X2 ) ( inn23 : T_dom X2 X3 ) : T_dom X1 X3 .
Proof.
  intros.
  assert ( gt0 := T_dom_gt0 inn12 ) . 
  assert ( is21 := T_dom_isabove inn12 ) . assert ( is32 := T_dom_isabove inn23 ) .
  refine ( T_dom_constr _ _ ) . 
  exact gt0 .

  exact ( isabov_trans is32 ( isover_ft' is21 ) ) . 

Defined.



(** The type objects of which are candidates for operations T on an lB-system. *)
 
Definition T_ops_type ( BB : lBsystem_carrier ) :=
  forall ( X1 X2 : BB ) ( inn : T_dom X1 X2 ) , BB .


Lemma T_equals_2 { BB : lBsystem_carrier } { X1 X2 X2' : BB } ( T : T_ops_type BB )
      ( eq : X2 = X2' ) ( inn : T_dom X1 X2 ) ( inn' : T_dom X1 X2' )  :
  T X1 X2 inn = T X1 X2' inn' .
Proof.
  intros BB X1 X2 X2' T eq .
  rewrite eq . 
  intros . rewrite ( noparts_T_dom inn inn' ) . 
  apply idpath . 

Defined.


  

(** The zeros property (later an axiom) of an operation of type T *)

Definition T_ax0_type { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  forall ( X1 X2 : BB ) ( inn : T_dom X1 X2 ) , ( ll ( T X1 X2 inn ) = 1 + ( ll X2 ) ) .

(** The first property (later an axiom) of an operation of type T *)


Lemma T_ax1a_dom { BB : lBsystem_carrier } { X1 X2 : BB } ( inn : T_dom X1 X2 )
      ( isab : isabove ( ft X2 ) ( ft X1 ) ) : T_dom X1 ( ft X2 ) .
Proof .
  intros. exact ( T_dom_constr ( T_dom_gt0 inn ) isab ) . 

Defined.

Definition T_ax1a_type { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  forall ( X1 X2 : BB ) ( inn : T_dom X1 X2 ) ( isab : isabove ( ft X2 ) ( ft X1 ) ) ,
    ft ( T X1 X2 inn ) = T X1 ( ft X2 ) ( T_ax1a_dom inn isab ) .


Definition T_ax1b_type { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  forall ( X1 X2 : BB ) ( inn : T_dom X1 X2 ) , isabove ( T X1 X2 inn ) X1 .


(** The computation of the iterated ft of ( T X1 X2 ) .  *)

Lemma T_dom_ftn { BB : lBsystem_carrier } { X1 X2 : BB } ( n : nat ) ( inn : T_dom X1 X2 )
      ( isab : isabove ( ftn n X2 ) ( ft X1 ) ) : T_dom X1 ( ftn n X2 ) .
Proof .
  intros. exact ( T_dom_constr ( T_dom_gt0 inn ) isab ) . 

Defined.

Lemma ftn_T { BB : lBsystem_carrier } { T : T_ops_type BB } ( ax1a : T_ax1a_type T )
      ( n : nat ) { X1 X2 : BB } ( isab : isabove ( ftn n X2 ) ( ft X1 ) )
      ( inn : T_dom X1 X2 ) :
  ftn n ( T X1 X2 inn ) = T X1 ( ftn n X2 ) ( T_dom_ftn n inn isab ) .
Proof .
  intros BB T ax1a n . induction n as [ | n IHn ] .
  intros .
  rewrite ( noparts_T_dom inn (T_dom_ftn 0 inn isab) ) . 
  apply idpath . 

  intros .
  change ( ftn (S n) (T X1 X2 inn) ) with ( ft ( ftn n (T X1 X2 inn) ) ) .
  assert ( isab' : isabove ( ftn n X2 ) ( ft X1 ) ) .
  exact ( isabove_ft_inv isab ) . 
  
  rewrite ( IHn X1 X2 isab' inn ) . 
  refine ( ax1a _ _ _ _ ) . 

Defined.


Lemma ft_T { BB : lBsystem_carrier } { T : T_ops_type BB } { X1 X2 : BB } ( ax0 : T_ax0_type T )
      ( ax1b : T_ax1b_type T ) ( iseq : ft X2 = ft X1 ) ( inn : T_dom X1 X2 ) :
  ft ( T X1 X2 inn ) = X1 .
Proof.
  intros .
  assert ( isov := ax1b X1 X2 inn : isover (T X1 X2 inn) X1  ) .
  unfold isover in isov . rewrite ax0 in isov .  rewrite ( natassocpmeq _ _ _ ( T_dom_geh inn ) )
                                                         in isov . 
  assert ( eq : ll X2 = ll X1 ) .
  assert ( eq' : ll X2 - 1 = ll X1 - 1 ) . repeat rewrite <- ll_ft .  rewrite iseq .
  apply idpath .

  assert ( eq1 : ( ll X1 - 1 ) + 1 = ll X1 ) . refine ( minusplusnmm _ _ _ ) .
  exact ( natgthtogehsn _ _ (T_dom_gt0 inn ) ) .

  assert ( eq2 : ( ll X2 - 1 ) + 1 = ll X2 ) . refine ( minusplusnmm _ _ _ ) .
  exact ( istransnatgeh _ _ _ ( T_dom_geh inn ) ( natgthtogehsn _ _ (T_dom_gt0 inn ) ) ) .

  assert ( eq'' := maponpaths ( fun n => n + 1 ) eq' ) . 
  lazy beta in eq'' . 
  rewrite eq1 in eq'' . rewrite eq2 in eq'' . exact eq'' .

  rewrite eq in isov . 
  rewrite natminusnn in isov . 
  exact ( ! isov ) . 

Defined.





(** The isover and isabove properties of the expressions T X1 X2 *)



Lemma isover_T_T_2 { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 :  T_ax0_type T ) ( ax1a : T_ax1a_type T )
      { X1 X2 X2' : BB } ( inn : T_dom X1 X2 ) ( inn' : T_dom X1 X2' )
      ( is : isover X2 X2' ) : isover ( T X1 X2 inn ) ( T X1 X2' inn' ) .
Proof .
  intros . 
  unfold isover in * .
  repeat rewrite ax0 .
  simpl .
  assert ( isab : isabove ( ftn ( ll X2 - ll X2') X2 ) ( ft X1 ) ) .
  rewrite <- is . 
  exact ( T_dom_isabove inn' ) . 

  rewrite ( ftn_T ax1a _ isab inn ) .
  exact ( T_equals_2 _ is _ _ ) . 

Defined.


Lemma isabove_T_T_2 { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( ax0 :  T_ax0_type T ) ( ax1a : T_ax1a_type T )
      { X1 X2 X2' : BB } ( inn : T_dom X1 X2 ) ( inn' : T_dom X1 X2' )
      ( is : isabove X2 X2' ) : isabove ( T X1 X2 inn ) ( T X1 X2' inn' ) .
Proof .
  intros .
  refine ( isabove_constr _ _ ) .
  repeat rewrite ax0 . 
  exact ( isabove_gth is ) . 

  exact ( isover_T_T_2 ax0 ax1a _ _ is ) . 
  
Defined.









  
  
(** Two implications of the zeros and first properties of operations of type T 
that are required for the formulation of the property TT *) 


Lemma T_dom_12_23_to_T12_T13 { BB : lBsystem_carrier } { T : T_ops_type BB }
      ( ax0 :  T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T )
           { X1 X2 X3 : BB } ( inn12 : T_dom X1 X2 ) ( inn23 : T_dom X2 X3 ) :
  T_dom ( T X1 X2 inn12 ) ( T X1 X3 ( T_dom_comp inn12 inn23 ) ) .
Proof . 
  intros . 
  assert ( is21 := T_dom_isabove inn12 ) .
  assert ( is32 := T_dom_isabove inn23 ) .
  refine ( T_dom_constr _ _ ) .
  rewrite ( ax0 _ _ inn12 ) .  exact ( natgthsn0 _ ) .
  
  destruct ( isabove_choice is21 ) as [ isab | eq ] .

  rewrite ( ax1a _ _ _ isab ) . 
  exact ( isabove_T_T_2 ax0 ax1a _ _ is32) .

  rewrite ( ft_T ax0 ax1b ( ! eq ) _ ) .
  apply ax1b . 

Defined.

 

Lemma T_dom_12_23_to_T1T23 { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( ax1b : T_ax1b_type T ) 
           { X1 X2 X3 : BB } ( inn12 : T_dom X1 X2 ) ( inn23 : T_dom X2 X3 ) :
  T_dom X1 ( T X2 X3 inn23 ) .
Proof .
  intros .
  refine ( T_dom_constr _ _ ) . 
  exact ( T_dom_gt0 inn12 ) . 

  refine ( isabov_trans ( ax1b _ _ _ ) _ ) . 
  exact ( T_dom_isabove inn12 ) .

Defined.






(** Property TT *)

Definition TT_type { BB : lBsystem_carrier } ( T : T_ops_type BB )
           ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T ) :=
  forall ( X1 X2 X3 : BB ) ( inn12 : T_dom X1 X2 ) ( inn23 : T_dom X2 X3 ) ,
    T ( T X1 X2 inn12 ) ( T X1 X3 ( T_dom_comp inn12 inn23 ) )
      ( T_dom_12_23_to_T12_T13 ax0 ax1a ax1b inn12 inn23 ) =
    T X1 ( T X2 X3 inn23 ) ( T_dom_12_23_to_T1T23 ax1b inn12 inn23 ) . 




  
(** **** Operation(s) Tt .

Including constructions related to their domains of definition. *)

(** Domains of definition of operations of type Tt *)


Definition Tt_dom { BB : lBsystem_carrier } ( X : BB ) ( s : Tilde BB ) := T_dom X ( dd s ) .



(** The type objects of which are candidates for operations Tt on an lB-system. *)
 
              
Definition Tt_ops_type ( BB : lBsystem_carrier ) :=
  forall ( X : BB ) ( s : Tilde BB ) ( inn : Tt_dom X s ) , Tilde BB .


(** The zeros property (later an axiom) of an operation of type Tt 
is not needed because it is a corollary of the first property of Tt and the
zeros property of T. *


Definition Tt_ax0_type { BB : lBsystem_carrier } ( Tt : Tt_ops_type BB ) :=
  forall ( X : BB ) ( s : Tilde BB ) ( inn : Tt_dom X s ) ,
    ll ( dd ( Tt X s inn ) ) = 1 + ll ( dd s ) .

*)



(** The first property (later an axiom) of an operation of type Tt *)


Definition Tt_ax1_type { BB : lBsystem_carrier } ( T : T_ops_type BB ) ( Tt : Tt_ops_type BB ) :=
  forall ( X : BB ) ( s : Tilde BB ) ( inn : Tt_dom X s ) ,
    dd ( Tt X s inn ) = T X ( dd s ) inn .


(** Two implications of the zeros and first properties of operations of type T and Tt
that are required for the formulation of the property TT *) 

Lemma Tt_dom_12_2r_to_T12_Tt1r { BB : lBsystem_carrier } ( T : T_ops_type BB )
      ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T )
           ( Tt : Tt_ops_type BB ) ( ax1at : Tt_ax1_type T Tt )
           { X1 X2 : BB } { r : Tilde BB } ( inn12 : T_dom X1 X2 ) ( inn2r : Tt_dom X2 r ) :
  Tt_dom ( T X1 X2 inn12 ) ( Tt X1 r ( T_dom_comp inn12 inn2r ) ) .
Proof.
  intros . 
  unfold Tt_dom .
  rewrite ax1at . 
  apply ( T_dom_12_23_to_T12_T13 ax0 ax1a ax1b inn12 inn2r ) . 
Defined.


Lemma Tt_dom_12_2r_to_Tt1Tt2r { BB : lBsystem_carrier } ( T : T_ops_type BB )
      ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
      ( Tt : Tt_ops_type BB ) ( ax1at : Tt_ax1_type T Tt )
      { X1 X2 : BB } { r : Tilde BB } ( inn12 : T_dom X1 X2 ) ( inn2r : Tt_dom X2 r ) :
  Tt_dom X1 ( Tt X2 r inn2r ) .
Proof.
  intros.
  unfold Tt_dom.
  rewrite ax1at . 
  apply ( T_dom_12_23_to_T1T23 ax1b inn12 inn2r ) .
Defined.





  
(** Property TTt *)

Definition TTt_type { BB : lBsystem_carrier } ( T : T_ops_type BB )
           ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T )
           ( Tt : Tt_ops_type BB ) ( ax1at : Tt_ax1_type T Tt ) :=
  forall ( X1 X2 : BB ) ( r : Tilde BB ) ( inn12 : T_dom X1 X2 ) ( inn2r : Tt_dom X2 r ) ,
    Tt ( T X1 X2 inn12 ) ( Tt X1 r ( T_dom_comp inn12 inn2r ) )
      ( Tt_dom_12_2r_to_T12_Tt1r T ax0 ax1a ax1b Tt ax1at inn12 inn2r ) =
    Tt X1 ( Tt X2 r inn2r ) ( Tt_dom_12_2r_to_Tt1Tt2r T ax0 ax1b Tt ax1at inn12 inn2r ) . 















(* **** Operation(s) S  

Note: both the domain of definition of operations S and the type of the axiom 1a of operations 
S are obtainable from the same for operations T by removing the condition T_dom_gt0 and 
replacing ( ft X1 ) by ( dd r ). This leads to the possibility of almost direct copy-and_paste
of many proofs concerning T into the context of S. 

Operations T and S are different in the forms of axiom 0 and axiom 1b . 

*)

(** Domains of definition of operations of type S *)


Definition S_dom { BB : lBsystem_carrier } ( r : Tilde BB ) ( Y : BB ) :=
  isabove Y ( dd r ) .

Definition S_dom_gth { BB : lBsystem_carrier } { r : Tilde BB } { Y : BB } ( inn : S_dom r Y ) :
  ll Y > 0 .
Proof .
  intros .  exact ( istransnatgth _ _ _ ( isabove_gth inn ) ( ll_dd _ ) )  . 

Defined.

Definition S_dom_geh { BB : lBsystem_carrier } { r : Tilde BB } { Y : BB } ( inn : S_dom r Y ) :
  ll Y >= 1 .
Proof .
  intros .  exact ( natgthtogehsn _ _ ( S_dom_gth inn ) ) . 

Defined.


Lemma isaprop_S_dom { BB : lBsystem_carrier } ( r : Tilde BB ) ( Y : BB ) :
  isaprop ( S_dom r Y ) . 
Proof.
  intros . apply isaprop_isabove . 
Defined.


Lemma noparts_S_dom { BB : lBsystem_carrier } { r : Tilde BB } { Y : BB }
      ( inn1 inn2 : S_dom r Y ) : inn1 = inn2 .
Proof .
  intros . apply ( proofirrelevance _ ( isaprop_S_dom r Y ) ) .
Defined .  


(** The type objects of which are candidates for operations S on an lB-system. *)
 

Definition S_ops_type ( BB : lBsystem_carrier ) :=
  forall ( r : Tilde BB ) ( Y : BB ) ( inn : S_dom r Y ) , BB .

Lemma S_equals_2 { BB : lBsystem_carrier } { r : Tilde BB } { Y Y' : BB } ( S : S_ops_type BB )
      ( eq : Y = Y' ) ( inn : S_dom r Y ) ( inn' : S_dom r Y' )  :
  S r Y inn = S r Y' inn' .
Proof.
  intros BB r Y Y' S eq .
  rewrite eq . 
  intros . rewrite ( noparts_S_dom inn inn' ) . 
  apply idpath . 

Defined.



(** The zeros property (later an axiom) of an operation of type S *)

Definition S_ax0_type { BB : lBsystem_carrier } ( S : S_ops_type BB ) :=
  forall ( r : Tilde BB ) ( Y : BB ) ( inn : S_dom r Y ) , ( ll ( S r Y inn ) ) = ( ll Y ) - 1 .

(** The first property (later an axiom) of an operation of type S *)

Definition S_ax1a_type { BB : lBsystem_carrier } ( S : S_ops_type BB ) :=
  forall ( r : Tilde BB ) ( Y : BB ) ( inn : S_dom r Y ) ( isab : isabove ( ft Y ) ( dd r ) ) ,
    ft ( S r Y inn ) = S r ( ft Y ) isab . 

Definition S_ax1b_type { BB : lBsystem_carrier } ( S : S_ops_type BB ) :=
  forall ( r : Tilde BB ) ( Y : BB ) ( inn : S_dom r Y ) ,
    isabove ( S r Y inn ) ( ft ( dd r ) ) .




(** The computation of the iterated ft of ( S r Y ) .  *)
          
Lemma ftn_S { BB : lBsystem_carrier } { S : S_ops_type BB } ( ax1a : S_ax1a_type S )
      ( n : nat ) { r : Tilde BB } { Y : BB } ( isab : isabove ( ftn n Y ) ( dd r ) )
      ( inn : S_dom r Y ) :
  ftn n ( S r Y inn ) = S r ( ftn n Y ) isab .
Proof .
  intros BB S ax1a n . induction n as [ | n IHn ] .
  intros .
  rewrite ( noparts_S_dom inn isab ) . 
  apply idpath . 

  intros .
  change ( ftn (Datatypes.S n) (S r Y inn) ) with ( ft ( ftn n (S r Y inn) ) ) .
  assert ( isab' : isabove ( ftn n Y ) ( dd r ) ) .
  exact ( isabove_ft_inv isab ) . 
  
  rewrite ( IHn r Y isab' inn ) . 
  refine ( ax1a _ _ _ _ ) . 

Defined.

Lemma ft_S { BB : lBsystem_carrier } { S : S_ops_type BB } { r : Tilde BB } { Y : BB }
      ( ax0 : S_ax0_type S ) ( ax1b : S_ax1b_type S ) ( iseq : ft Y = dd r )
      ( inn : S_dom r Y ) : ft ( S r Y inn ) = ft ( dd r ) .
Proof.
  intros .
  assert ( isov := ax1b r Y inn : isover ( S r Y inn ) ( ft ( dd r ) ) ) .
  unfold isover in isov . 
  rewrite ll_ft in isov .  rewrite ax0 in isov . rewrite <- ll_ft  in isov .
  rewrite iseq in isov . 
  assert ( int : (ll (dd r) - (ll (dd r) - 1)) = 1 ) . refine ( natminusmmk _ ) .
  exact ( natgthtogehsn _ _ ( ll_dd _ ) ) .

  rewrite int in isov . 
  exact ( ! isov ) . 

Defined.

Lemma isover_S_S_2 { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 :  S_ax0_type S ) ( ax1a : S_ax1a_type S )
      { r : Tilde BB } { Y Y' : BB } ( inn : S_dom r Y ) ( inn' : S_dom r Y' )
      ( is : isover Y Y' ) : isover ( S r Y inn ) ( S r Y' inn' ) .
Proof .
  intros . 
  unfold isover in * .
  repeat rewrite ax0 .
  simpl .
  assert ( isab : isabove ( ftn ( ll Y - ll Y') Y ) ( dd r ) ) .
  rewrite <- is . 
  exact inn' . 

  rewrite ( natmiusmius1mminus1 ( S_dom_gth inn ) ( S_dom_gth inn' ) ) . 
  rewrite ( ftn_S ax1a _ isab inn ) .
  exact ( S_equals_2 _ is _ _ ) . 

Defined.


Lemma isabove_S_S_2 { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 :  S_ax0_type S ) ( ax1a : S_ax1a_type S )
      { r : Tilde BB } { Y Y' : BB } ( inn : S_dom r Y ) ( inn' : S_dom r Y' )
      ( is : isabove Y Y' ) : isabove ( S r Y inn ) ( S r Y' inn' ) .
Proof .
  intros .
  refine ( isabove_constr _ _ ) .
  repeat rewrite ax0 .
  refine ( natgthandminusinvr _ _ ) .
  exact ( isabove_gth is ) .

  exact ( S_dom_geh inn' ) . 

  exact ( isover_S_S_2 ax0 ax1a _ _ is ) . 

Defined.


  













(** **** Operation(s) St  *)


(** Domains of definition of operations of type St *)


Definition St_dom { BB : lBsystem_carrier } ( r : Tilde BB ) ( s : Tilde BB ) :=
  S_dom r ( dd s ) . 


(** The type objects of which are candidates for operations St on an lB-system. *)
 

Definition St_ops_type ( BB : lBsystem_carrier ) :=
  forall ( r : Tilde BB ) ( s : Tilde BB ) ( inn : St_dom r s ) , Tilde BB .


(** The first property (later an axiom) of an operation of type St *)


Definition St_ax1_type { BB : lBsystem_carrier } ( S : S_ops_type BB )
           ( St : St_ops_type BB ) := 
  forall ( r : Tilde BB ) ( s : Tilde BB ) ( inn : St_dom r s ) ,
    ft ( dd ( St r s inn ) ) = S r ( dd s ) inn .




(** Two implications of the zeros and first properties of operations of type S and St
that are required for the formulation of the properties SS and SSt *) 

























(** *** Non-unital pre-l-Bsystems, definition. *)



Definition nu_pre_lBsystem :=
  total2 ( fun BB : lBsystem_carrier =>
             dirprod ( dirprod ( T_ops_type BB ) ( Tt_ops_type BB ) )
                     ( dirprod ( S_ops_type BB ) ( St_ops_type BB ) ) ) .


Definition nu_pre_lBsystem_to_lBsystem_carrier : nu_pre_lBsystem -> lBsystem_carrier := pr1 .
Coercion nu_pre_lBsystem_to_lBsystem_carrier : nu_pre_lBsystem >-> lBsystem_carrier .


Definition T { BB : nu_pre_lBsystem } { X1 X2 : BB } ( inn : T_dom X1 X2 ) :
  BB := ( pr1 ( pr1 ( pr2 BB ) ) ) X1 X2 inn .

Definition Tt { BB : nu_pre_lBsystem } { X : BB } { s : Tilde BB } ( inn : Tt_dom X s ) :
  Tilde BB := ( pr2 ( pr1 ( pr2 BB ) ) ) X s inn .

Definition Si { BB : nu_pre_lBsystem } { r : Tilde BB } { Y : BB } ( inn : S_dom r Y ) :
  BB := ( pr1 ( pr2 ( pr2 BB ) ) ) r Y inn .
    
Definition Sti { BB : nu_pre_lBsystem } { r : Tilde BB } { s : Tilde BB } ( inn : St_dom r s ) :
  Tilde BB := ( pr2 ( pr2 ( pr2 BB ) ) ) r s inn .







(* ** Non-unital l-B0-systems. *) 









(* End of the file lBsystems.v *)


