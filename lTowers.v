(** * Presentation of towers through the length function

by Vladimir Voevodsky, started on Jan. 22, 2015, most material migrated from 
lBsystems_carriers.v 

*)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_prelim.


(** To uu0a.v *)

Lemma iscontrpathsfrom { T : UU } ( A : T ) :
  iscontr ( total2 ( fun X : T => A = X ) ) .
Proof .
  intros .
  split with ( tpair _ A ( idpath A ) ) . 
  intro t . 
  destruct t as [ t e ] .
  destruct e . 
  apply idpath . 

Defined.





  

(** We formalize the sequences of types ...->B_{n+1}->B_n->...->B_0

as one type B with a length function ll and an endomorphism ft. *)


Definition ltower_str_data ( T : UU ) :=  dirprod ( T -> nat ) ( T -> T ) .

Definition ltower_str ( T : UU ) :=
  total2 ( fun str :ltower_str_data T =>
             dirprod 
               ( forall X : T , ( pr1 str ) ( pr2 str X ) = pr1 str X - 1 )
               ( forall ( X : T ) ( e : pr1 str X = 0 ) , pr2 str X = X ) ) .


Definition ltower := total2 ( fun T : UU => ltower_str T ) .

Definition ltower_constr { T : UU } ( ll : T -> nat ) ( ft : T -> T )
           ( ll_ft_eq : forall X : T , ll ( ft X ) = ll X - 1 )
           ( ll0_eq : forall ( X : T ) ( e : ll X = 0 ) , ft X = X ) : ltower .
Proof .
  intros .
  split with T .
  
  split with ( dirprodpair ll ft ) .

  exact ( dirprodpair ll_ft_eq ll0_eq ) . 

Defined.









  
(** The type ltower is constructively equivalent to the type of pretowers defined as follows:

Definition pretowerfam := ( fun T : nat -> UU => forall n : nat , T ( S n  ) -> T n ) .
Definition pretower := total2 pretowerfam . 

See pretowers.v 

*)

Definition ltower_data_pr1 : ltower -> UU := pr1 .
Coercion ltower_data_pr1 : ltower >-> UU .

Definition ll { X : ltower } : X -> nat := pr1 ( pr1 ( pr2 X ) ) . 

Definition ft { X : ltower } : X -> X := pr2 ( pr1 ( pr2 X ) ) .

Definition ftn { X : ltower } ( n : nat ) : X -> X := iteration ( @ft X ) n . 


Definition ll_ft { T : ltower } ( X : T ) : ll ( ft X ) = ll X - 1 :=
  pr1 ( pr2 ( pr2 T ) ) X .

Definition ftX_eq_X { T : ltower } { X : T } ( e : ll X = 0 ) : ft X = X :=
  pr2 ( pr2 ( pr2 T ) ) X e . 


(** Some useful lemmas about ltower *)

Lemma ll_ftn { BB : ltower } ( n : nat ) ( X : BB ) : ll ( ftn n X ) = ll X - n . 
Proof.
  intros BB n .
  induction n as [ | n IHn ] .
  intro . rewrite natminuseqn . apply idpath . 
  intro . change ( ftn ( S n ) X ) with ( ft ( ftn n X ) ) .  rewrite ( ll_ft _ ) . 
  rewrite ( IHn X ) .  rewrite ( natminusassoc _ _ _ ) .  rewrite ( natpluscomm n 1 ) . 
  apply idpath .
Defined .

  
Lemma ftn_ft { BB : ltower } ( n : nat ) ( X : BB ) :
  ftn n ( ft X ) = ftn ( 1 + n ) X .
Proof .
  intros . induction n as [ | n IHn ] .
  apply idpath . 
  apply ( maponpaths ( @ft BB ) IHn ) . 
Defined.

Lemma ftn_ftn { BB : ltower } ( m n : nat ) ( X : BB ) :
  ftn m ( ftn n X ) = ftn ( m + n ) X .
Proof.
  intros .  induction m as [ | m IHm ] . 
  exact ( idpath _ ) .
  apply ( maponpaths ft ) . 
  exact IHm .
Defined.


Lemma lltowergehll { BB : ltower } { X1 X2 : BB } ( gt : ll X2 > ll X1 ) :
  ll ( ft X2 ) >= ll X1 .
Proof.
  intros. rewrite ( ll_ft X2 ) . apply ( natgthtominus1geh gt ) . 
Defined .

Lemma llgehll { BB : ltower } { X1 X2 : BB } ( gt : ll X2 > ll ( ft X1 ) ) :
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


Definition isover { BB : ltower } ( X A : BB ) := ( A = ftn ( ll X - ll A ) X ) .


Lemma isover_geh { BB : ltower } { X A : BB } ( is : isover X A ) :
  ll X >= ll A .
Proof.
  intros . unfold isover in is . 
  assert ( int : ll A = ll ( ftn (ll X - ll A) X ) ) . exact ( maponpaths ll is ) .

  rewrite int . rewrite ll_ftn . exact ( natminuslehn _ _ ) .
  
Defined.

Lemma isover_XX { BB : ltower } ( X : BB ) : isover X X .
Proof.
  intros . unfold isover . rewrite natminusnn . apply idpath . 

Defined.

Lemma isover_trans { BB : ltower } { X A A' : BB } :
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

Lemma isover_X_ftX { BB : ltower } ( X : BB ) : isover X ( ft X ) .
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

Lemma isover_X_ftnX { BB : ltower } ( X : BB ) ( n : nat ) : isover X ( ftn n X ) .
Proof .
  intros . 
  induction n as [ | n IHn ] . 
  exact ( isover_XX _ ) . 

  exact ( isover_trans IHn ( isover_X_ftX _ ) ) . 

Defined.



  
Lemma isover_X_ftA { BB : ltower } { X A : BB }
      ( is : isover X A ) : isover X ( ft A ) .
Proof.
  intros. exact ( isover_trans is ( isover_X_ftX _ ) ) . 

Defined.



Lemma isover_ft { BB : ltower } { X A : BB }
      ( is : isover X A ) ( gt : ll X > ll A ) : isover ( ft X ) A .
Proof.
  intros. unfold isover in * . 
  rewrite ftn_ft . rewrite ll_ft . rewrite <- lB_2014_12_07_l1 .
  exact is .

  exact gt .

Defined.

Lemma isover_ftn { BB : ltower } { n : nat } { X A : BB } 
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


Lemma isover_choice { BB : ltower } { X A : BB }
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


Definition isabove { BB : ltower } ( X A : BB ) :=
  dirprod ( ll X > ll A ) ( isover X A ) .

Definition isabove_constr { BB : ltower } { X A : BB }
           ( gt : ll X > ll A ) ( isov : isover X A ) : isabove X A :=
  tpair _ gt isov . 

Definition isabove_gth { BB : ltower } { X A : BB } ( is : isabove X A ) :
  ll X > ll A := pr1 is .

Lemma isabove_gt0 { BB : ltower } { X A : BB } ( is : isabove X A ) : ll X > 0 .
Proof .
  intros .
  exact ( natgthgehtrans _ _ _ ( isabove_gth is ) ( natgehn0 _ ) ) .

Defined.

  
Definition isabove_to_isover { BB : ltower } { X A : BB } :
  isabove X A -> isover X A := pr2 .
Coercion isabove_to_isover : isabove >-> isover .

Lemma isabove_X_ftX { BB : ltower } ( X : BB ) ( gt0 : ll X > 0 ) : isabove X ( ft X ) .
Proof .
  intros .
  refine ( isabove_constr _ _ ) .
  rewrite ll_ft . 
  exact ( natgthnnmius1 gt0 ) . 

  exact ( isover_X_ftX _ ) . 

Defined.

  
Lemma isabove_X_ftA { BB : ltower } { X A : BB }
      ( is : isabove X A ) : isabove X ( ft A ) .
Proof .
  intros . refine ( isabove_constr _ _ ) .
  rewrite ll_ft . 
  exact ( natgthgehtrans _ _ _ ( isabove_gth is ) ( natminuslehn _ 1 ) ) . 

  exact (isover_X_ftA is ) .

Defined.


Lemma isabove_X_ftA' { BB : ltower } { X A : BB }
      ( is : isover X A ) ( gt0 : ll A > 0 ) : isabove X ( ft A ) .
Proof .
  intros . refine ( isabove_constr _ _ ) .
  rewrite ll_ft .
  refine ( natgehgthtrans _ _ _ ( isover_geh is ) _ ) .
  exact ( natgthnnmius1 gt0 ) . 

  exact ( isover_X_ftA is ) . 

Defined.



Lemma isabove_trans { BB : ltower } { X A A' : BB } :
  isabove X A -> isabove A A' -> isabove X A' .
Proof.
  intros BB X A A' is is' . refine ( isabove_constr _ _ ) .
  exact ( istransnatgth _ _ _ ( isabove_gth is ) ( isabove_gth is' ) ) .

  exact ( isover_trans is is' ) .

Defined.

Lemma isabov_trans { BB : ltower } { X A A' : BB } :
  isabove X A -> isover A A' -> isabove X A' .
Proof.
  intros BB X A A' is is' . refine ( isabove_constr _ _ ) .
  exact ( natgthgehtrans _ _ _ ( isabove_gth is ) ( isover_geh is' ) ) .

  exact ( isover_trans is is' ) .

Defined.

Lemma isovab_trans { BB : ltower } { X A A' : BB } :
  isover X A -> isabove A A' -> isabove X A' .
Proof.
  intros BB X A A' is is' . refine ( isabove_constr _ _ ) .
  exact ( natgehgthtrans _ _ _ ( isover_geh is ) ( isabove_gth is' ) ) .

  exact ( isover_trans is is' ) .

Defined.


Lemma isover_ft' { BB : ltower } { X A : BB } ( is : isabove X A ) :
  isover ( ft X ) A .
Proof .
  intros . exact ( isover_ft is ( isabove_gth is ) ) . 

Defined.

Lemma isabove_ft_inv { BB : ltower } { X A : BB } ( is : isabove ( ft X ) A ) :
  isabove X A .
Proof .
  intros . exact ( isovab_trans ( isover_X_ftX _ ) is ) .  

Defined.


Lemma ovab_choice { BB : ltower } { X A : BB } ( isov : isover X A ) :
  coprod ( isabove X A ) ( X = A ) .
Proof .
  intros .
  destruct ( natgehchoice _ _ ( isover_geh isov ) ) as [ gth | eq ] . 
  exact ( ii1 ( tpair _ gth isov ) ) .

  unfold isover in isov . 
  rewrite eq in isov . 
  rewrite natminusnn in isov . 
  exact ( ii2 ( ! isov ) ) . 

Defined.

  
Lemma isabove_choice { BB : ltower } { X A : BB } ( isab : isabove X A ) :
  coprod ( isabove ( ft X ) A ) ( A = ft X ) . 
Proof.
  intros .
  assert ( isov := isover_ft' isab ) . 
  assert ( gte : ll ( ft X ) >= ll A ) .
  exact ( lltowergehll ( isabove_gth isab ) ) .

  destruct ( natgehchoice _ _ gte ) as [ gt | eq ] .
  exact ( ii1 ( isabove_constr gt isov ) ) . 

  unfold isover in isov . 
  rewrite eq in isov . 
  rewrite natminusnn in isov . 
  exact ( ii2 isov ) . 

Defined.

Lemma isabove_choice_n { BB : ltower } ( n : nat ) { X A : BB } ( isab : isabove X A ) :
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



  



(** Pointed ltowers 

These are ltowers such that the zero's floor is contractible *)

Definition ispointed ( T : ltower ) :=
  iscontr ( total2 ( fun X : T => ll X = 0 ) ) . 

Lemma isoverll0 { T : ltower } ( is : ispointed T )
      { X1 : T } ( eq0 : ll X1 = 0 )
      ( X2 : T ) : isover X2 X1 .
Proof .
  intros . 
  unfold isover . 
  assert ( eq0' : ll ( ftn ( ll X2 - ll X1 ) X2 ) = 0 ) . 
  rewrite ll_ftn . 
  rewrite eq0 . rewrite natminuseqn.
  exact ( natminusnn _ ) . 

  assert ( eq : tpair ( fun X : T => ll X = 0 ) _ eq0 = tpair ( fun X : T => ll X = 0 ) _ eq0' ) .
  exact ( proofirrelevancecontr is _ _ ) .

  exact ( maponpaths ( @pr1 _ ( fun X : T => ll X = 0 ) ) eq ) . 

Defined.



(** ltowers of objects over an object *)


Definition ltower_over_carrier { T : ltower } ( A : T ) :=
  total2 ( fun X : T => isover X A ) .

Definition obj_over_constr { T : ltower } { A : T } { X : T } ( isov : isover X A ) :
  ltower_over_carrier A := tpair ( fun X : T => isover X A ) _ isov .

Definition isov_isov { T : ltower } { A : T } ( X : ltower_over_carrier A ) :
  isover ( pr1 X ) A := pr2 X . 

Definition ltower_over_ll { T : ltower } { A : T } ( X : ltower_over_carrier A ) : nat :=
  ll ( pr1 X ) - ll A .
      
Definition ltower_over_ft { T : ltower } { A : T } ( X : ltower_over_carrier A ) :
  ltower_over_carrier A .
Proof .
  intros .
  destruct ( isover_choice ( isov_isov X ) ) as [ isov | eq ] .
  exact ( tpair _ ( ft ( pr1 X ) )  isov ) .

  exact ( tpair ( fun X : T => isover X A ) A ( isover_XX A ) ) . 

Defined.

Lemma ltower_over_ll_ft_eq { T : ltower } { A : T } ( X : ltower_over_carrier A ) :
  ltower_over_ll ( ltower_over_ft X ) = ltower_over_ll X - 1 .
Proof .
  intros . 
  unfold ltower_over_ft . 
  destruct ( isover_choice ( isov_isov X ) ) as [ isov | eq ] .
  unfold ltower_over_ll .  
  simpl .
  rewrite ll_ft . 
  rewrite natminusassoc . 
  rewrite natpluscomm . 
  rewrite <- natminusassoc . 
  apply idpath . 

  unfold ltower_over_ll .
  simpl . 
  rewrite natminusnn . 
  rewrite <- eq . 
  rewrite natminusnn .
  apply idpath . 

Defined.


Lemma ispointed_ltower_over_int { T : ltower } ( A : T ) :
  iscontr ( total2 ( fun X : ltower_over_carrier A =>
                       ltower_over_ll X = 0 ) ) .
Proof.
  intros .
  assert ( weq1 : weq ( total2 ( fun X : ltower_over_carrier A =>
                                   ltower_over_ll X = 0 ) )
                      ( total2 ( fun X : T => dirprod
                                                ( isover X A ) ( ll X - ll A = 0 ) ) ) ) .
  apply weqtotal2asstor . 

  assert ( weq2 : weq ( total2 ( fun X : T => dirprod
                                                ( isover X A ) ( ll X - ll A = 0 ) ) )
                      ( total2 ( fun X : T => A = X ) ) ) .
  refine ( weqfibtototal _ _ _ ) . 
  intro X . 
  assert ( weq3 : weq (dirprod (isover X A) (ll X - ll A = 0))
                      (dirprod (ll X - ll A = 0) (isover X A)) ) .
  apply weqdirprodcomm . 

  assert ( weq4 : weq (dirprod (ll X - ll A = 0) (isover X A))
                      (dirprod (ll X - ll A = 0) ( A = X ) ) ) .
  refine ( weqfibtototal _ _ _ ) . 
  intro eq . 
  unfold isover . 
  rewrite eq . 
  apply idweq.

  assert ( weq5 : weq (dirprod (ll X - ll A = 0) (A = X))
                      (dirprod (A = X)(ll X - ll A = 0))).
  apply weqdirprodcomm . 

  assert ( weq6 : weq (dirprod (A = X) (ll X - ll A = 0))
                      ( A = X ) ) .
  apply weqpr1 . 
  intro eq . 
  rewrite eq . 
  rewrite natminusnn . 
  apply iscontraprop1 . 
  apply isasetnat . 

  apply idpath . 

  apply ( weqcomp weq3 ( weqcomp weq4 ( weqcomp weq5 weq6 ) ) ) .  

  assert ( weq := weqcomp weq1 weq2 ) . 
  apply ( iscontrweqb weq ) .

  apply iscontrpathsfrom .

Defined.

  

         


Lemma ltower_over_ll0_eq { T : ltower } { A : T }
      ( X : ltower_over_carrier A ) ( eq0 : ltower_over_ll X = 0 ) : 
  ltower_over_ft X = X .
Proof .
  intros .
  assert ( eq0' : ltower_over_ll ( ltower_over_ft X ) = 0 ) . 
  rewrite ltower_over_ll_ft_eq . 
  rewrite eq0 . 
  apply idpath .

  assert ( int : tpair ( fun X' => ltower_over_ll X' = 0 ) _ eq0' =
                 tpair ( fun X' => ltower_over_ll X' = 0 ) X eq0 ) .
  apply ( proofirrelevancecontr ( ispointed_ltower_over_int _ ) _ _ ) .

  apply ( maponpaths ( @pr1 _ ( fun X' => ltower_over_ll X' = 0 ) ) int ) .

Defined.


  

Definition ltower_over { T : ltower } ( A : T ) : ltower :=
  ltower_constr ( @ltower_over_ll _ A ) ( @ltower_over_ft _ A )
                ( @ltower_over_ll_ft_eq _ A ) ( @ltower_over_ll0_eq _ A ) .

(** The name of the following function comes from the word octothrope that is the official name for the 
"pound sign". This symbol, as a subscript, is used sometimes to denote the left adjoint to the pull-back 
functor that takes a presheaf represneted by p : X -> B over B to the presheaf represented by X. *)

Definition pocto { T : ltower } { A : T } ( X : ltower_over A ) : T := pr1 X . 
(* Coercion ltower_over_carrier_pr1 : ltower_over_carrier >-> ltower_data_pr1 . *)


Lemma ll_over_minus_ll_over { T : ltower } { A : T } ( X1 X2 : ltower_over A ) :
  ll X1 - ll X2 = ll ( pr1 X1 ) - ll ( pr1 X2 ) .
Proof .
  intros .
  destruct X1 as [ X1 isov1 ] . destruct X2 as [ X2 isov2 ] . 
  unfold ll . 
  simpl . 
  unfold ltower_over_ll . 
  change _ with ( ( ll X1 - ll A ) - ( ll X2 - ll A ) = ( ll X1 - ll X2 ) ) . 
  rewrite natminusassoc . 
  rewrite natpluscomm . 
  rewrite ( minusplusnmm _ _ ( isover_geh isov2 ) ) . 
  apply idpath . 

Defined.

Lemma ltower_over_ftn { T : ltower } { A : T } ( n : nat )
      ( X : ltower_over A ) ( ge : ll X >= n ) : pr1 ( ftn n X ) = ftn n ( pr1 X ) .
Proof .
  intros T A n . 
  induction n .
  intros . 
  apply idpath . 

  intros. 
  rewrite <- ftn_ft . 
  rewrite <- ftn_ft . 
  assert ( int : ft ( pr1 X ) = pr1 ( ft X ) ) . 
  change ( ft X ) with ( ltower_over_ft X ) . 
  unfold ltower_over_ft . 
  destruct ( isover_choice (isov_isov X) ) as [ isov | eq ] . 
  simpl . 
  apply idpath . 

  assert ( absd : empty ) . 
  change ( ll X ) with ( ll ( pr1 X ) - ll A ) in ge .
  rewrite <- eq in ge . 
  rewrite natminusnn in ge . 
  apply ( ge ( natgthsn0 _ ) ) . 

  destruct absd .
  rewrite int . 
  refine ( IHn ( ft X ) _ ) . 
  rewrite ll_ft . 

  assert ( ge' := natgehandminusr _ _ 1 ge ) . 
  change ( S n - 1 ) with ( n - 0 ) in ge' .
  rewrite natminuseqn in ge' . 
  exact ge' . 

Defined.



(** Monotone functions between l-towers *)


Definition isovmonot { T1 T2 : ltower } ( f : T1 -> T2 ) :=
  forall ( X Y : T1 ) , isover X Y -> isover ( f X ) ( f Y ) . 

Definition monotone_fun ( T1 T2 : ltower ) :=
  total2 ( fun f : T1 -> T2 => isovmonot f ) . 

Definition monotone_fun_constr { T1 T2 : ltower }
           ( f : T1 -> T2 ) ( is : forall ( X Y : T1 ) , isover X Y -> isover ( f X ) ( f Y ) ) :
  monotone_fun T1 T2 := tpair _ f is .


Definition monotone_fun_pr1 ( T1 T2 : ltower ) : monotone_fun T1 T2 -> ( T1 -> T2 ) := pr1 . 
Coercion monotone_fun_pr1 : monotone_fun >-> Funclass .



(** The projection pocto from the over-tower to the tower is over-monotone *)


Definition isovmonot_pocto { T : ltower } ( A : T ) { X Y : ltower_over A } ( isov : isover X Y ) :
isover ( pocto X ) ( pocto Y ) .  
Proof .
  intros . 
  destruct X as [ X isovX ] .
  destruct Y as [ Y isovY ] .
  simpl . 
  assert ( int := maponpaths pr1 isov ) . 
  simpl in int .
  rewrite ltower_over_ftn in int . 
  simpl in int . 
  rewrite ll_over_minus_ll_over in int . 
  simpl in int . 
  exact int . 

  exact ( natminuslehn _ _ ) . 

Defined.


(** Composition of monotone functions is monotone *)

Definition isovmonot_comp { T1 T2 T3 : ltower } ( f : T1 -> T2 ) ( g : T2 -> T3 )
           ( isf : isovmonot f ) ( isg : isovmonot g ) : isovmonot ( funcomp f g ) .
Proof .
  intros . unfold isovmonot .  
  intros X Y is . 
  apply isg . 
  apply isf . 
  apply is . 

Defined.




  
(* End of the file ltowers.v *)