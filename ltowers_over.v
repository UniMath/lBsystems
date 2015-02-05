(** ** Constructions related to ltowers opver an object  

by Vladimir Voevodsky, started on Feb. 3, 2015.

*)

Unset Automatic Introduction.

Require Export lBsystems.ltowers.








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


(** **** Standard constructions of over-objects *)

Definition X_over_X { T : ltower } ( X : T ) : ltower_over X :=
  obj_over_constr ( isover_XX X ) .

Definition X_over_ftX { T : ltower } ( X : T ) : ltower_over ( ft X ) :=
  obj_over_constr ( isover_X_ftX X ) . 




(** The projection pocto from the over-tower to the tower is over-monotone *)



Lemma ll_over_minus_ll_over { T : ltower } { A : T } ( X1 X2 : ltower_over A ) :
  ll X1 - ll X2 = ll ( pocto X1 ) - ll ( pocto X2 ) . 
Proof .
  intros . 
  destruct X1 as [ X1 isov1 ] . destruct X2 as [ X2 isov2 ] . 
  unfold ll . 
  simpl . 
  unfold ltower_over_ll .  simpl . 
  change _ with ( ( ll X1 - ll A ) - ( ll X2 - ll A ) = ( ll X1 - ll X2 ) ) . 
  rewrite natminusassoc . 
  rewrite natpluscomm . 
  rewrite ( minusplusnmm _ _ ( isover_geh isov2 ) ) . 
  apply idpath . 

Defined.


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



Lemma isllmonot_pocto { T : ltower } { A : T } : isllmonot ( @pocto T A ) . 
Proof .
  intros .
  unfold isllmonot .
  intros X Y isov .
  apply ( ! ( ll_over_minus_ll_over X Y ) ) .

Defined.





(** **** Some functions between over-towers *)


Definition to_ltower_over { T : ltower } ( is : ispointed T ) ( X : T ) : ltower_over ( cntr is ) .
Proof .
  intros . 
  exact ( obj_over_constr ( isoverll0 is ( ll_cntr is ) X ) ) .

Defined.


Lemma ll_to_ltower_over { T : ltower } ( is : ispointed T ) ( X : T ) :
  ll ( to_ltower_over is X ) = ll X .
Proof .
  intros.
  unfold ll . 
  simpl .
  unfold ltower_over_ll . 
  rewrite ll_cntr . 
  rewrite natminuseqn .
  apply idpath . 

Defined.



Lemma isllmonot_to_ltower_over { T : ltower } ( is : ispointed T ) :
  isllmonot ( to_ltower_over is ) .
Proof .
  unfold isllmonot . intros .
  repeat rewrite ll_to_ltower_over . apply idpath . 
  
Defined.




  
(** The following constructions probably work for all ltowers 
but we only give a proof for ltowers of sets in the file hSet_ltowers.v . 

Definition ovmonot_to_over_pocto  { T : ltower } { X : T } { X' : ltower_over X } :
  ovmonot_fun ( ltower_over X' ) ( ltower_over ( pocto X' ) ) .

Definition ovmonot_over { T1 T2 : ltower } ( f : ovmonot_fun T1 T2 )
           ( X : T1 ) : ovmonot_fun ( ltower_over X ) ( ltower_over ( f X ) ) .

Definition lft { T : hSet_ltower }
           { X : T } { X' : ltower_over X } ( X'' : ltower_over ( pocto X' ) ) : ltower_over X' .

Definition ovmonot_second { T : ltower }
           { X Y : T } ( f : ovmonot_fun ( ltower_over X ) ( ltower_over Y ) )
           ( X' : ltower_over X ) :
  ovmonot_fun ( ltower_over ( pocto X' ) ) ( ltower_over ( pocto ( f X' ) ) ) .


Lemma isovmonot_to_ltower_over { T : ltower } ( is : ispointed T ) : isovmonot ( to_ltower_over is ) . 

*)





(* End of the file ltowers_over.v *)