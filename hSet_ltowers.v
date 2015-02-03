(** ** l-towers of (h-)sets. 

by Vladimir Voevodsky. File created on January 30, 2015. *)

Unset Automatic Introduction.

Require Export lBsystems.ltowers_over .



Definition hSet_ltower := total2 ( fun T : ltower => isaset T ) .

Definition hSet_ltower_pr1 : hSet_ltower -> ltower := pr1 . 
Coercion hSet_ltower_pr1 : hSet_ltower >-> ltower .

Definition isasetB ( T : hSet_ltower ) : isaset T := pr2 T .

Lemma isaprop_isover { T : hSet_ltower } ( X A : T ) : isaprop ( isover X A ) .
Proof .
  intros . exact ( isasetB _ _ _ ) . 

Defined.

Lemma isaprop_isabove { T : hSet_ltower } ( X A : T ) : isaprop ( isabove X A ) . 
Proof. 
  intros . 
  apply isapropdirprod . 
  exact ( pr2 ( _ > _ ) ) .

  exact ( isaprop_isover _ _ ) . 

Defined .


Lemma isinvovmonot_pocto { T : hSet_ltower } { A : T } { X Y : ltower_over A }
      ( isov : isover ( pocto X ) ( pocto Y ) ) : isover X Y .  
Proof .
  intros . 
  refine ( invmaponpathsincl pr1 _ _ _ _ ) . 
  apply isinclpr1 . 
  intro x . 
  apply isaprop_isover .

  rewrite ll_over_minus_ll_over . 
  rewrite ltower_over_ftn . 
  exact isov . 

  change ( ll X ) with ( ll ( pr1 X ) - ll A ) . 
  apply natgehandminusl . 
  exact ( isover_geh ( isov_isov Y ) ) . 

Defined.



Lemma isaset_ltower_over { T : hSet_ltower } ( X : T ) : isaset ( ltower_over X ) .
Proof .
  intros . 
  apply ( isofhleveltotal2 2 ) . 
  exact ( pr2 T ) . 

  intro x .
  apply isasetaprop . 
  apply isaprop_isover . 

Defined.

Definition hSet_ltower_over { T : hSet_ltower } ( X : T ) : hSet_ltower :=
  tpair _ ( ltower_over X ) ( isaset_ltower_over X ) . 
   
  
Lemma isovmonot_to_ltower_over { T : hSet_ltower } ( is : ispointed T )
      { X Y : T } ( isov : isover X Y ) : isover ( to_ltower_over is X ) ( to_ltower_over is Y ) .
Proof .
  intros .
  refine ( @isinvovmonot_pocto T ( cntr is ) (to_ltower_over is X) (to_ltower_over is Y) isov ) . 

Defined.



Definition lft { T : hSet_ltower }
           { X : T } { X' : ltower_over X } ( X'' : ltower_over ( pocto X' ) ) : ltower_over X' .
Proof .
  intros .
  refine (obj_over_constr _ ) .
  split with ( pocto X'' ) . 
  apply ( isover_trans ( isov_isov X'' ) ( isov_isov X' ) ) .
  apply isinvovmonot_pocto . 
  simpl .
  exact ( isov_isov X'' ) . 

Defined.

Lemma isovmonot_lft { T : hSet_ltower }
      { X : T } ( X' : ltower_over X ) : isovmonot ( @lft _ _ X' ) .
Proof .
  intros . unfold isovmonot . 
  intros X0 Y isov . 
  apply ( @isinvovmonot_pocto ( hSet_ltower_over X ) ) .
  simpl . 
  apply isinvovmonot_pocto. 
  simpl . 
  apply ( isovmonot_pocto _ isov ) . 

Defined.


Definition ovmonot_lft { T : hSet_ltower } { X : T } ( X' : ltower_over X ) :
  ovmonot_fun ( ltower_over ( pocto X' ) ) ( ltower_over X' ) :=
  ovmonot_fun_constr _ ( isovmonot_lft X' ) . 




Definition ovmonot_over { T1 T2 : hSet_ltower } ( f : ovmonot_fun T1 T2 )
           ( X : T1 ) : ovmonot_fun ( ltower_over X ) ( ltower_over ( f X ) ) .
Proof .
  intros . 
  refine ( ovmonot_fun_constr _ _ ) .
  intro X' . 
  split with ( f ( pocto X' ) ) . 
  apply ( pr2 f ) . 
  apply ( isov_isov X' ) . 

  intros X0 Y isov . simpl .
  apply isinvovmonot_pocto . 
  simpl .
  apply ( pr2 f ) . 
  apply ( isovmonot_pocto _ isov ) . 

Defined.


Definition ovmonot_to_over_pocto  { T : hSet_ltower } { X : T } ( X' : ltower_over X ) :
  ovmonot_fun ( ltower_over X' ) ( ltower_over ( pocto X' ) ) .
Proof .
  intros .
  refine ( ovmonot_fun_constr _ _ ) .
  intro X'' . 
  split with ( pocto ( pocto X'' ) ) . 
  apply isovmonot_pocto . 
  apply ( isov_isov X'' ) . 

  intros X0 Y isov .
  simpl .
  apply isinvovmonot_pocto . 
  simpl .
  apply isovmonot_pocto .  apply isovmonot_pocto . 
  apply isov . 

Defined.




  

Definition ovmonot_second { T : hSet_ltower }
           { X Y : T } ( f : ovmonot_fun ( ltower_over X ) ( ltower_over Y ) )
           ( X' : ltower_over X ) :
  ovmonot_fun ( ltower_over ( pocto X' ) ) ( ltower_over ( pocto ( f X' ) ) ) .
Proof .
  intros .
  set ( int1 :=
          ovmonot_funcomp ( ovmonot_lft X' )
                          ( @ovmonot_over ( hSet_ltower_over X ) ( hSet_ltower_over Y ) f X' ) ) .  
  apply ( ovmonot_funcomp int1 ( ovmonot_to_over_pocto _ ) ) .

Defined.






  

(* End of the file hSet_ltowers.v *)