(** ** l-towers of (h-)sets. 

by Vladimir Voevodsky. File created on January 30, 2015. *)

Unset Automatic Introduction.

Require Export lBsystems.ltowers .



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


Lemma to_isover_over { T : hSet_ltower } { A : T } { X Y : ltower_over A }
      ( isov : @isover T ( pr1 X ) ( pr1 Y ) ) : @isover ( ltower_over A ) X Y .  
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


 
  

(* End of the file hSet_ltowers.v *)