(** ** lC_to_lB_systems by Vladimir Voevodsky,

started Feb. 15, 2015 

We refer below to the paper "Subsystems and regular quotients of C-systems"
by V. Voevodsky as "Csubsystems".

 *)


Require Export lCsystems.lCsystems.
Require Export lBsystems.lBsystems.

Unset Automatic Introduction.


(** *** The function from lC-systems to pre-lB-systems. *)

(** **** Constructing the lB-system carrier *)

Definition ltower_and_p_Tilde ( CC : ltower_precat_and_p ) :=
  total2 ( fun X : CC => dirprod ( ll X > 0 ) ( Ob_tilde_rel X ) ) .

Lemma isaset_ltower_and_p_Tilde { CC : ltower_precat_and_p }
      ( is1 : has_homsets CC ) ( is2 : isaset CC ) :
  isaset ( ltower_and_p_Tilde CC ) .
Proof.
  intros . 
  apply ( isofhleveltotal2 2 ) . 
  apply is2 . 

  intro X . 
  unfold Ob_tilde_rel.
  apply ( isofhleveltotal2 2 ) .

  apply isasetaprop .
  apply ( pr2 ( ll X > 0 ) ) . 

  intro . 
  apply ( isofhleveltotal2 2 ) . 

  apply is1  .

  intro Y .
  apply isasetaprop . 
  apply is1 . 

Defined.

  

Definition ltower_and_p_dd ( CC : ltower_precat_and_p ) ( r : ltower_and_p_Tilde CC ) : CC :=
  pr1 r . 

Definition ltower_and_p_to_lBsystem_carrier { CC : pltower_precat_and_p }
  ( is1 : has_homsets CC ) ( is2 : isaset CC ) : lBsystem_carrier .
Proof .
  intros .
  refine ( lBsystem_carrier_constr _ _ ) . 
  refine ( hSet_pltower_constr _ _ ) .
  apply ( hSet_ltower_constr CC is2 ) . 

  apply ( pr2 CC ) . 

  apply ( tpair _ _ ( isaset_ltower_and_p_Tilde is1 is2 ) ) . 

  apply ltower_and_p_dd . 

  intro r . simpl in r .
  apply ( pr1 ( pr2 r ) ) . 

Defined.


(** **** Constructing operation T *)










  
  
(* End of the file lC_to_lB_systems.v *)