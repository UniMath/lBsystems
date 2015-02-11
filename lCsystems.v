(** ** lCsystems by Vladimir Voevodsky,

started Dec. 4, 2014, continued Jan. 22, 2015, Feb. 11, 2015 

We refer below to the paper "Subsystems and regular quotients of C-systems"
by V. Voevodsky as "Csubsystems".

*)

Require Export Foundations.hlevel2.hnat .
Require Export RezkCompletion.precategories.
Require Export lBsystems.ltowers.

Unset Automatic Introduction.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Local Notation "f ;; g" := (compose f g)(at level 50). 

(** To precategories *)


Definition wide_comp { C : precategory_data } { X Y Y' Z : C }
           ( f : X --> Y ) ( g : Y' --> Z ) ( e : Y = Y' ) : X --> Z :=
  ( transportf ( fun A : C => ( X --> A ) ) e f ) ;; g  . 


(** *** The C0-systems

The following sequence of definitions is a formalization of Definition 2.1 in Csubsystems *)


Definition ltower_precat := total2 ( fun C : precategory => ltower_str C ) .

Definition ltower_precat_to_ltower ( CC : ltower_precat ) : ltower :=
  tpair ( fun C : UU => ltower_str C ) ( pr1 CC ) ( pr2 CC ) .
Coercion ltower_precat_to_ltower : ltower_precat >-> ltower .

Definition ltower_precat_pr1 : ltower_precat -> precategory := pr1 .
Coercion ltower_precat_pr1 : ltower_precat >-> precategory .

Definition ltower_and_p_precat :=
  total2 ( fun CC : ltower_precat  => forall X : CC , X --> ft X ) .

Definition ltower_and_p_precat_pr1 : ltower_and_p_precat -> ltower_precat := pr1 . 
Coercion ltower_and_p_precat_pr1 : ltower_and_p_precat >-> ltower_precat . 
                                                          
Definition pX { CC : ltower_and_p_precat } ( X : CC ) : X --> ft X := pr2 CC X .

Definition pointed_ltower_and_p_precat :=
  total2 ( fun CC : ltower_and_p_precat => ispointed CC ) .

Definition pointed_ltower_and_p_precat_pr1 : pointed_ltower_and_p_precat ->
                                             ltower_and_p_precat := pr1 .
Coercion pointed_ltower_and_p_precat_pr1 : pointed_ltower_and_p_precat >->
                                             ltower_and_p_precat.

Definition pointed_ltower_and_p_precat_pr2 : forall C : pointed_ltower_and_p_precat,  ispointed C :=
  pr2 . 
Coercion pointed_ltower_and_p_precat_pr2 : pointed_ltower_and_p_precat >-> ispointed . 




(* *)

Definition q_data_type ( CC : ltower_and_p_precat ) := 
  forall ( X Y : CC ) ( is : ll X > 0 ) ( f : Y --> ft X ) ,
    total2 ( fun fstarX : CC => fstarX --> X ) .   

Definition f_star { CC : ltower_and_p_precat } (qd : q_data_type CC ) 
           { X Y : CC } ( is : ll X > 0 ) ( f : Y --> ft X ) := 
  pr1 ( qd X Y is f ) . 

Definition q_of_f { CC : ltower_and_p_precat } ( qd : q_data_type CC )
           { X Y : CC } ( is : ll X > 0 ) ( f : Y --> ft X ) : f_star qd is f --> X :=
  pr2 ( qd X Y is f ) . 

Definition wide_q { CC : ltower_and_p_precat } ( qd : q_data_type CC ) 
           { X : CC } { X' Y : CC } ( is : ll X > 0 ) ( f : Y --> X' ) ( e : X' = ft X ) : 
  total2 ( fun fstarX => fstarX --> X ) :=
  qd X Y is ( transportf ( fun A : CC => ( Y --> A ) ) e f ) . 


(** The numbering of the axioms below is according to the Csubsystems *)
           


Notation "`C0sysax1_type` CC" := (ispointed CC) (at level 50) . 

Notation C0sysax2 := ll_ft .  (* Note that this is a notation dfor the axiom itself not for the
type of the axiom *)

Lemma C0sysax3 { CC : ltower } 



Definition C0sysax5a_type { CC : ltower_and_p_precat } ( qd : q_data_type CC ) :=
  forall ( X Y : CC ) ( is : ll X > 0 ) ( f : Y --> ft X ) , ll ( f_star qd is f ) > 0  .

Definition C0sysax5b_type { CC : ltower_and_p_precat } ( qd : q_data_type CC ) :=
  forall ( X Y : CC ) ( is : ll X > 0 ) ( f : Y --> ft X ) , ft ( f_star qd is f ) = Y .

(** 

A problem arises with the following definition since one of the morphisms f or 
( pX ftd ( fstar qd is f ) ) 
need to be transported along the equality fteq in order for the composition  
( pX ftd ( fstar qd is f ) ) ;; f 
to be defined. Therefore we have to use wide_comp  *)





Definition C0sysax5c_type { CC :  ltower_and_p_precat } { qd : q_data_type CC }
           ( ax : C0sysax5b_type qd ) := 
  forall ( X Y : CC ) ( is : ll X > 0 ) ( f : Y --> ft X ) , 
    wide_comp ( pX ( f_star qd is f ) ) f ( ax X Y is f ) = ( q_of_f qd is f ) ;; ( pX X ) . 


Definition C0sysax6_type { CC : ltower_and_p_precat } { qd : q_data_type CC } :=
  forall ( X : CC ) ( is : ll X > 0 ) ,
    qd _ _ is ( identity ( ft X ) ) = tpair _ X ( identity X ) . 

Definition C0sysax7_type { CC : ltower_and_p_precat } { qd : q_data_type CC } 
  ( ax5a : C0sysax5a_type qd ) ( ax5b : C0sysax5b_type qd ) :=
  forall ( X Y Z : CC ) ( is : ll X > 0 ) ( g : Z --> Y ) ( f : Y --> ft X ) , 
    qd _ _ is ( g ;; f ) = 
    let is' := ax5a _ _ is f   in
    tpair _ ( pr1 ( wide_q qd is' g ( pathsinv0 ( ax5b X Y is f ) ) ) ) 
          ( ( pr2 ( wide_q qd is' g ( pathsinv0 ( ax5b X Y is f ) ) ) ) ;; q_of_f qd is f  ) . 







(* Lemma loff_star { CC : ltower_and_p_precat } { ft : ft_data CC } { l : CC -> nat } { qd : q_data_type ft l }
      ( ax2 : C0sysax2 l ft ) ( ax5a : C0sysax5a qd ) { X : CC } { Y : CC } ( is : natgth ( l X ) 0 ) ( f : Y --> ft X ) : 
  l ( f_star qd is f ) = 1 + l Y . 
Proof. intros .  admit . Qed . *)
  

(* Definition C0sysax1 { CC : UU } ( l : CC -> nat ) := iscontr ( total2 ( fun X : CC => l X = 0 ) ) . *)

(* Definition C0pt { CC : UU } { l : CC -> nat } ( ax : C0sysax1 l ) : CC := pr1 ( pr1  ax ) . *)

(* Definition C0sysax3 { CC : ltower_and_p_precat } { ft : ft_data CC } { l : CC -> nat } { ax : C0sysax1 l } :=
  ft ( C0pt ax ) = C0pt ax . *) 

(* Here it might be better to use the standard definition of being a final object *)

(* Definition C0sysax4 { CC : ltower_and_p_precat } { l : CC -> nat } { ax : C0sysax1 l } := 
  forall X : CC , iscontr ( X --> C0pt ax ) . *)





(* 

Note: continue checking the definition of a C-system as a category with attributes together with additional data.

Then check the connection with categories with families of Peter Dybjer. *)




(* Let's try the definition of a category with attributes instead. 

Definition atr_data_1 ( CC : ltower_and_p_precat ) := total2 ( fun 

*)





 



(* End of the file lCsystems.v *)