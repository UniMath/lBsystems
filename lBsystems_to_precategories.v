(** * lB-systems to precategories.  

by Vladimir Voevodsky, started on Jan. 22, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_Tj_Ttj.
Require Export lBsystems.lBsystems_S_St.



(** Contractibility axiom and its consequences *)




Definition Mor_and_fstar { BB : lBsystem_carrier } ( pax : ispointed BB )
           { T : T_ops_type BB } ( ax1b : T_ax1b_type T )
           ( n : nat )
           ( X1 : BB ) :
  total2 ( fun Mor_n : forall ( A : BB ) ( eq : ll A = n ) , UU =>
             forall ( A : BB ) ( eq : ll A = n ) ( f : Mor_n A eq )
                    ( X2 : BB ) ( isov : isabove X2 A ) ,
               total2 ( fun fstar_n : BB =>
                          dirprod ( isabove fstar_n X1 ) ( ll fstar_n - ll X1 = ll X2 - n ) ) ) .
Proof .
  intros BB pax T ax1b n . induction n as [ | n IHn ] . 
  intros . 
  split with ( fun x => fun eq => unit ) . 
  intros . 
  assert ( isov1 : isover X1 A ) . exact ( isoverll0 pax eq X1 ) .

  
  










  

(* End of the file lBsystems_to_precategories.v *)