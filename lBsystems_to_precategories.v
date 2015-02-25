(** ** lB-systems to precategories.  

by Vladimir Voevodsky, started on Jan. 22, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_T_fun_Tj_Ttj.
Require Export lBsystems.lBsystems_S_fun.

Require Export lBsystems.lB0systems . 


(** *** The first construction of the types Mor_from_B *)


(** We first define for Z in an lB-system and m <= ll Z the type
( iterated_sections m Z ) that corresponds to the sections of the projection Z -> ft^m Z 
in the associated lC-system. We do it for non-unital prelBsystems but the only structure that
is actually required is an lBsystem_carrier and an operation of type S_ops_type satisfying
axiom ax0. *)

Definition iterated_sections { BB : prelBsystem_non_unital }
           ( m : nat ) (Z : BB ) ( le : m <= ll Z ) : UU .
Proof.
  intros until m . set ( S := @S_op BB ) . set ( sax0 := @S_ax0 BB ) . 
  induction m as [ | m IHm ] .
  intros. exact unit .

  intros Z le .
  destruct ( natgehchoice _ _ ( natgehn0 m ) ) as [ gt0 | eq0 ] . 
  assert ( inn : forall s : Tilde_dd ( ftn m Z ), S_dom s Z ) .
  intro s .
  unfold S_dom .
  set ( eq := pr2 s : dd s = ftn m Z ) . simpl in eq .
  rewrite eq .  
  apply ( isabove_X_ftnX gt0 ) .
  apply ( natgehgthtrans _ _ _ le ( natgthsn0 _ ) ) . 

  assert ( le' : forall s : Tilde_dd ( ftn m Z ), m <= ll ( S s Z ( inn s ) ) ) . 
  intro s . 
  rewrite sax0 . 
  assert ( leint := natgehandminusr _ _ 1 le ) . 
  simpl in leint . 
  rewrite natminuseqn in leint .
  exact leint . 

  exact ( total2 ( fun s : Tilde_dd ( ftn m Z ) => IHm ( S s Z ( inn s ) ) (le' s) ) ) .

  exact ( Tilde_dd Z ) . 

Defined.


(** We now define morphisms X --> Y as iterated sections of the projection Tprod X Y --> X *)


Definition Mor_from_B { BB : lB0system_non_unital } ( X Y : BB ) : UU .
Proof.
  intros.
  refine ( iterated_sections ( ll Y ) ( Tprod X Y ) _ ) .
  rewrite ll_Tprod . 
  apply natlehmplusnm . 

Defined.


(** Here is another definition of morphisms that defines them together with the corresponding
operation f_star *)


Definition Mor_and_fstar { BB : lB0system_non_unital }
           ( X1 : BB ) ( n : nat ) ( A : BB ) ( eq : ll A = n ) : 
  total2 ( fun Mor_X1_A : UU =>
             forall f : Mor_X1_A ,
               ltower_fun ( ltower_over A ) ( ltower_over X1 ) ) . 
Proof .
  intros until n . induction n as [ | n IHn ] . 
  intros . 
  split with unit .

  intro .
  exact ( Tj_fun ( @isoverll0 BB _ eq X1 ) ) . 

  intros .
  assert ( eqft : ll ( ft A ) = n ) . rewrite ll_ft . rewrite eq . simpl . rewrite natminuseqn .
  apply idpath .

  set ( Mor_X1_ftA := pr1 ( IHn ( ft A ) eqft ) ) .
  set ( Mor_X1_A :=
          total2 ( fun ftf : Mor_X1_ftA =>
                     Tilde_dd ( pocto ( ( pr2 ( IHn ( ft A ) eqft ) ftf ) ( X_over_ftX A ) ) ) ) ) .
  split with Mor_X1_A . 

  intro f .
  set ( ftf := pr1 f : Mor_X1_ftA ) .
  set ( s_f := pr1 ( pr2 f ) : Tilde BB ) .
  set ( ftf_star := pr2 ( IHn ( ft A ) eqft ) ftf :
                      ltower_fun ( ltower_over ( ft A ) ) ( ltower_over X1 ) ) .
  set ( ftf_star_A := pocto ( ftf_star ( X_over_ftX A ) : ltower_over X1 ) ) .
  set ( eq_s_f := pr2 ( pr2 f ) : dd ( s_f ) = ftf_star_A ) . 
  assert ( fun1 : ltower_fun ( ltower_over A ) ( ltower_over ftf_star_A ) ) .
  apply ( ltower_fun_second ftf_star ( X_over_ftX A ) ) .

  assert ( fun2 : ltower_fun ( ltower_over ftf_star_A ) ( ltower_over ( ft ftf_star_A ) ) ) . 
  rewrite <- eq_s_f .
  apply ( S_fun s_f ) .

  assert ( gt0 : ll (ftf_star (X_over_ftX A)) > 0 ) .
  rewrite (@ll_ltower_fun (pltower_over ( ft A ) )).
  change ( ll (X_over_ftX A) > 0 ) . 
  rewrite ll_X_over_ftX . 
  apply idpath . 

  rewrite eq . apply natgthsn0 .
  
  assert ( eq' : ft ftf_star_A = X1 ) .
  unfold ftf_star_A .
  rewrite ft_pocto .
  assert ( eq1 : ft (ftf_star (X_over_ftX A)) = X_over_X X1 ) . 
  assert ( eq2 : ll ( ft (ftf_star (X_over_ftX A)) ) = 0 ) .
  rewrite ll_ft . 
  rewrite (@ll_ltower_fun (pltower_over (ft A))). 
  change ( ll (X_over_ftX A) - 1 = 0 ) . 
  rewrite ll_X_over_ftX . 
  apply idpath . 

  rewrite eq . apply natgthsn0 .

  apply ( @noparts_ispointed  ( pltower_over _ ) _ _ eq2 ( ll_X_over_X X1 ) ) . 

  rewrite eq1 .
  apply idpath . 

  apply gt0 . 

  set ( fun12 := ltower_funcomp fun1 fun2 ) .
  rewrite eq' in fun12 . 
  exact fun12 . 

Defined.

  

(* End of the file lBsystems_to_precategories.v *)