(** * lB-systems to precategories.  

by Vladimir Voevodsky, started on Jan. 22, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_T_fun_Tj_Ttj.
Require Export lBsystems.lBsystems_S_fun.




Definition for_Mor { BB : lBsystem_carrier } 
           { S : S_ops_type BB } ( sax0 : S_ax0_type S )
           ( m : nat ) (Z : BB ) ( le : m <= ll Z ) : UU .
Proof.
  intros until m .
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


  

Definition Mor_and_fstar { BB : lBsystem_carrier } ( is : ispointed BB )
           { T : T_ops_type BB } ( tax0 : T_ax0_type T )
           ( tax1a : T_ax1a_type T ) ( tax1b : T_ax1b_type T )
           { S : S_ops_type BB } ( sax0 : S_ax0_type S )
           ( sax1a : S_ax1a_type S ) ( sax1b : S_ax1b_type S )
           ( X1 : BB ) ( n : nat ) ( A : BB ) ( eq : ll A = n ) : 
  total2 ( fun Mor_X1_A : UU =>
             forall f : Mor_X1_A ,
               ltower_fun ( ltower_over A ) ( ltower_over X1 ) ) . 
Proof .
  intros until n . induction n as [ | n IHn ] . 
  intros . 
  split with unit .

  intro .
  exact ( ltower_Tj_fun tax0 tax1a tax1b ( isoverll0 is eq X1 ) ) . 

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
  apply ( ltower_fun_S sax0 sax1a sax1b s_f ) .

  assert ( gt0 : ll (ftf_star (X_over_ftX A)) > 0 ) .
  rewrite ll_ltower_fun .
  rewrite ll_X_over_ftX . 
  apply idpath . 

  rewrite eq . apply natgthsn0 .

  apply ispointed_ltower_over . 
  
  assert ( eq' : ft ftf_star_A = X1 ) .
  unfold ftf_star_A .
  rewrite ft_pocto .
  assert ( eq1 : ft (ftf_star (X_over_ftX A)) = X_over_X X1 ) . 
  assert ( eq2 : ll ( ft (ftf_star (X_over_ftX A)) ) = 0 ) .
  rewrite ll_ft . 
  rewrite ll_ltower_fun . 
  rewrite ll_X_over_ftX .
  apply idpath . 

  rewrite eq . apply natgthsn0 .

  apply ispointed_ltower_over . 

  apply ( noparts_ispointed ( ispointed_ltower_over X1 ) eq2 ( ll_X_over_X X1 ) ) . 

  rewrite eq1 .
  apply idpath . 

  apply gt0 . 

  set ( fun12 := ltower_funcomp fun1 fun2 ) .
  rewrite eq' in fun12 . 
  exact fun12 . 

Defined.

  

(* End of the file lBsystems_to_precategories.v *)