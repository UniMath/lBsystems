(** * lB-systems to precategories.  

by Vladimir Voevodsky, started on Jan. 22, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_T_fun_Tj_Ttj.
Require Export lBsystems.lBsystems_S_fun.



Definition Mor_and_fstar { BB : lBsystem_carrier } ( pax : ispointed BB )
           { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1a : T_ax1a_type T ) ( ax1b : T_ax1b_type T )
           ( n : nat ) ( X1 A : BB ) ( eq : ll A = n ) : 
  total2 ( fun Mor_X1_A : UU =>
             forall f : Mor_X1_A , ovmonot_fun ( ltower_over A ) ( ltower_over X1 ) ) . 
Proof .
  intros BB pax T ax0 ax1a ax1b n . induction n as [ | n IHn ] . 
  intros . 
  split with unit .

  intro .
  refine ( ovmonot_fun_constr _ _ ) . 
  intro X2 . 
  set ( X2' := pocto X2 ) .
  exact ( Tprod_fun pax ax1b X1 X2' ) . 

  intros X Y isov .
  simpl . 
  apply ( isovmonot_Tprod_fun pax ax0 ax1a ax1b ) .
  apply isovmonot_pocto . 
  exact isov . 

  intros .
  assert ( eqft : ll ( ft A ) = n ) . rewrite ll_ft . rewrite eq . simpl . rewrite natminuseqn .
  apply idpath .

  set ( Mor_X1_ftA := pr1 ( IHn X1 ( ft A ) eqft ) ) .
  set ( Mor_X1_A :=
          total2 ( fun ftf : Mor_X1_ftA =>
                     Tilde_dd ( pocto ( pr2 ( IHn X1 ( ft A ) eqft ) ftf ( X_over_ftX A ) ) ) ) ) .
  split with Mor_X1_A . 

  intro f .
  set ( ftf := pr1 f : Mor_X1_ftA ) .
  set ( ftf_star := pr2 ( IHn X1 ( ft A ) eqft ) ftf :
                     ovmonot_fun ( ltower_over ( ft A ) ) ( ltower_over X1 ) ) .
  set ( ftf_star_A := ftf_star ( X_over_ftX A ) : ltower_over X1 ) . 





  set ( s_f := pr2 f : Tilde_dd ) . 
  assert ( fun1 : ovmonot_fun ( ltower_over A ) ( ltower_over 
  


  
  
  intros . 
  assert ( isov : isover X1 A ) .
  exact ( isoverll0 pax eq X1 ) .

  split with ( Tj ax0 ax1b isov isab ) .

  split with ( isabove_Tj _ _ _ _ ) . 

  rewrite ( natminuseqn _ ) . 
  rewrite ll_Tj . 
  rewrite eq . 
  rewrite natminuseqn . 
  apply plusminusnmm . 

  intros .
  set ( Morn := fun X1 => pr1 ( IHn X1 ) ) . 
  set ( fstarn := fun X1 A eq f X2 isab => pr1 ( pr2 ( IHn X1 ) A eq f X2 isab ) ) . 
  set ( fstareq := fun X1 A eq f X2 isab => pr2 ( pr2 ( IHn X1 ) A eq f X2 isab ) ) . 
  refine ( tpair _ _ _ ) . 
  intros .

  assert ( eqft : ll ( ft A ) = n ) . 
  rewrite ll_ft . 
  rewrite eq . 
  simpl . rewrite natminuseqn . apply idpath . 

  exact ( total2 ( fun ftf : Morn X1 ( ft A ) eqft =>
                     total2 ( fun r : Tilde BB => dd r = X1 ) ) ) . 

  intros . 
  

  

*)



  

(* End of the file lBsystems_to_precategories.v *)