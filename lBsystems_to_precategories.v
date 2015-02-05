(** * lB-systems to precategories.  

by Vladimir Voevodsky, started on Jan. 22, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_T_fun_Tj_Ttj.
Require Export lBsystems.lBsystems_S_fun.



Definition Mor_and_fstar { BB : lBsystem_carrier } ( pax : ispointed BB )
           { T : T_ops_type BB } ( tax0 : T_ax0_type T )
           ( tax1a : T_ax1a_type T ) ( tax1b : T_ax1b_type T )
           { S : S_ops_type BB } ( sax0 : S_ax0_type S )
           ( sax1a : S_ax1a_type S ) ( sax1b : S_ax1b_type S )
           ( n : nat ) ( X1 A : BB ) ( eq : ll A = n ) : 
  total2 ( fun Mor_X1_A : UU =>
             forall f : Mor_X1_A ,
               total2 ( fun fstar : ovmonot_fun ( ltower_over A ) ( ltower_over X1 ) =>
                        isllmonot fstar ) ) . 
Proof .
  intros BB pax T tax0 tax1a tax1b S sax0 sax1a sax1b n . induction n as [ | n IHn ] . 
  intros . 
  split with unit .

  intro .
  refine ( tpair _ _ _ ) . 
  refine ( ovmonot_fun_constr _ _ ) . 
  intro X2 . 
  set ( X2' := pocto X2 ) .
  exact ( Tprod_fun pax tax1b X1 X2' ) . 

  intros X Y isov .
  simpl . 
  apply ( isovmonot_Tprod_fun pax tax0 tax1a tax1b ) .
  apply isovmonot_pocto . 
  exact isov . 

  simpl . 
  apply ( @isllmonot_funcomp _ _ _ ( ovmonot_Tprod_fun pax tax1b X1 ) pocto ) .  

  
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
  set ( ftf_star_A := pocto ( ftf_star ( X_over_ftX A ) : ltower_over X1 ) ) .
  set ( s_f := pr1 ( pr2 f ) : Tilde BB ) .
  set ( eq_s_f := pr2 ( pr2 f ) : dd ( s_f ) = ftf_star_A ) . 
  assert ( fun1 : ovmonot_fun ( ltower_over A ) ( ltower_over ftf_star_A ) ) .
  apply ( @ovmonot_second _ ( ft A ) X1 ftf_star ( X_over_ftX A ) ) .

  set ( fun2 := ovmonot_S_fun sax0 sax1a sax1b s_f ) .
  rewrite eq_s_f in fun2 .
  assert ( eq' : ft ftf_star_A = X1 ) . 
  
  assert ( fun2 : ovmonot_fun ( ltower_over ftf_star_A ) ( ltower_over X1 ) ) .
  rewrite <- eq_s_f . 
  apply ( S_fun 
  


  
  
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