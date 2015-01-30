(** * lB-systems to precategories.  

by Vladimir Voevodsky, started on Jan. 22, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_Tj_Ttj.
Require Export lBsystems.lBsystems_S_St.





(*


Definition Mor_and_fstar { BB : lBsystem_carrier } ( pax : ispointed BB )
           { T : T_ops_type BB } ( ax0 : T_ax0_type T ) ( ax1b : T_ax1b_type T )
           ( n : nat ) ( X1 A : BB ) ( eq : ll A = n ) : 
  total2 ( fun Mor_X1_A : UU =>
             forall f : Mor_X1_A , monotone_fun ( ltower_over A ) ( ltower_over X1 ) ) . 
Proof .
  intros BB pax T ax0 ax1b n . induction n as [ | n IHn ] . 
  intros . 
  split with unit .

  intro . 
  

  
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