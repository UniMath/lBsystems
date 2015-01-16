(** * The structure delta on carriers of lB-systems and its properties

deltaT, deltaS, deltaSid and SdeltaT and StdeltaTt. 

By Vladimir Voevodsky, started Jan. 14, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems_T_Tt.
Require Export lBsystems_S_St.

(** The structure delta *)

Definition delta_type ( BB : lBsystem_carrier ) :=
  forall ( X : BB ) ( gt0 : ll X > 0 ) , Tilde BB .

(** The zeros property (later an axiom ) of operations delta *)

Definition delta_ax0_type { BB : lBsystem_carrier } ( dlt : delta_type BB ) :=
  forall ( X : BB ) ( gt0 : ll X > 0 ) , ll ( dd ( dlt X gt0 ) ) = 1 + ll X .

(** The first property (later an axiom) of operations delta *)

Definition delta_ax1_type { BB : lBsystem_carrier }
           ( T : T_ops_type BB )
           ( dlt : delta_type BB ) :=
  forall ( X : BB ) ( gt0 : ll X > 0 ) , dd ( dlt X gt0 ) = T X X ( T_dom_refl X gt0 ) .

Lemma ll_dd_dlt { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( ax0 : T_ax0_type T ) 
           { dlt : delta_type BB } ( ax1 : delta_ax1_type T dlt )
           { X : BB } ( gt0 : ll X > 0 ) : ll ( dd ( dlt X gt0 ) ) = 1 + ll X .
Proof .
  intros .
  rewrite ax1 .
  rewrite ax0 . 
  exact ( idpath _ ) .

Defined.

(** Lemmas that are required to formulate the property deltaT *)

Lemma Tt_dom_12_to_1_dlt2 { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( tax1b : T_ax1b_type T ) 
      { dlt : delta_type BB } ( dltax1 : delta_ax1_type T dlt )  
      { X1 X2 : BB } ( inn12 : T_dom X1 X2 ) : Tt_dom  X1 ( dlt X2 ( T_dom_gt0_2 inn12 ) ) .
Proof .
  intros . 
  unfold Tt_dom . 
  refine (T_dom_constr _ _ ) .
  exact ( T_dom_gt0 inn12 ) .

  rewrite dltax1 . 
  exact ( isabove_trans ( tax1b _ _ _ ) ( T_dom_isabove inn12 ) ) .  

Defined.


           

(** The property deltaT *)

Definition deltaT_type { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( tax0 : T_ax0_type T ) ( tax1b : T_ax1b_type T ) 
           { Tt : Tt_ops_type BB }
           { dlt : delta_type BB } ( dltax1 : delta_ax1_type T dlt ) :=
  forall ( X1 X2 : BB ) ( inn12 : T_dom X1 X2 ) ,
    Tt X1 ( dlt X2 ( T_dom_gt0_2 inn12 ) ) ( Tt_dom_12_to_1_dlt2 tax1b dltax1 inn12 ) =
    dlt ( T X1 X2 inn12 ) ( ll_T_gt0 tax0 inn12 ) .


(** Lemmas that are required to formulate the property deltaS *)

Lemma St_dom_r1_to_r_dlt1 { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( tax1b : T_ax1b_type T ) 
      { dlt : delta_type BB } ( dltax1 : delta_ax1_type T dlt )  
      { r : Tilde BB } { X : BB } ( innr1 : S_dom r X ) :
  St_dom  r ( dlt X ( S_dom_gt0 innr1 ) ) .
Proof .
  intros . 
  unfold St_dom .
  unfold S_dom .
  rewrite dltax1 . 
  exact ( isabove_trans ( tax1b _ _ _ ) innr1 ) .  

Defined.




(** The property deltaS *)

Definition deltaS_type { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( tax1b : T_ax1b_type T ) 
           { S : S_ops_type BB } ( sax0 : S_ax0_type S )
           { St : St_ops_type BB }
           { dlt : delta_type BB } ( dltax1 : delta_ax1_type T dlt ) :=
  forall ( r : Tilde BB ) ( X : BB ) ( innr1 : S_dom r X ) ,
    St r ( dlt X ( S_dom_gt0 innr1 ) ) ( St_dom_r1_to_r_dlt1 tax1b dltax1 innr1 ) =
    dlt ( S r X innr1 ) ( ll_S_gt0 sax0 innr1 ) .



(** Lemmas needed to formulate the property deltaSid *)

Lemma St_dom_r_dltddr { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( tax1b : T_ax1b_type T )
      { dlt : delta_type BB } ( dltax1 : delta_ax1_type T dlt )
      ( r : Tilde BB ) : St_dom r ( dlt ( dd r ) ( ll_dd r ) ) . 
Proof.
  intros .
  unfold St_dom. 
  unfold S_dom .
  rewrite dltax1 .
  exact ( tax1b _ _ _ ) . 

Defined.






  

(** The property deltaSid *)

Definition deltaSid_type { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( tax1b : T_ax1b_type T )
           { dlt : delta_type BB } ( dltax1 : delta_ax1_type T dlt )
           { St : St_ops_type BB } :=
  forall ( r : Tilde BB ) ,
    St r ( dlt ( dd r ) ( ll_dd r ) ) ( St_dom_r_dltddr tax1b dltax1 r ) = r . 




(** Lemmas needed to formulate the property SdeltaT *)

Lemma T_dom_SdeltaT_l1 { BB : lBsystem_carrier }
      { X1 X2 : BB } ( gt0 : ll X1 > 0 ) ( isov : isover X2 X1 ) : T_dom X1 X2 .
Proof.
  intros .
  refine ( T_dom_constr gt0 _ ) . 
  exact ( isabove_X_ftA' isov gt0 ) . 

Defined.
  
Lemma S_dom_gt0_isab_to_dlt1_T12 { BB : lBsystem_carrier }
      { T : T_ops_type BB } ( tax0 :  T_ax0_type T ) ( tax1a : T_ax1a_type T ) 
      { dlt : delta_type BB } ( dltax1 : delta_ax1_type T dlt ) 
      { X1 X2 : BB } ( gt0 : ll X1 > 0 ) ( isab : isabove X2 X1 ) :
  S_dom ( dlt X1 gt0 ) ( T X1 X2 ( T_dom_SdeltaT_l1 gt0 isab ) ) .
Proof.
  intros .
  unfold S_dom . 
  rewrite dltax1 . 
  refine ( isabove_T_T_2 tax0 tax1a _ _ isab ) .

Defined.

  

  

(** The property SdeltaT *)


Definition SdeltaT_type { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( tax0 : T_ax0_type T ) ( tax1a : T_ax1a_type T )
           { dlt : delta_type BB } ( dltax1 : delta_ax1_type T dlt ) 
           { S : S_ops_type BB } :=
  forall ( X1 X2 : BB ) ( gt0 : ll X1 > 0 ) ( isab : isabove X2 X1 ) ,
    S ( dlt X1 gt0 ) ( T X1 X2 ( T_dom_SdeltaT_l1 gt0 isab ) )
      ( S_dom_gt0_isab_to_dlt1_T12 tax0 tax1a dltax1 gt0 isab ) = X2 . 


(** Lemmas needed to formulate the property StdeltaTt *)


Lemma Tt_dom_StdeltaTt_l1 { BB : lBsystem_carrier }
      { X : BB } { r : Tilde BB } ( gt0 : ll X > 0 ) ( isab : isabove ( dd r ) X ) :
  Tt_dom X r .
Proof.
  intros .
  refine ( T_dom_constr _ _ ) . 
  exact gt0 . 

  exact ( isabove_X_ftA isab ) . 

Defined.


  
Lemma St_dom_gt0_isab_to_dlt1_Tt1r { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( tax0 : T_ax0_type T ) ( tax1a : T_ax1a_type T )
           { dlt : delta_type BB } ( dltax1 : delta_ax1_type T dlt )
           { Tt : Tt_ops_type BB } ( ttax1 : Tt_ax1_type T Tt )
           { X : BB } { r : Tilde BB } ( gt0 : ll X > 0 ) ( isab : isabove ( dd r ) X ) :
  St_dom ( dlt X gt0 ) ( Tt X r ( Tt_dom_StdeltaTt_l1 gt0 isab ) ) .
Proof .
  intros .
  unfold St_dom. unfold S_dom.
  rewrite dltax1 .
  rewrite ttax1 .
  refine ( isabove_T_T_2 tax0 tax1a _ _ isab ) .

Defined.

  


(** The property StdeltaTt *)


Definition StdeltaTt_type { BB : lBsystem_carrier }
           { T : T_ops_type BB } ( tax0 : T_ax0_type T ) ( tax1a : T_ax1a_type T )
           { dlt : delta_type BB } ( dltax1 : delta_ax1_type T dlt )
           { Tt : Tt_ops_type BB } ( ttax1 : Tt_ax1_type T Tt )
           { St : St_ops_type BB } :=
  forall ( X : BB ) ( r : Tilde BB ) ( gt0 : ll X > 0 ) ( isab : isabove ( dd r ) X ) ,
    St ( dlt X gt0 ) ( Tt X r ( Tt_dom_StdeltaTt_l1 gt0 isab ) )
      ( St_dom_gt0_isab_to_dlt1_Tt1r tax0 tax1a dltax1 ttax1 gt0 isab ) = r . 









(* End of the file lBsystems_units.v *)