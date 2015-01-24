(** * The type of the unital lBsystems

By Vladimir Voevodsky, started on Jan. 18, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_non_unital.
Require Export lBsystems.lBsystems_dlt.


(** The the structure formed by operations dlt *)


Definition dlt_layer_0 ( BB : lBsystem_carrier ) :=
  total2 ( fun dlt : dlt_ops_type BB => dlt_ax0_type dlt ) .

Definition dlt_layer_0_to_dlt_ops_type ( BB : lBsystem_carrier ) :
  dlt_layer_0 BB -> dlt_ops_type BB := pr1 .
Coercion dlt_layer_0_to_dlt_ops_type : dlt_layer_0 >-> dlt_ops_type .



(** The layer associated with operations dlt *)

Definition dlt_layer { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  total2 ( fun dlt : dlt_layer_0 BB => dlt_ax1_type T dlt ) .

Definition dlt_layer_pr1 { BB : lBsystem_carrier }
           ( T : T_ops_type BB )
           ( dlt : dlt_layer T ) : dlt_layer_0 BB := pr1 dlt .
Coercion dlt_layer_pr1 : dlt_layer >-> dlt_layer_0 . 

Definition dlt_ax1 { BB : lBsystem_carrier }
           { T : T_ops_type BB }
           ( dlt : dlt_layer T ) : dlt_ax1_type T dlt := pr2 dlt .


(** Condition dltT *)

Definition dltT { BB : lBsystem_carrier } { T : T_Tt_layer BB } ( dlt : dlt_layer T ) :=
  dltT_type ( T_ax0 T ) ( T_ax1b T ) T ( dlt_ax1 dlt ) . 

(** Condition dltS *)

Definition dltS { BB : lBsystem_carrier } { T : T_layer BB } ( dlt : dlt_layer T )
           ( S : S_St_layer BB ) :=
  dltS_type ( T_ax1b T ) ( S_ax0 S ) S ( dlt_ax1 dlt ) .


(** Condition SdltT *)

Definition SdltT { BB : lBsystem_carrier } { T : T_layer BB } ( dlt : dlt_layer T ) 
           ( S : S_ops_type BB ) :=
  SdltT_type ( T_ax0 T ) ( T_ax1a T ) ( dlt_ax1 dlt ) S .

(** Condition StdltTt *)

Definition StdltTt { BB : lBsystem_carrier } { T : T_Tt_layer BB } ( dlt : dlt_layer T ) 
           ( St : St_ops_type BB ) :=
  StdltTt_type ( T_ax0 T ) ( T_ax1a T ) ( dlt_ax1 dlt ) ( Tt_ax1 T ) St .

(** Condition dltSid *)

Definition dltSid { BB : lBsystem_carrier } { T : T_layer BB } ( dlt : dlt_layer T ) 
           ( St : St_ops_type BB ) :=
  dltSid_type ( T_ax1b T ) ( dlt_ax1 dlt ) St .



(** Packaging dlt and the conditions it needs to satisfy together *)


Definition dlt_and_five { BB : lBsystem_carrier }
           ( T : T_Tt_layer BB ) ( S : S_St_layer BB ) :=
  total2 ( fun dlt : dlt_layer T =>
             dirprod
               ( dirprod
                   ( dirprod ( dltT dlt ) ( dltS dlt S ) )
                   ( dirprod ( SdltT dlt S ) ( StdltTt dlt S ) ) )
               ( dltSid dlt S ) ) .

Definition dlt_and_five_pr1 { BB : lBsystem_carrier }
           ( T : T_Tt_layer BB ) ( S : S_St_layer BB ) :
  dlt_and_five T S -> dlt_layer T := pr1 .
Coercion  dlt_and_five_pr1 : dlt_and_five >-> dlt_layer . 



(** Unital lBsystem *)

Definition lB := total2 ( fun BB : nu_lB => dlt_and_five BB BB ) .

Definition lB_pr1 : lB -> nu_lB := pr1 .
Coercion lB_pr1 : lB >-> nu_lB .

Definition lB_pr2 ( BB : lB ) : dlt_and_five BB BB := pr2 BB .
Coercion lB_pr2 : lB >-> dlt_and_five . 

Definition dltT_ax ( BB : lB ) : dltT BB := pr1 ( pr1 ( pr1 ( pr2 ( pr2 BB ) ) ) ) . 

Definition dltS_ax ( BB : lB ) : dltS BB BB := pr2 ( pr1 ( pr1 ( pr2 ( pr2 BB ) ) ) ) .

Definition SdltT_ax ( BB : lB ) : SdltT BB BB := pr1 ( pr2 ( pr1 ( pr2 ( pr2 BB ) ) ) ) . 

Definition StdltTt_ax ( BB : lB ) : StdltTt BB BB := pr2 ( pr2 ( pr1 ( pr2 ( pr2 BB ) ) ) ) . 

Definition dltSid_ax ( BB : lB ) : dltSid BB BB := pr2 ( pr2 ( pr2 BB ) ) . 














(* End of the file lBsystems_unital.v *)