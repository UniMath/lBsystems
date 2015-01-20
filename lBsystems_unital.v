(** * The type of the unital lBsystems

By Vladimir Voevodsky, started on Jan. 18, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems_non_unital.
Require Export lBsystems_dlt.


(** The the structure formed by operations dlt and their elementary properties *)

Definition dlt_layer { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  total2 ( fun dlt : dlt_type BB => dlt_ax1_type T dlt ) .

Definition dlt_layer_pr1 { BB : lBsystem_carrier } ( T : T_ops_type BB )
           ( dlt : dlt_layer T ) : dlt_type BB := pr1 dlt .
Coercion dlt_layer_pr1 : dlt_layer >-> dlt_type . 

Definition dlt_ax1 { BB : lBsystem_carrier } { T : T_ops_type BB } ( dlt : dlt_layer T ) :
  dlt_ax1_type T dlt := pr2 dlt .


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



(** Packaging dlt and the conditions it need to satisfy together *)


Definition dlt_and_five { BB : lBsystem_carrier }
           ( T : T_Tt_layer BB ) ( S : S_St_layer BB ) :=
  total2 ( fun dlt : dlt_layer T =>
             dirprod
               ( dirprod
                   ( dirprod ( dltT dlt ) ( dltS dlt S ) )
                   ( dirprod ( SdltT dlt S ) ( StdltTt dlt S ) ) )
               ( dltSid dlt S ) ) .






(** Complete unital lBsystem *)

Definition lB := total2 ( fun BB : nu_lB => dlt_and_five BB BB ) . 









(* End of the file lBsystems_unital.v *)