(** ** lB0-systems

By Vladimir Voevodsky, started on Jan. 24, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.prelBsystems. 
Require Export lBsystems.lBsystems_TS_ST.
Require Export lBsystems.lBsystems_STid .
Require Export lBsystems.lBsystems_dlt . 




(** ** lB0-systems *)

(** *** Non-unital lB0-systems *)

(** **** The layer associated with operations T *)

Definition T_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun T : T_layer_0 BB => dirprod ( T_ax1a_type T ) ( T_ax1b_type T ) ) .

Definition T_layer_to_T_layer_0 ( BB : lBsystem_carrier ) : T_layer BB -> T_layer_0 BB :=
  pr1 . 
Coercion T_layer_to_T_layer_0 : T_layer >-> T_layer_0 . 
 
Definition T_ax1a { BB : lBsystem_carrier } ( T : T_layer BB ) : T_ax1a_type T :=
  pr1 ( pr2 T ) .

Definition T_ax1b { BB : lBsystem_carrier } ( T : T_layer BB ) : T_ax1b_type T :=
  pr2 ( pr2 T ) .


(** **** The layer associated with operations Tt *)


Definition Tt_layer { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  total2 ( fun Tt : Tt_ops_type BB => Tt_ax1_type T Tt ) .

Definition Tt_layer_to_Tt_ops_type ( BB : lBsystem_carrier ) ( T : T_ops_type BB )
  ( Tt : Tt_layer T ) : Tt_ops_type BB := pr1 Tt .
Coercion Tt_layer_to_Tt_ops_type : Tt_layer >-> Tt_ops_type . 


Definition Tt_ax1 { BB : lBsystem_carrier } { T : T_ops_type BB } ( Tt : Tt_layer T ) :
  Tt_ax1_type T Tt := pr2 Tt .


(** **** The structure formed by operations T and Tt *)

Definition T_Tt_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun T : T_layer BB => Tt_layer T ) .

Definition T_Tt_layer_to_T_layer { BB : lBsystem_carrier } ( T_Tt : T_Tt_layer BB ) :
  T_layer BB := pr1 T_Tt .
Coercion T_Tt_layer_to_T_layer : T_Tt_layer >->  T_layer .

Definition T_Tt_layer_to_Tt_layer { BB : lBsystem_carrier } ( T_Tt : T_Tt_layer BB ) :
  Tt_layer T_Tt := pr2 T_Tt .
Coercion T_Tt_layer_to_Tt_layer : T_Tt_layer >-> Tt_layer .  


(** **** The layer associated with operations S *)


Definition S_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun S : S_layer_0 BB =>  dirprod ( S_ax1a_type S ) ( S_ax1b_type S ) ) .

Definition S_layer_to_S_layer_0 ( BB : lBsystem_carrier ) :
  S_layer BB -> S_layer_0 BB := pr1 .
Coercion S_layer_to_S_layer_0 : S_layer >-> S_layer_0 . 

Definition S_ax1a { BB : lBsystem_carrier } ( S : S_layer BB ) : S_ax1a_type S :=
  pr1 ( pr2 S ) .

Definition S_ax1b { BB : lBsystem_carrier } ( S : S_layer BB ) : S_ax1b_type S :=
  pr2 ( pr2 S ) .


(** **** The layer associated with operations St *)


(* Definition St_layer { BB : lBsystem_carrier } ( S : S_ops_type BB ) :=
  total2 ( fun St : St_layer_0 BB => St_ax1_type S St ) .

Definition St_layer_to_St_layer_0 ( BB : lBsystem_carrier ) ( S : S_ops_type BB )
  ( St : St_layer S ) : St_layer_0 BB := pr1 St.
Coercion St_layer_to_St_layer_0 : St_layer >-> St_layer_0 . *)

Definition St_layer { BB : lBsystem_carrier } ( S : S_ops_type BB ) :=
  total2 ( fun St : St_ops_type BB => St_ax1_type S St ) .

Definition St_layer_to_St_ops_type ( BB : lBsystem_carrier ) ( S : S_ops_type BB )
  ( St : St_layer S ) : St_ops_type BB := pr1 St.
Coercion St_layer_to_St_ops_type : St_layer >-> St_ops_type .


Definition St_ax1 { BB : lBsystem_carrier } { S : S_ops_type BB } ( St : St_layer S ) :
  St_ax1_type S St := pr2 St .


(** **** The structure formed by operations S and St *)

Definition S_St_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun S : S_layer BB => St_layer S ) .

Definition S_St_layer_to_S_layer { BB : lBsystem_carrier } ( S_St : S_St_layer BB ) :
  S_layer BB := pr1 S_St .
Coercion S_St_layer_to_S_layer : S_St_layer >->  S_layer .

Definition S_St_layer_to_St_layer { BB : lBsystem_carrier } ( S_St : S_St_layer BB ) :
  St_layer S_St := pr2 S_St .
Coercion S_St_layer_to_St_layer : S_St_layer >-> St_layer .  


(** **** Complete definition of a non-unital lB0-system *)

Definition T_ax1_type ( BB : prelBsystem_non_unital ) :=
  dirprod ( T_ax1a_type ( T_op BB ) ) ( T_ax1b_type ( T_op BB ) ) .

Definition Tt_ax1_type' ( BB : prelBsystem_non_unital ) :=
  Tt_ax1_type ( T_op BB ) ( Tt_op BB ) .

Definition S_ax1_type ( BB : prelBsystem_non_unital ) :=
  dirprod ( S_ax1a_type ( S_op BB ) ) ( S_ax1b_type ( S_op BB ) ) .

Definition St_ax1_type' ( BB : prelBsystem_non_unital ) :=
  St_ax1_type ( S_op BB ) ( St_op BB ) .

Definition lB0system_non_unital :=
  total2 ( fun BB : prelBsystem_non_unital =>
             dirprod
               ( dirprod ( T_ax1_type BB ) ( Tt_ax1_type' BB ) )
               ( dirprod ( S_ax1_type BB ) ( St_ax1_type' BB ) ) ) . 

Definition lB0system_non_unital_pr1 : lB0system_non_unital -> prelBsystem_non_unital := pr1 .
Coercion lB0system_non_unital_pr1 : lB0system_non_unital >-> prelBsystem_non_unital .


(** *** Unital lB0-systems *)


(** **** The layer associated with operations dlt *)

Definition dlt_layer { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  total2 ( fun dlt : dlt_layer_0 BB => dlt_ax1_type T dlt ) .

Definition dlt_layer_pr1 { BB : lBsystem_carrier }
           ( T : T_ops_type BB )
           ( dlt : dlt_layer T ) : dlt_layer_0 BB := pr1 dlt .
Coercion dlt_layer_pr1 : dlt_layer >-> dlt_layer_0 . 

Definition dlt_ax1 { BB : lBsystem_carrier }
           { T : T_ops_type BB }
           ( dlt : dlt_layer T ) : dlt_ax1_type T dlt := pr2 dlt .



(** **** Complete definition of a unital lB0-system *)


Definition lB0system :=
  total2 ( fun BB : lB0system_non_unital => dlt_layer ( T_op BB ) ) .

Definition lB0system_pr1 : lB0system -> lB0system_non_unital := pr1 .
Coercion lB0system_pr1 : lB0system >-> lB0system_non_unital . 




(* End of the file lB0systems.v *)

