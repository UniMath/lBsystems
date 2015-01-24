(** ** Pre-lB-systems 

By Vladimir Voevodsky, started on Jan. 24, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_T_Tt.
Require Export lBsystems.lBsystems_S_St .
Require Export lBsystems.lBsystems_dlt . 


(** *** Non-unital pre-lB-systems *) 

(** **** The structure formed by operations T *)

Definition T_layer_0 ( BB : lBsystem_carrier ) :=
  total2 ( fun T : T_ops_type BB =>  T_ax0_type T ) .

Definition T_layer_0_to_T_ops_type ( BB : lBsystem_carrier ) ( T : T_layer_0 BB ) :
  T_ops_type BB := pr1 T .
Coercion T_layer_0_to_T_ops_type : T_layer_0 >-> T_ops_type .

Definition T_ax0 { BB : lBsystem_carrier } ( T : T_layer_0 BB ) : T_ax0_type T :=
  pr2 T .

(** **** The structure formed by operations Tt *)

Definition Tt_layer_0 ( BB : lBsystem_carrier ) :=
  total2 ( fun Tt : Tt_ops_type BB => Tt_ax0_type Tt ) .

Definition Tt_layer_0_to_Tt_ops_type ( BB : lBsystem_carrier ) :
  Tt_layer_0 BB -> Tt_ops_type BB := pr1 .
Coercion Tt_layer_0_to_Tt_ops_type : Tt_layer_0 >-> Tt_ops_type .

Definition Tt_ax0 { BB : lBsystem_carrier } ( Tt : Tt_layer_0 BB ) : Tt_ax0_type Tt :=
  pr2 Tt .


(** **** The structure formed by operations S *)


Definition S_layer_0 ( BB : lBsystem_carrier ) :=
  total2 ( fun S : S_ops_type BB => S_ax0_type S ) .

Definition S_layer_0_to_S_ops_type { BB : lBsystem_carrier } ( S : S_layer_0 BB ) :
  S_ops_type BB := pr1 S .
Coercion S_layer_0_to_S_ops_type : S_layer_0 >-> S_ops_type .


Definition S_ax0 { BB : lBsystem_carrier } ( S : S_layer_0 BB ) : S_ax0_type S :=
  pr2 S .


(** **** The structure formed by operations St *)


Definition St_layer_0 ( BB : lBsystem_carrier ) :=
  total2 ( fun St : St_ops_type BB => St_ax0_type St ) .

Definition St_layer_0_to_St_ops_type ( BB : lBsystem_carrier ) :
  St_layer_0 BB -> St_ops_type BB := pr1 .
Coercion St_layer_0_to_St_ops_type : St_layer_0 >-> St_ops_type .



(** **** Complete definition of a non-unital pre-lB-system *)

Definition prelBsystem_non_unital :=
  total2 ( fun BB : lBsystem_carrier =>
             dirprod
               ( dirprod ( T_layer_0 BB ) ( Tt_layer_0 BB ) )
               ( dirprod ( S_layer_0 BB ) ( St_layer_0 BB ) ) ) .

Definition prelBsystem_non_unital_pr1 : prelBsystem_non_unital -> lBsystem_carrier := pr1 .
Coercion  prelBsystem_non_unital_pr1 : prelBsystem_non_unital >-> lBsystem_carrier .                                              
Definition T_op ( BB : prelBsystem_non_unital ) : T_ops_type BB := pr1 ( pr1 ( pr2 BB ) ) . 

Definition Tt_op ( BB : prelBsystem_non_unital ) : Tt_ops_type BB := pr2 ( pr1 ( pr2 BB ) ) . 

Definition S_op ( BB : prelBsystem_non_unital ) : S_ops_type BB := pr1 ( pr2 ( pr2 BB ) ) . 

Definition St_op ( BB : prelBsystem_non_unital ) : St_ops_type BB := pr2 ( pr2 ( pr2 BB ) ) . 






(** *** Unital pre-lB-systems *)

(** **** The structure formed by operations dlt *)


Definition dlt_layer_0 ( BB : lBsystem_carrier ) :=
  total2 ( fun dlt : dlt_ops_type BB => dlt_ax0_type dlt ) .

Definition dlt_layer_0_to_dlt_ops_type ( BB : lBsystem_carrier ) :
  dlt_layer_0 BB -> dlt_ops_type BB := pr1 .
Coercion dlt_layer_0_to_dlt_ops_type : dlt_layer_0 >-> dlt_ops_type .


(** **** Complete definition of a (unital) pre-lB-system *)


Definition prelBsystem :=
  total2 ( fun BB : prelBsystem_non_unital => dlt_layer_0 BB ) .

Definition prelBsystem_pr1 : prelBsystem -> prelBsystem_non_unital := pr1 . 
Coercion prelBsystem_pr1 : prelBsystem >-> prelBsystem_non_unital . 

Definition dlt_op ( BB : prelBsystem ) : dlt_ops_type BB := pr2 BB . 









(* End of the file prelBsystems.v *)