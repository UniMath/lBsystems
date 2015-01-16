(** * The type of the non-unital lBsystems

By Vladimir Voevodsky, started on Jan. 16, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems_TS_ST.
Require Export lBsystems_STid .


(** The structure formed by operations T *)


Definition T_layer_1 ( BB : lBsystem_carrier ) :=
  total2 ( fun T : T_ops_type BB =>
             dirprod ( T_ax0_type T )
                     ( dirprod ( T_ax1a_type T ) ( T_ax1b_type T ) ) ) .

Definition T_layer_to_T_ops_type ( BB : lBsystem_carrier ) ( T : T_layer_1 BB ) :
  T_ops_type BB := pr1 T .
Coercion T_layer_to_T_ops_type : T_layer_1 >-> T_ops_type .

Definition T_ax0 { BB : lBsystem_carrier } ( T : T_layer_1 BB ) : T_ax0_type T :=
  pr1 ( pr2 T ) .

Definition T_ax1a { BB : lBsystem_carrier } ( T : T_layer_1 BB ) : T_ax1a_type T :=
  pr1 ( pr2 ( pr2 T ) ) .

Definition T_ax1b { BB : lBsystem_carrier } ( T : T_layer_1 BB ) : T_ax1b_type T :=
  pr2 ( pr2 ( pr2 T ) ) .


Definition T_layer_2 ( BB : lBsystem_carrier ) :=
  total2 ( fun T : T_layer_1 BB => TT_type ( T_ax0 T ) ( T_ax1a T ) ( T_ax1b T ) ) .

Definition T_layer_2_to_T_layer_1 ( BB : lBsystem_carrier ) ( T : T_layer_2 BB ) :
  T_layer_1 BB := pr1 T .
Coercion T_layer_2_to_T_layer_1 : T_layer_2 >-> T_layer_1 .

Definition TT_ax { BB : lBsystem_carrier } ( T : T_layer_2 BB ) :
  TT_type ( T_ax0 T ) ( T_ax1a T ) ( T_ax1b T ) := pr2 T . 


(** The structure formed by operations Tt *)


Definition Tt_layer_1 { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  total2 ( fun Tt : Tt_ops_type BB => Tt_ax1_type T Tt ) .

Definition Tt_layer_1_to_Tt_ops_type ( BB : lBsystem_carrier ) ( T : T_ops_type BB )
  ( Tt_compl : Tt_layer_1 T ) : Tt_ops_type BB := pr1 Tt_compl .
Coercion Tt_layer_1_to_Tt_ops_type : Tt_layer_1 >-> Tt_ops_type . 


Definition Tt_ax1 { BB : lBsystem_carrier } { T : T_ops_type BB } ( Tt : Tt_layer_1 T ) :
  Tt_ax1_type T Tt := pr2 Tt .

Definition Tt_layer_2 { BB : lBsystem_carrier } ( T : T_layer_1 BB ) :=
  total2 ( fun Tt : Tt_layer_1 T =>
             TTt_type ( T_ax0 T ) ( T_ax1a T ) ( T_ax1b T ) ( Tt_ax1 Tt ) ) .

Definition Tt_layer_2_to_Tt_layer_1 { BB : lBsystem_carrier } { T : T_layer_1 BB }
           ( Tt : Tt_layer_2 T ) : Tt_layer_1 T := pr1 Tt . 
Coercion Tt_layer_2_to_Tt_layer_1 :  Tt_layer_2 >-> Tt_layer_1 . 



(** The structure formed by operations T and Tt *)

Definition T_Tt_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun T : T_layer_2 BB => Tt_layer_2 T ) . 

Definition T_Tt_layer_to_T_layer_2 ( BB : lBsystem_carrier ) ( TTt : T_Tt_layer BB ) :
  T_layer_2 BB := pr1 TTt .
Coercion T_Tt_layer_to_T_layer_2 : T_Tt_layer >-> T_layer_2 .

Definition T_Tt_layer_to_Tt_layer_2 ( BB : lBsystem_carrier ) ( TTt : T_Tt_layer BB ) :
  Tt_layer_2 TTt := pr2 TTt .
Coercion T_Tt_layer_to_Tt_layer_2 : T_Tt_layer >-> Tt_layer_2 .


(** The structure formed by operations S and St *)

(** Layer 1 for S *)


Definition S_layer_1 ( BB : lBsystem_carrier ) :=
  total2 ( fun S : S_ops_type BB =>
             dirprod ( S_ax0_type S )
                     ( dirprod ( S_ax1a_type S ) ( S_ax1b_type S ) ) ) .

Definition S_layer_to_S_ops_type ( BB : lBsystem_carrier ) ( S : S_layer_1 BB ) :
  S_ops_type BB := pr1 S .
Coercion S_layer_to_S_ops_type : S_layer_1 >-> S_ops_type .

Definition S_ax0 { BB : lBsystem_carrier } ( S : S_layer_1 BB ) : S_ax0_type S :=
  pr1 ( pr2 S ) .

Definition S_ax1a { BB : lBsystem_carrier } ( S : S_layer_1 BB ) : S_ax1a_type S :=
  pr1 ( pr2 ( pr2 S ) ) .

Definition S_ax1b { BB : lBsystem_carrier } ( S : S_layer_1 BB ) : S_ax1b_type S :=
  pr2 ( pr2 ( pr2 S ) ) .

(** Layer 1 for St *)


Definition St_layer_1 { BB : lBsystem_carrier } ( S : S_ops_type BB ) :=
  total2 ( fun St : St_ops_type BB => St_ax1_type S St ) .

Definition St_layer_to_St_ops_type ( BB : lBsystem_carrier ) ( S : S_ops_type BB )
  ( St_compl : St_layer_1 S ) : St_ops_type BB := pr1 St_compl .
Coercion St_layer_to_St_ops_type : St_layer_1 >-> St_ops_type . 


Definition St_ax1 { BB : lBsystem_carrier } { S : S_ops_type BB } ( St : St_layer_1 S ) :
  St_ax1_type S St := pr2 St .


(** Layer 2 for S and St *)



Definition S_St_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun SSt : total2 ( fun S : S_layer_1 BB => St_layer_1 S ) =>
             dirprod
               ( SSt_type
                   ( S_ax0 ( pr1 SSt ) ) ( S_ax1a ( pr1 SSt ) ) ( S_ax1b ( pr1 SSt ) )
                   ( St_ax1 ( pr2 SSt ) ) )
               ( StSt_type ( S_ax0 ( pr1 SSt ) ) ( S_ax1a ( pr1 SSt ) ) ( S_ax1b ( pr1 SSt ) )
                   ( St_ax1 ( pr2 SSt ) ) ) ) . 

Definition S_St_layer_to_S_layer_1 { BB : lBsystem_carrier } ( SSt : S_St_layer BB ) :
  S_layer_1 BB := pr1 ( pr1 SSt ) . 
Coercion S_St_layer_to_S_layer_1 : S_St_layer >-> S_layer_1 . 

Definition S_St_layer_to_St_layer_1 { BB : lBsystem_carrier } ( SSt : S_St_layer BB ) :
  St_layer_1 SSt := pr2 ( pr1 SSt ) . 
Coercion S_St_layer_to_St_layer_1 : S_St_layer >-> St_layer_1 .


Definition SSt_ax { BB : lBsystem_carrier } ( SSt : S_St_layer BB ) :
  SSt_type ( S_ax0 SSt ) ( S_ax1a SSt ) ( S_ax1b SSt )
           ( St_ax1 SSt ) := pr1 ( pr2 SSt ) . 

Definition StSt_ax { BB : lBsystem_carrier } ( SSt : S_St_layer BB ) :
  StSt_type ( S_ax0 SSt ) ( S_ax1a SSt ) ( S_ax1b SSt )
           ( St_ax1 SSt ) := pr2 ( pr2 SSt ) . 


???? need to use level 1 in the next two definitions

(** The layers with axioms TS and ST *)

Definition TS_layer ( BB : lBsystem_carrier )
           ( TTt : T_Tt_layer BB ) ( SSt : S_St_layer BB ) :=
  dirprod
    ( TS_type ( T_ax1b TTt ) ( S_ax0 SSt ) ( S_ax1a SSt ) ( S_ax1b SSt ) )
    ( TtS_type ( T_ax1b TTt ) ( Tt_ax1 TTt ) ( S_ax0 SSt ) ( S_ax1a SSt ) ( S_ax1b SSt )
               ( St_ax1 SSt ) ) .


Definition STt_layer ( BB : lBsystem_carrier )
           ( TTt : T_Tt_layer BB ) ( SSt : S_St_layer BB ) :=
  dirprod
    ( STt_type ( T_ax0 TTt ) ( T_ax1a TTt ) ( Tt_ax1 TTt ) ( S_ax1b SSt ) )
    ( StTt_type ( T_ax0 TTt ) ( T_ax1a TTt ) ( Tt_ax1 TTt )  ( S_ax1b SSt ) ( St_ax1 SSt ) ) .


(** The layer with axioms STid *) 


Definition STid_layer ( BB : lBsystem_carrier )
           ( T : T_Tt_layer BB ) ( Tt : Tt_layer_1 T )
           ( S : S_ops_type BB ) ( St : St_ops_type BB ) :=
  dirprod
    ( STid_type ( T_ax1b T ) S )
    ( StTtid_type ( T_ax1b T ) ( Tt_ax1 Tt ) St ) .



(** Complete non-unital lBsystem *)

Definition nu_lB := total2 ( fun BB : lBsystem_carrier =>
                               dirprod
                                 ( total2 ( fun T : T_layer_1 BB => 






(* End of the file lBsystems_non_unital.v *) 