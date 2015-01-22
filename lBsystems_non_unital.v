(** * The type of the non-unital lBsystems

By Vladimir Voevodsky, started on Jan. 16, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_TS_ST.
Require Export lBsystems.lBsystems_STid .


(** The structure formed by operations T *)


Definition T_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun T : T_ops_type BB =>
             dirprod ( T_ax0_type T )
                     ( dirprod ( T_ax1a_type T ) ( T_ax1b_type T ) ) ) .

Definition T_layer_to_T_ops_type ( BB : lBsystem_carrier ) ( T : T_layer BB ) :
  T_ops_type BB := pr1 T .
Coercion T_layer_to_T_ops_type : T_layer >-> T_ops_type .



Definition T_ax0 { BB : lBsystem_carrier } ( T : T_layer BB ) : T_ax0_type T :=
  pr1 ( pr2 T ) .

Definition T_ax1a { BB : lBsystem_carrier } ( T : T_layer BB ) : T_ax1a_type T :=
  pr1 ( pr2 ( pr2 T ) ) .

Definition T_ax1b { BB : lBsystem_carrier } ( T : T_layer BB ) : T_ax1b_type T :=
  pr2 ( pr2 ( pr2 T ) ) .




(** The structure formed by operations Tt *)


Definition Tt_layer { BB : lBsystem_carrier } ( T : T_ops_type BB ) :=
  total2 ( fun Tt : Tt_ops_type BB => Tt_ax1_type T Tt ) .

Definition Tt_layer_to_Tt_ops_type ( BB : lBsystem_carrier ) ( T : T_ops_type BB )
  ( Tt_compl : Tt_layer T ) : Tt_ops_type BB := pr1 Tt_compl .
Coercion Tt_layer_to_Tt_ops_type : Tt_layer >-> Tt_ops_type . 


Definition Tt_ax1 { BB : lBsystem_carrier } { T : T_ops_type BB } ( Tt : Tt_layer T ) :
  Tt_ax1_type T Tt := pr2 Tt .


(** The structure formed by operations T and Tt *)

Definition T_Tt_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun T : T_layer BB => Tt_layer T ) .

Definition T_Tt_layer_to_T_layer { BB : lBsystem_carrier } ( T_Tt : T_Tt_layer BB ) :
  T_layer BB := pr1 T_Tt .
Coercion T_Tt_layer_to_T_layer : T_Tt_layer >->  T_layer .

Definition T_Tt_layer_to_Tt_layer { BB : lBsystem_carrier } ( T_Tt : T_Tt_layer BB ) :
  Tt_layer T_Tt := pr2 T_Tt .
Coercion T_Tt_layer_to_Tt_layer : T_Tt_layer >-> Tt_layer .  




(** Condition TT *)


Definition TT { BB : lBsystem_carrier } ( T : T_layer BB ) :=
  TT_type ( T_ax0 T ) ( T_ax1a T ) ( T_ax1b T ) .



(** Condition TTt *)


Definition TTt { BB : lBsystem_carrier } ( T : T_layer BB ) ( Tt : Tt_layer T ) :=
  TTt_type ( T_ax0 T ) ( T_ax1a T ) ( T_ax1b T ) ( Tt_ax1 Tt ) .




(** The structure formed by operations T, Tt and conditions TT, TTt *)


Definition TT_TTt_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun T_Tt : T_Tt_layer BB =>
             dirprod ( TT T_Tt ) ( TTt T_Tt T_Tt ) ) . 

          
Definition TT_TTt_layer_to_T_Tt_layer ( BB : lBsystem_carrier ) ( T : TT_TTt_layer BB ) :
  T_Tt_layer BB := pr1 T .
Coercion TT_TTt_layer_to_T_Tt_layer : TT_TTt_layer >-> T_Tt_layer .

Definition TT_ax { BB : lBsystem_carrier } ( T : TT_TTt_layer BB ) :
  TT T := pr1 ( pr2 T ) .

Definition TTt_ax { BB : lBsystem_carrier } ( T : TT_TTt_layer BB ) :
  TTt T T := pr2 ( pr2 T ) .



(** The structure formed by operations S *)


Definition S_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun S : S_ops_type BB =>
             dirprod ( S_ax0_type S )
                     ( dirprod ( S_ax1a_type S ) ( S_ax1b_type S ) ) ) .

Definition S_layer_to_S_ops_type ( BB : lBsystem_carrier ) ( S : S_layer BB ) :
  S_ops_type BB := pr1 S .
Coercion S_layer_to_S_ops_type : S_layer >-> S_ops_type .

Definition S_ax0 { BB : lBsystem_carrier } ( S : S_layer BB ) : S_ax0_type S :=
  pr1 ( pr2 S ) .

Definition S_ax1a { BB : lBsystem_carrier } ( S : S_layer BB ) : S_ax1a_type S :=
  pr1 ( pr2 ( pr2 S ) ) .

Definition S_ax1b { BB : lBsystem_carrier } ( S : S_layer BB ) : S_ax1b_type S :=
  pr2 ( pr2 ( pr2 S ) ) .


(** The structure formed by operations St *)


Definition St_layer { BB : lBsystem_carrier } ( S : S_ops_type BB ) :=
  total2 ( fun St : St_ops_type BB => St_ax1_type S St ) .

Definition St_layer_to_St_ops_type ( BB : lBsystem_carrier ) ( S : S_ops_type BB )
  ( St_compl : St_layer S ) : St_ops_type BB := pr1 St_compl .
Coercion St_layer_to_St_ops_type : St_layer >-> St_ops_type . 


Definition St_ax1 { BB : lBsystem_carrier } { S : S_ops_type BB } ( St : St_layer S ) :
  St_ax1_type S St := pr2 St .


(** The structure formed by operations S and St *)

Definition S_St_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun S : S_layer BB => St_layer S ) .

Definition S_St_layer_to_S_layer { BB : lBsystem_carrier } ( S_St : S_St_layer BB ) :
  S_layer BB := pr1 S_St .
Coercion S_St_layer_to_S_layer : S_St_layer >->  S_layer .

Definition S_St_layer_to_St_layer { BB : lBsystem_carrier } ( S_St : S_St_layer BB ) :
  St_layer S_St := pr2 S_St .
Coercion S_St_layer_to_St_layer : S_St_layer >-> St_layer .  



(** Condition SSt *)

Definition SSt { BB : lBsystem_carrier } ( S : S_St_layer BB ) :=
  SSt_type ( S_ax0 S ) ( S_ax1a S ) ( S_ax1b S ) ( St_ax1 S ) .


(** Condition StSt *)

Definition StSt { BB : lBsystem_carrier } ( S : S_St_layer BB ) :=
  StSt_type ( S_ax0 S ) ( S_ax1a S ) ( S_ax1b S ) ( St_ax1 S ) .


(** The structure formed by operations S, St and conditions SSt, SSt *)


Definition SSt_StSt_layer ( BB : lBsystem_carrier ) :=
  total2 ( fun S_St : S_St_layer BB =>
             dirprod ( SSt S_St ) ( StSt S_St ) ) . 

          
Definition SSt_SSt_layer_to_S_St_layer ( BB : lBsystem_carrier ) ( S : SSt_StSt_layer BB ) :
  S_St_layer BB := pr1 S .
Coercion SSt_SSt_layer_to_S_St_layer : SSt_StSt_layer >-> S_St_layer .

Definition SSt_ax { BB : lBsystem_carrier } ( S : SSt_StSt_layer BB ) :
  SSt S := pr1 ( pr2 S ) .

Definition StSt_ax { BB : lBsystem_carrier } ( S : SSt_StSt_layer BB ) :
  StSt S := pr2 ( pr2 S ) .


(** Conditions TS and TtS *)

Definition TS { BB : lBsystem_carrier } ( T : T_layer BB ) ( S : S_layer BB ) :=
  TS_type ( T_ax1b T ) ( S_ax0 S ) ( S_ax1a S ) ( S_ax1b S ) .

Definition TtS { BB : lBsystem_carrier } ( T : T_Tt_layer BB ) ( S : S_St_layer BB ) :=
  TtS_type ( T_ax1b T ) ( Tt_ax1 T ) ( S_ax0 S ) ( S_ax1a S ) ( S_ax1b S ) ( St_ax1 S ) .


(** Conditions STt and StTt *)

Definition STt { BB : lBsystem_carrier } ( T : T_Tt_layer BB ) ( S : S_layer BB ) :=
  STt_type ( T_ax0 T ) ( T_ax1a T ) ( Tt_ax1 T ) ( S_ax1b S ) . 


Definition StTt { BB : lBsystem_carrier } ( T : T_Tt_layer BB ) ( S : S_St_layer BB ) :=
  StTt_type ( T_ax0 T ) ( T_ax1a T ) ( Tt_ax1 T )  ( S_ax1b S ) ( St_ax1 S ) .


(** Conditions STid and StTtid *) 


Definition STid { BB : lBsystem_carrier } ( T : T_layer BB ) ( S : S_ops_type BB ) :=
  STid_type ( T_ax1b T ) S . 


Definition StTtid { BB : lBsystem_carrier } ( T : T_Tt_layer BB ) ( St : St_ops_type BB ) :=
  StTtid_type ( T_ax1b T ) ( Tt_ax1 T ) St .  




(** Complete non-unital lBsystem *)

Definition lB_int ( BB : lBsystem_carrier ) := dirprod ( TT_TTt_layer BB ) ( SSt_StSt_layer BB ) .

Definition lB_int_pr1 ( BB : lBsystem_carrier ) ( Ops : lB_int BB ) := pr1 Ops .
Coercion lB_int_pr1 : lB_int >-> TT_TTt_layer . 

Definition lB_int_pr2 ( BB : lBsystem_carrier ) ( Ops : lB_int BB ) := pr2 Ops .
Coercion lB_int_pr2 : lB_int >-> SSt_StSt_layer . 

Definition nu_lB := total2 ( fun BB : lBsystem_carrier =>
                               total2 ( fun X : lB_int BB =>
                                          dirprod
                                              ( dirprod
                                                ( dirprod ( TS X X ) ( TtS X X ) )
                                                ( dirprod ( STt X X ) ( StTt X X ) ) )
                                              ( dirprod ( STid X X ) ( StTtid X X ) ) ) ) .

Definition nu_lB_pr1 : nu_lB -> lBsystem_carrier := pr1 .
Coercion nu_lB_pr1 : nu_lB >-> lBsystem_carrier .

Definition nu_lB_pr2 ( BB : nu_lB ) : lB_int BB := pr1 ( pr2 BB )  .  
Coercion nu_lB_pr2 : nu_lB >-> lB_int .

Definition TS_ax ( BB : nu_lB ) : TS BB BB := pr1 ( pr1 ( pr1 ( pr2 ( pr2 BB ) ) ) ) .  

Definition TtS_ax ( BB : nu_lB ) : TtS BB BB := pr2 ( pr1 ( pr1 ( pr2 ( pr2 BB ) ) ) ) .  

Definition STt_ax ( BB : nu_lB ) : STt BB BB := pr1 ( pr2 ( pr1 ( pr2 ( pr2 BB ) ) ) ) .  

Definition StTt_ax ( BB : nu_lB ) : StTt BB BB := pr2 ( pr2 ( pr1 ( pr2 ( pr2 BB ) ) ) ) .  

Definition STid_ax ( BB : nu_lB ) : STid BB BB := pr1 ( pr2 ( pr2 ( pr2 BB ) ) )  .  

Definition StTtid_ax ( BB : nu_lB ) : StTtid BB BB := pr2 ( pr2 ( pr2 ( pr2 BB ) ) )  .  





(* End of the file lBsystems_non_unital.v *) 