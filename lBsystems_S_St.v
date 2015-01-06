(** * Operations S and St on carriers of lB-systems and 
their properties SSt and StSt .

by Vladimir Voevodsky, file created on Jan. 6, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems_T_Tt.






(* **** Operation(s) S  

Note: both the domain of definition of operations S and the type of the axiom 1a of operations 
S are obtainable from the same for operations T by removing the condition T_dom_gt0 and 
replacing ( ft X1 ) by ( dd r ). This leads to the possibility of almost direct copy-and_paste
of many proofs concerning T into the context of S. 

Operations T and S are different in the forms of axiom 0 and axiom 1b . 

*)

(** Domains of definition of operations of type S *)


Definition S_dom { BB : lBsystem_carrier } ( r : Tilde BB ) ( Y : BB ) :=
  isabove Y ( dd r ) .

Definition S_dom_gth { BB : lBsystem_carrier } { r : Tilde BB } { Y : BB } ( inn : S_dom r Y ) :
  ll Y > 0 .
Proof .
  intros .  exact ( istransnatgth _ _ _ ( isabove_gth inn ) ( ll_dd _ ) )  . 

Defined.

Definition S_dom_geh { BB : lBsystem_carrier } { r : Tilde BB } { Y : BB } ( inn : S_dom r Y ) :
  ll Y >= 1 .
Proof .
  intros .  exact ( natgthtogehsn _ _ ( S_dom_gth inn ) ) . 

Defined.


Lemma isaprop_S_dom { BB : lBsystem_carrier } ( r : Tilde BB ) ( Y : BB ) :
  isaprop ( S_dom r Y ) . 
Proof.
  intros . apply isaprop_isabove . 
Defined.


Lemma noparts_S_dom { BB : lBsystem_carrier } { r : Tilde BB } { Y : BB }
      ( inn1 inn2 : S_dom r Y ) : inn1 = inn2 .
Proof .
  intros . apply ( proofirrelevance _ ( isaprop_S_dom r Y ) ) .
Defined .  


(** The type objects of which are candidates for operations S on an lB-system. *)
 

Definition S_ops_type ( BB : lBsystem_carrier ) :=
  forall ( r : Tilde BB ) ( Y : BB ) ( inn : S_dom r Y ) , BB .

Lemma S_equals_2 { BB : lBsystem_carrier } { r : Tilde BB } { Y Y' : BB } ( S : S_ops_type BB )
      ( eq : Y = Y' ) ( inn : S_dom r Y ) ( inn' : S_dom r Y' )  :
  S r Y inn = S r Y' inn' .
Proof.
  intros BB r Y Y' S eq .
  rewrite eq . 
  intros . rewrite ( noparts_S_dom inn inn' ) . 
  apply idpath . 

Defined.



(** The zeros property (later an axiom) of an operation of type S *)

Definition S_ax0_type { BB : lBsystem_carrier } ( S : S_ops_type BB ) :=
  forall ( r : Tilde BB ) ( Y : BB ) ( inn : S_dom r Y ) , ( ll ( S r Y inn ) ) = ( ll Y ) - 1 .

(** The first property (later an axiom) of an operation of type S *)

Definition S_ax1a_type { BB : lBsystem_carrier } ( S : S_ops_type BB ) :=
  forall ( r : Tilde BB ) ( Y : BB ) ( inn : S_dom r Y ) ( isab : isabove ( ft Y ) ( dd r ) ) ,
    ft ( S r Y inn ) = S r ( ft Y ) isab . 

Definition S_ax1b_type { BB : lBsystem_carrier } ( S : S_ops_type BB ) :=
  forall ( r : Tilde BB ) ( Y : BB ) ( inn : S_dom r Y ) ,
    isabove ( S r Y inn ) ( ft ( dd r ) ) .




(** The computation of the iterated ft of ( S r Y ) .  *)
          
Lemma ftn_S { BB : lBsystem_carrier } { S : S_ops_type BB } ( ax1a : S_ax1a_type S )
      ( n : nat ) { r : Tilde BB } { Y : BB } ( isab : isabove ( ftn n Y ) ( dd r ) )
      ( inn : S_dom r Y ) :
  ftn n ( S r Y inn ) = S r ( ftn n Y ) isab .
Proof .
  intros BB S ax1a n . induction n as [ | n IHn ] .
  intros .
  rewrite ( noparts_S_dom inn isab ) . 
  apply idpath . 

  intros .
  change ( ftn (Datatypes.S n) (S r Y inn) ) with ( ft ( ftn n (S r Y inn) ) ) .
  assert ( isab' : isabove ( ftn n Y ) ( dd r ) ) .
  exact ( isabove_ft_inv isab ) . 
  
  rewrite ( IHn r Y isab' inn ) . 
  refine ( ax1a _ _ _ _ ) . 

Defined.

Lemma ft_S { BB : lBsystem_carrier } { S : S_ops_type BB } { r : Tilde BB } { Y : BB }
      ( ax0 : S_ax0_type S ) ( ax1b : S_ax1b_type S ) ( iseq : ft Y = dd r )
      ( inn : S_dom r Y ) : ft ( S r Y inn ) = ft ( dd r ) .
Proof.
  intros .
  assert ( isov := ax1b r Y inn : isover ( S r Y inn ) ( ft ( dd r ) ) ) .
  unfold isover in isov . 
  rewrite ll_ft in isov .  rewrite ax0 in isov . rewrite <- ll_ft  in isov .
  rewrite iseq in isov . 
  assert ( int : (ll (dd r) - (ll (dd r) - 1)) = 1 ) . refine ( natminusmmk _ ) .
  exact ( natgthtogehsn _ _ ( ll_dd _ ) ) .

  rewrite int in isov . 
  exact ( ! isov ) . 

Defined.

Lemma isover_S_S_2 { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 :  S_ax0_type S ) ( ax1a : S_ax1a_type S )
      { r : Tilde BB } { Y Y' : BB } ( inn : S_dom r Y ) ( inn' : S_dom r Y' )
      ( is : isover Y Y' ) : isover ( S r Y inn ) ( S r Y' inn' ) .
Proof .
  intros . 
  unfold isover in * .
  repeat rewrite ax0 .
  simpl .
  assert ( isab : isabove ( ftn ( ll Y - ll Y') Y ) ( dd r ) ) .
  rewrite <- is . 
  exact inn' . 

  rewrite ( natmiusmius1mminus1 ( S_dom_gth inn ) ( S_dom_gth inn' ) ) . 
  rewrite ( ftn_S ax1a _ isab inn ) .
  exact ( S_equals_2 _ is _ _ ) . 

Defined.


Lemma isabove_S_S_2 { BB : lBsystem_carrier }
      { S : S_ops_type BB } ( ax0 :  S_ax0_type S ) ( ax1a : S_ax1a_type S )
      { r : Tilde BB } { Y Y' : BB } ( inn : S_dom r Y ) ( inn' : S_dom r Y' )
      ( is : isabove Y Y' ) : isabove ( S r Y inn ) ( S r Y' inn' ) .
Proof .
  intros .
  refine ( isabove_constr _ _ ) .
  repeat rewrite ax0 .
  refine ( natgthandminusinvr _ _ ) .
  exact ( isabove_gth is ) .

  exact ( S_dom_geh inn' ) . 

  exact ( isover_S_S_2 ax0 ax1a _ _ is ) . 

Defined.


  













(** **** Operation(s) St  *)


(** Domains of definition of operations of type St *)


Definition St_dom { BB : lBsystem_carrier } ( r : Tilde BB ) ( s : Tilde BB ) :=
  S_dom r ( dd s ) . 


(** The type objects of which are candidates for operations St on an lB-system. *)
 

Definition St_ops_type ( BB : lBsystem_carrier ) :=
  forall ( r : Tilde BB ) ( s : Tilde BB ) ( inn : St_dom r s ) , Tilde BB .


(** The first property (later an axiom) of an operation of type St *)


Definition St_ax1_type { BB : lBsystem_carrier } ( S : S_ops_type BB )
           ( St : St_ops_type BB ) := 
  forall ( r : Tilde BB ) ( s : Tilde BB ) ( inn : St_dom r s ) ,
    ft ( dd ( St r s inn ) ) = S r ( dd s ) inn .




(** Two implications of the zeros and first properties of operations of type S and St
that are required for the formulation of the properties SS and SSt *) 










(* End of the file lBsystems_S_St.v *)