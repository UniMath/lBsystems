(** ** lC_to_lB0_systems by Vladimir Voevodsky,

started Feb. 15, 2015, renamed Fe. 21, 2015 

We refer below to the paper "Subsystems and regular quotients of C-systems"
by V. Voevodsky as "Csubsystems".

 *)


Require Export lCsystems.lCsystems.
Require Export lBsystems.lBsystems.

Unset Automatic Introduction.

(** *** Constructing the lB-system carrier *)

Definition Tilde_from_C ( CC : ltower_precat_and_p ) :=
  total2 ( fun X : CC => dirprod ( ll X > 0 ) ( Ob_tilde_over X ) ) .


Lemma isaset_Tilde_from_C ( CC : lC0system ) : isaset ( Tilde_from_C CC ) .
Proof.
  intros . set ( is1 := C0_has_homsets CC ) . set ( is2 := C0_isaset_Ob CC ) .  
  apply ( isofhleveltotal2 2 ) . 
  apply is2 . 

  intro X . 
  unfold Ob_tilde_over .
  apply ( isofhleveltotal2 2 ) .

  apply isasetaprop .
  apply ( pr2 ( ll X > 0 ) ) . 

  intro . 
  apply ( isofhleveltotal2 2 ) . 

  apply is1  .

  intro Y .
  apply isasetaprop . 
  apply is1 . 

Defined.

  

Definition dd_from_C { CC : ltower_precat_and_p } ( r : Tilde_from_C CC ) : CC :=
  pr1 r .

Definition ll_dd_from_C { CC : ltower_precat_and_p } ( r : Tilde_from_C CC ) :
  ll ( dd_from_C r ) > 0 := pr1 ( pr2 r ) . 


Definition Tilde_from_C_to_Ob_tilde_over { CC : ltower_precat_and_p } ( r : Tilde_from_C CC ) :
  Ob_tilde_over ( dd_from_C r ) := pr2 ( pr2 r ) .
Coercion Tilde_from_C_to_Ob_tilde_over : Tilde_from_C >-> Ob_tilde_over . 




Definition B_carrier_from_C ( CC : lC0system ) : lBsystem_carrier .
Proof .
  intros .  
  refine ( lBsystem_carrier_constr _ _ ) . 
  refine ( hSet_pltower_constr _ _ ) .
  apply ( hSet_ltower_constr CC ( C0_isaset_Ob CC ) ) . 

  apply ( ispointed CC ) . 

  apply ( tpair _ _ ( isaset_Tilde_from_C CC ) ) . 

  apply dd_from_C . 

  intro r . simpl in r .
  apply ( pr1 ( pr2 r ) ) . 

Defined.


(** *** Operation T *)

(** **** Constructing operation T *)

Definition T_from_C ( CC : lC0system ) : T_ops_type ( B_carrier_from_C CC ) . 
Proof.
  intros.
  unfold T_ops_type . 
  intros X1 X2 inn .
  set ( f := pX X1 : ( X1 --> ft X1 ) ) .
  set ( n := ll X2 - ( ll ( ft X1 ) ) ) .
  assert ( e : ftn n X2 = ft X1 ) .
  assert ( isov := isabove_to_isover (T_dom_isabove inn )) .
  
  unfold isover in isov . 
  apply ( ! isov ) .

  assert ( gtn : ll X2 >= n ) . apply natminuslehn .
  
  apply ( fn_star f n gtn e ) . 

Defined.


(** **** Proving properties ax1a, ax1b and ax0 of operation T *)

Lemma T_ax1a_from_C { CC : lC0system } : T_ax1a_type ( T_from_C CC ) .
Proof.
  intros.
  unfold T_ax1a_type.
  intros .
  unfold T_from_C . 
  assert ( eq : ll X2 - ll (ft X1)  = S ( ll ( ft X2 ) - ll ( ft X1 ) ) ) .
  rewrite ( ll_ft X2 ) . 
  rewrite natminuscomm .
  change  ( ll X2 - ll (ft X1) = 1 + ( ll X2 - ll ( ft X1 ) - 1 ) ) .  
  rewrite <- natassocpmeq . 
  simpl . rewrite natminuseqn . 
  apply idpath . 

  apply gth0_to_geh1 . 
  apply minusgth0 . 
  apply ( T_dom_gth inn ) .

  rewrite ( fn_star_to_fsm_star _ _ _ eq ) .
  rewrite fsn_strict . 
  rewrite ( @ft_f_star CC ).
  unfold fn_star . 
  apply ( maponpaths pr1 ) .  apply qn_equals_qn . 
  apply C0_isaset_Ob .

  apply idpath . 
  
Defined.


 
Lemma T_ax1b_from_C ( CC : lC0system ) : T_ax1b_type ( T_from_C CC ) .
Proof.
  intros.
  unfold T_ax1b_type . 
  intros .
  refine ( isabove_constr _ _ ) .
  unfold T_from_C . 
  rewrite (@ll_fn_star CC) . 
  rewrite ll_ft .
  rewrite ( natpluscomm ( ll X1 ) _ ) . 
  change  ( ll X2 - (ll X1 - 1) + ll X1 > 0 + ( ll X1 ) ) . 
  apply natgthandplusr . 
  apply minusgth0 . 
  unfold T_dom in inn . 
  rewrite <- ll_ft .
  apply ( isabove_gth ( T_dom_isabove inn ) ) . 

  unfold T_from_C . apply isover_fn_star . 

Defined.


  

Lemma T_ax0_from_C ( CC : lC0system ) : T_ax0_type ( T_from_C CC ) . 
Proof.
  intros.
  unfold T_ax0_type . 
  intros X1 X2 inn .
  unfold T_from_C . 
  rewrite ( @ll_fn_star CC ) . 
  rewrite ll_ft . 
  rewrite <- natassocmpeq . rewrite <- natplusassoc .  rewrite ( natpluscomm ( ll X1 ) _ ) .
  rewrite minusplusnmm . 
  apply natpluscomm . 

  apply ( T_dom_geh inn ) . 

  apply ( T_dom_geh inn ) . 

  apply ( gth0_to_geh1 ( T_dom_gt0 inn ) ) .

Defined.


(** **** Morphism qT *)

Definition qT { CC : lC0system } { X1 X2 : B_carrier_from_C CC } ( inn : T_dom X1 X2 ) :
  mor_to X2 :=
  qn (pX X1) (ll X2 - ll (ft X1)) (natminuslehn (ll X2) (ll (ft X1)))
     (! ( isabove_to_isover ( T_dom_isabove inn) ) ).

Definition dom_qT { CC : lC0system } { X1 X2 : B_carrier_from_C CC } ( inn : T_dom X1 X2 ) :
  ( pr1 ( qT inn ) ) = T_from_C CC _ _ inn :=
  idpath _ . 


(** **** Operation T_ext and the inductive property of operation T *)


Notation T_ext_from_C := ( T_ext ( T_from_C _ ) ) .

Definition qT_ext { CC : lC0system } { X1 X2 : B_carrier_from_C CC } ( inn : T_ext_dom X1 X2 ) :
  mor_to X2 .
Proof.
  intros. refine ( mor_to_constr _ ) . 
  destruct (ovab_choice (pr2 inn)) as [ isab | iseq ] .
  apply ( pr1 ( qT ( T_dom_constr ( T_ext_dom_gt0 inn ) isab ) ) ) . 

  apply X1 .

  destruct (ovab_choice (pr2 inn)) as [ isab | iseq ] .
  apply ( pr2 ( qT ( T_dom_constr ( T_ext_dom_gt0 inn ) isab ) ) ) . 

  apply (( pX X1 ) ;; ( id_to_mor ( ! iseq ) ) ) . 

Defined.

Definition dom_qT_ext { CC : lC0system } { X1 X2 : B_carrier_from_C CC } ( inn : T_ext_dom X1 X2 ) :
  ( pr1 ( qT_ext inn ) ) = T_ext_from_C inn :=
  idpath _ . 


(* Lemma qT_as_q_of_f { CC : lC0system } { X1 X2 : B_carrier_from_C CC } ( inn : T_dom X1 X2 ) :
  qT inn = q_of_f ( T_dom_gt0_2 inn ) ( qT_ext ( T_dom_to_T_ext_dom_ft inn ) ) . 
Proof.
  intros.
  unfold qT . 
  assert ( eq : ll X2 - ll (ft X1)  = S ( ll ( ft X2 ) - ll ( ft X1 ) ) ) .
  rewrite ( ll_ft X2 ) . 
  rewrite natminuscomm .
  change  ( ll X2 - ll (ft X1) = 1 + ( ll X2 - ll ( ft X1 ) - 1 ) ) .  
  rewrite <- natassocpmeq . 
  simpl . rewrite natminuseqn . 
  apply idpath . 

  apply gth0_to_geh1 . 
  apply minusgth0 . 
  apply ( T_dom_gth inn ) .
  
  rewrite ( qn_to_qsm _ _ _ eq ) .
  rewrite qsn_strict .
  unfold qT_ext .
  set ( gt0_1 := (natgehgthtrans (ll X2) (S (ll (ft X2) - ll (ft X1))) 0
        (qsn_new_gtn (natminuslehn (ll X2) (ll (ft X1))) eq)
        (natgthsn0 (ll (ft X2) - ll (ft X1))))).
  change ((natgehgthtrans (ll X2) (S (ll (ft X2) - ll (ft X1))) 0
        (qsn_new_gtn (natminuslehn (ll X2) (ll (ft X1))) eq)
        (natgthsn0 (ll (ft X2) - ll (ft X1))))) with gt0_1 .
  assert ( int : gt0_1 = (T_dom_gt0_2 inn) ) .  
  apply ( proofirrelevance _ ( pr2 ( _ > _ ) ) ) .
  
  rewrite int .
  destruct ( ovab_choice (pr2 (T_dom_to_T_ext_dom_ft inn)) ) as [ isab | iseq ] .
  unfold qT .
  rewrite ( qn_equals_qn ( C0_isaset_Ob CC ) _ ( idpath (ll (ft X2) - ll (ft X1))) _
                         (natminuslehn (ll (ft X2)) (ll (ft X1))) _ (! ( isabove_to_isover isab))).
  apply idpath .

  assert ( int' : (qn (pX X1) (ll (ft X2) - ll (ft X1))
        (ll_ft_gtn (qsn_new_gtn (natminuslehn (ll X2) (ll (ft X1))) eq))
        (ftn_ft (ll (ft X2) - ll (ft X1)) X2 @
                qsn_new_eq (! ( isabove_to_isover ( T_dom_isabove inn))) eq)) =
                   (mor_to_constr (pX X1;; id_to_mor (! iseq)))) . 
  assert ( eq0 : (ll (ft X2) - ll (ft X1)) = 0 ) . 
  rewrite iseq . 
  apply natminusnn .
  apply q0 .

  rewrite ( maponpaths ( pr2 _ ) int' ) . 



 





  

  exact ( @maponpaths _ _ ( fun x => q_of_f (T_dom_gt0_2 inn) x ) (qn (pX X1) (ll (ft X2) - ll (ft X1))
        (ll_ft_gtn (qsn_new_gtn (natminuslehn (ll X2) (ll (ft X1))) eq))
        (ftn_ft (ll (ft X2) - ll (ft X1)) X2 @
         qsn_new_eq (! ( isabove_to_isover ( T_dom_isabove inn)))  eq)) (pr2 (mor_to_constr (pX X1;; id_to_mor (! iseq)))) int' ) . 


  
  *)

  

(** ***** Constructing operation S *)


Definition S_op_from_C ( CC : lC0system ) : S_ops_type ( B_carrier_from_C CC ) .
Proof.
  intros.
  unfold S_ops_type.
  intros r X inn . 
  set ( Y := ft ( dd r ) ) . set ( A := dd r ) . change _ with ( Tilde_from_C CC ) in r . 
  set ( f := r : Y --> A ) .
  set ( n := ll X - ll A ) .
  assert ( e : ftn n X = A ) . 
  set ( isov := inn : isover X A ) . 
  unfold isover in isov . 
  apply ( ! isov ) . 

  assert ( gtn : ll X >= n ) . apply natminuslehn .

  apply ( fn_star f n gtn e ) .

Defined.





Lemma S_ax1a_from_C { CC : lC0system } : S_ax1a_type ( S_op_from_C CC ) .
Proof.
  intros.
  unfold S_ax1a_type.
  intros .
  unfold S_op_from_C . 
  assert ( eq : ll Y - ll (dd r)  = S ( ll ( ft Y ) - ll ( dd r ) ) ) .
  rewrite ( ll_ft Y ) . 
  rewrite natminuscomm .
  change  ( ll Y - ll (dd r) = 1 + ( ll Y - ll ( dd r ) - 1 ) ) .  
  rewrite <- natassocpmeq . 
  simpl . rewrite natminuseqn . 
  apply idpath . 

  apply gth0_to_geh1 . 
  apply minusgth0 . 
  apply ( S_dom_gth inn ) .
  
  set ( int1 := (! isabove_to_isover inn)).
  set ( int2 := (! isabove_to_isover isab)).
  set ( int3 := (natminuslehn (ll Y) (ll (dd r)))).
  set ( int4 := (natminuslehn (ll (ft Y)) (ll (dd r)))). 
  generalize int1 . clear int1 .
  generalize int2 . clear int2 .
  generalize int3 . clear int3 .
  generalize int4 . clear int4 .
   

  rewrite eq .
  intros . 
  rewrite fsn_strict . 
  rewrite ( @ft_f_star CC ).
  unfold fn_star . 
  apply ( maponpaths pr1 ) .  apply qn_equals_qn . 
  apply C0_isaset_Ob .

  apply idpath .

Defined.



Lemma S_ax1b_from_C ( CC : lC0system ) : S_ax1b_type ( S_op_from_C CC ) .
Proof.
  intros.
  unfold S_ax1b_type . 
  intros .
  refine ( isabove_constr _ _ ) .
  unfold S_op_from_C . 
  rewrite (@ll_fn_star CC) .
  rewrite <- ( natplusr0 (ll (ft (dd r)))) . 
  apply natgthandplusl .
  apply minusgth0 . 
  apply ( isabove_gth inn ) . 

  unfold S_op_from_C . apply isover_fn_star . 

Defined.


Lemma S_ax0_from_C ( CC : lC0system ) : S_ax0_type ( S_op_from_C CC ) . 
Proof.
  intros.
  unfold S_ax0_type . 
  intros X1 X2 inn .
  unfold S_op_from_C . 
  rewrite ( @ll_fn_star CC ) . 
  rewrite ll_ft .
  rewrite natpluscomm . rewrite <- natminusinter . apply idpath . 

  apply ( natgthtogeh _ _ ( isabove_gth inn ) ) . 

  apply gth0_to_geh1 . 
  apply ll_dd_from_C . 

Defined.








      


(** **** Constructing operation Tt *)


(* Definition Tt_op_from_C { CC : lCsystem } ( is1 : has_homsets CC ) ( is2 : isaset CC ) :
  Tt_ops_type ( B_carrier_from_C is1 is2 ) .
Proof .
  intros.
  unfold Tt_ops_type.
  intros X r inn .
  unfold Tilde . 
  simpl . 
  unfold Tilde_from_C . 
  refine ( tpair _ _ _ ) . 
  exact ( T_from_C is1 is2 _ _ inn ) . 

  split.
  rewrite (@T_ax0_from_C CC is1 is2) . 
  apply natgthsn0 . 

  *)

  
(* End of the file lC_to_lB_systems.v *)