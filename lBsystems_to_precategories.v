(** ** lB-systems to precategories.  

by Vladimir Voevodsky, started on Jan. 22, 2015 *)

Unset Automatic Introduction.

Require Export lBsystems.lBsystems_T_fun_Tj_Ttj.
Require Export lBsystems.lBsystems_S_fun.

Require Export lBsystems.lB0systems .

Require Export lCsystems.lC_to_lB0.


(** *** The first construction of the types Mor_from_B *)


(** We first define for Z in an lB-system and m <= ll Z the type
( iterated_sections m Z ) that corresponds to the sections of the projection Z -> ft^m Z 
in the associated lC-system. We do it for non-unital prelBsystems but the only structure that
is actually required is an lBsystem_carrier and an operation of type S_ops_type satisfying
axiom ax0. *)

Lemma iter_sec_inn { BB : prelBsystem_non_unital }
      { m : nat } { Z : BB } ( gt0 : m > 0 ) ( lesm : S m <= ll Z )
      ( s : Tilde_dd ( ftn m Z ) ) : S_dom s Z .
Proof.
  intros.
  unfold S_dom .
  set ( eq := pr2 s : dd s = ftn m Z ) . simpl in eq .
  rewrite eq .
  
  apply ( isabove_X_ftnX gt0 ) .
  apply ( natgehgthtrans _ _ _ lesm ( natgthsn0 _ ) ) .

Defined.

Lemma iter_sec_le { BB : prelBsystem_non_unital }
      { m : nat } { Z : BB } ( gt0 : m > 0 ) ( lesm : S m <= ll Z )
      ( s : Tilde_dd ( ftn m Z ) ) : m <= ll ( S_op s Z ( iter_sec_inn gt0 lesm s ) ) . 
Proof.
  intros.
  rewrite S_ax0 .
  assert ( leint := natgehandminusr _ _ 1 lesm ) . 
  simpl in leint . 
  rewrite natminuseqn in leint .
  exact leint . 

Defined.


Definition iter_sec { BB : prelBsystem_non_unital }
           ( m : nat ) ( Z : BB ) ( le : m <= ll Z ) : UU .
Proof.
  intros until m . set ( S := @S_op BB ) . set ( sax0 := @S_ax0 BB ) . 
  induction m as [ | m IHm ] .
  intros. exact unit .

  intros Z le .
  destruct ( natgehchoice _ _ ( natgehn0 m ) ) as [ gt0 | eq0 ] . 
  set ( inn := iter_sec_inn gt0 le ) .
  set ( le' := iter_sec_le gt0 le ) . 
  exact ( total2 ( fun s : Tilde_dd ( ftn m Z ) => IHm ( S s Z ( inn s ) ) (le' s) ) ) .

  exact ( Tilde_dd Z ) . 

Defined.


(* Definition iter_sec_m_eq_sn { BB : prelBsystem_non_unital }
           { m n : nat } ( eq : m = S n )
           ( Z : BB ) ( lem : m <= ll Z ) ( lesn : S n <= ll Z ) :
  iter_sec m Z lem =
  total2 ( fun s : Tilde_dd ( ftn m Z ) => iter_sec n ( S s Z ( inn s ) ))*)


(** We now define morphisms X --> Y as iterated sections of the projection Tprod X Y --> X *)


Definition Mor_from_B { BB : lB0system_non_unital } ( X Y : BB ) : UU .
Proof.
  intros.
  refine ( iter_sec ( ll Y ) ( Tprod X Y ) _ ) .
  rewrite ll_Tprod . 
  apply natlehmplusnm . 

Defined.


(** Here is another definition of morphisms that defines them together with the corresponding
operation f_star *)


Definition Mor_and_fstar { BB : lB0system_non_unital }
           ( X1 : BB ) ( n : nat ) ( A : BB ) ( eq : ll A = n ) : 
  total2 ( fun Mor_X1_A : UU =>
             forall f : Mor_X1_A ,
               ltower_fun ( ltower_over A ) ( ltower_over X1 ) ) . 
Proof .
  intros until n . induction n as [ | n IHn ] . 
  intros . 
  split with unit .

  intro .
  exact ( Tj_fun ( @isoverll0 BB _ eq X1 ) ) . 

  intros .
  assert ( eqft : ll ( ft A ) = n ) . rewrite ll_ft . rewrite eq . simpl . rewrite natminuseqn .
  apply idpath .

  set ( Mor_X1_ftA := pr1 ( IHn ( ft A ) eqft ) ) .
  set ( Mor_X1_A :=
          total2 ( fun ftf : Mor_X1_ftA =>
                     Tilde_dd ( pocto ( ( pr2 ( IHn ( ft A ) eqft ) ftf ) ( X_over_ftX A ) ) ) ) ) .
  split with Mor_X1_A . 

  intro f .
  set ( ftf := pr1 f : Mor_X1_ftA ) .
  set ( s_f := pr1 ( pr2 f ) : Tilde BB ) .
  set ( ftf_star := pr2 ( IHn ( ft A ) eqft ) ftf :
                      ltower_fun ( ltower_over ( ft A ) ) ( ltower_over X1 ) ) .
  set ( ftf_star_A := pocto ( ftf_star ( X_over_ftX A ) : ltower_over X1 ) ) .
  set ( eq_s_f := pr2 ( pr2 f ) : dd ( s_f ) = ftf_star_A ) . 
  assert ( fun1 : ltower_fun ( ltower_over A ) ( ltower_over ftf_star_A ) ) .
  apply ( ltower_fun_second ftf_star ( X_over_ftX A ) ) .

  assert ( fun2 : ltower_fun ( ltower_over ftf_star_A ) ( ltower_over ( ft ftf_star_A ) ) ) . 
  rewrite <- eq_s_f .
  apply ( S_fun s_f ) .

  assert ( gt0 : ll (ftf_star (X_over_ftX A)) > 0 ) .
  rewrite (@ll_ltower_fun (pltower_over ( ft A ) )).
  change ( ll (X_over_ftX A) > 0 ) . 
  rewrite ll_X_over_ftX . 
  apply idpath . 

  rewrite eq . apply natgthsn0 .
  
  assert ( eq' : ft ftf_star_A = X1 ) .
  unfold ftf_star_A .
  rewrite ft_pocto .
  assert ( eq1 : ft (ftf_star (X_over_ftX A)) = X_over_X X1 ) . 
  assert ( eq2 : ll ( ft (ftf_star (X_over_ftX A)) ) = 0 ) .
  rewrite ll_ft . 
  rewrite (@ll_ltower_fun (pltower_over (ft A))). 
  change ( ll (X_over_ftX A) - 1 = 0 ) . 
  rewrite ll_X_over_ftX . 
  apply idpath . 

  rewrite eq . apply natgthsn0 .

  apply ( @noparts_ispointed  ( pltower_over _ ) _ _ eq2 ( ll_X_over_X X1 ) ) . 

  rewrite eq1 .
  apply idpath . 

  apply gt0 . 

  set ( fun12 := ltower_funcomp fun1 fun2 ) .
  rewrite eq' in fun12 . 
  exact fun12 . 

Defined.




(** We now start proving the comparison theorem showing that for lB0-systems of the form
lB0_from_C CC our construction Mor_from_B recovers the morphisms in CC. *)



(** Construction of a function from iterated_sections to morphisms *)

Definition iter_sec_to_mor { CC : lCsystem } { m : nat } { Z : CC } { le : m <= ll Z }
           ( itrs : @iter_sec ( lB0_from_C CC ) m Z le ) : ftn m Z --> Z .
Proof.
  intros until m . 
  induction m . 
  intros . 
  apply ( identity Z ) .

  intros . 
  simpl in itrs . 
  destruct (natgehchoice m 0 (natgehn0 m)) as [ gt0 | eq0 ] .

  set ( s := pr1 itrs ) .
  set ( s_eq := pr2 ( pr1 itrs ) : dd s = ftn m Z ) .
  set ( s_mor := pr2 ( pr2 ( pr1 ( pr1 itrs ) ) ) : ft ( dd s ) --> dd s ) .
  set ( inn := (@iter_sec_inn ( lB0_from_C CC ) _ _ gt0 le s)).
  set ( le' := (@iter_sec_le ( lB0_from_C CC ) _ _ gt0 le s)).
  set ( sm := pr2 itrs : iter_sec m (@S_op ( lB0_from_C CC ) s Z inn) le') . 
  assert ( s1 := IHm (@S_op ( lB0_from_C CC ) s Z inn) le' sm ) . 

  assert ( qn_from_S : @S_op ( lB0_from_C CC ) s Z inn --> Z ) .  
  unfold S_op.
  simpl .
  unfold S_from_C . 
  exact ( qn s_mor (ll Z - ll (dd s)) _ _ ) .

  assert ( eq : ftn ( S m ) Z = ftn m ( @S_op ( lB0_from_C CC ) s Z inn ) ) . 
  assert ( isov : isover ( ( @S_op ( lB0_from_C CC ) s Z inn ) ) ( ft ( dd s ) ) ) .
  apply isabove_to_isover .  apply S_ax1b_from_C . 

  unfold isover in isov . 
  rewrite s_eq in isov . 
  change ( ftn ( S m ) Z ) with ( ft ( ftn m Z ) ) . 
  refine ( isov @ _ ) . 
  assert ( eq_in_nat : ll (@S_op ( lB0_from_C CC ) s Z inn) - ll (ft (ftn m Z)) = m ) . 
  rewrite ll_S .
  rewrite ll_ft . 
  rewrite ll_ftn .
  rewrite natmiusmius1mminus1 . 
  apply natminusmmk .

  apply ( istransnatgeh _ _ _ le ( natgehsnn _ ) ) .

  apply ( natgehgthtrans _ _ _ le ( natgthsn0 _ ) ) . 

  apply minusgth0 . apply ( natgehgthtrans _ _ _ le ( natgthsnn _ ) ) . 

  apply ( maponpaths ( fun n => ftn n _ ) eq_in_nat ) .

  apply ( ( id_to_mor eq ) ;; s1 ;; qn_from_S ) . 

  rewrite eq0 . 
  change ( ft Z --> Z ) . 
  set ( s_eq := pr2 itrs : dd itrs = Z ) .
  set ( s_mor := pr2 ( pr2 ( pr1 itrs ) ) : ft ( dd itrs ) --> dd itrs ) .
  rewrite s_eq in s_mor . 
  exact s_mor.

Defined.

(** Construction of the (horizontal) projection from ( Tj X A Y ) to Y *)



Definition hor_proj_ft_case { CC : lCsystem } ( X Z : CC ) ( gt0 : ll X > 0 ) :
  @Tprod ( lB0_from_C CC ) X Z --> @Tprod ( lB0_from_C CC ) ( ft X ) Z .
Proof .
  intros.
  rewrite ( @Tprod_compt ( lB0_from_C CC ) _ _ gt0 ) .
  unfold T_ext .   
  unfold lBsystems_T_fun_Tj_Ttj.T_ext .
  change ( ll X > 0 ) with ( ll ( X : ( lB0_from_C CC ) ) > 0 ) in gt0 . 
  set ( ch := ovab_choice (pr2 (T_ext_dom_constr gt0 (isover_Tprod (ft ( X  : ( lB0_from_C CC ) )) Z)))) .
  destruct ch as [ isab | iseq ] . 
  exact ( pr2 ( qn _ _ _ _ ) )  . 

  change (Tprod _ _) with (Tprod (ft ( X  : ( lB0_from_C CC ) )) Z) . rewrite iseq . 
  apply pX . 

Defined.

  
Definition hor_proj_int { CC : lCsystem } ( X Y Z : CC ) ( isov : isover X Y ) :
  @Tprod ( lB0_from_C CC ) X Z --> @Tprod ( lB0_from_C CC ) Y Z :=
  isover_ind
            ( fun X0 Y0 => @Tprod ( lB0_from_C CC ) X0 Z --> @Tprod ( lB0_from_C CC ) Y0 Z )
            ( fun X0 => identity _ )
            ( fun X0 gt0 => hor_proj_ft_case X0 Z gt0 )
            ( fun X0 Y0 f g => f ;; g ) X Y isov .


Definition hor_proj_cntr_case { CC : lCsystem } ( Y : CC ) : 
  @Tprod ( lB0_from_C CC ) ( cntr CC ) Y --> Y .
Proof.
  intros .
  unfold Tprod . 
  unfold Tprod_over . 
  unfold Tprod_fun . 
  unfold lBsystems_T_fun_Tj_Ttj.Tj_fun.
  rewrite (@isover_ind_compt0 ( lB0_from_C CC )). 
  simpl . 
  apply identity . 

Defined.


Definition hor_proj { CC : lCsystem } ( X Y : CC ) : 
  @Tprod ( lB0_from_C CC ) X Y --> Y .
Proof.
  intros .
  assert ( int1 : @Tprod ( lB0_from_C CC ) X Y --> @Tprod ( lB0_from_C CC ) ( cntr CC ) Y ) .
  apply hor_proj_int . 
  exact ( @isover_cntr ( lB0_from_C CC ) X ) . 

  assert ( int2 :  @Tprod ( lB0_from_C CC ) ( cntr CC ) Y --> Y ) . apply hor_proj_cntr_case .

  exact ( int1 ;; int2 ) . 

Defined.



Definition Mor_lB0_from_C_to_Mor { CC : lCsystem } ( X Y : CC )
           ( f : @Mor_from_B ( lB0_from_C CC ) X Y ) : X --> Y . 
Proof .
  intros .
  unfold Mor_from_B in f . 
  set ( int1 := iter_sec_to_mor f ) .
  assert ( eq : ftn ( ll Y ) ( @Tprod ( lB0_from_C CC ) X Y ) = X ) . 
  set ( isov := @isover_Tprod ( lB0_from_C CC ) X Y ) . 
  unfold isover in isov . 
  assert ( eq'' : ftn (ll (@Tprod ( lB0_from_C CC ) X Y) - ll X) (@Tprod ( lB0_from_C CC ) X Y) =
                  ftn (ll Y) (@Tprod ( lB0_from_C CC ) X Y) ) .
  rewrite ll_Tprod . 
  rewrite natpluscomm .
  rewrite plusminusnmm . 
  apply idpath . 

  exact ( ( ! eq'' ) @ ( ! isov ) ) . 

  change (ftn (ll Y) (Tprod _ _ )) with (ftn (ll Y) (@Tprod ( lB0_from_C CC ) X Y)) in int1 . 
  rewrite eq in int1 . 

  assert ( int2 := hor_proj X Y ) . 

  exact ( int1 ;; int2 ) . 

Defined.











(* End of the file lBsystems_to_precategories.v *)