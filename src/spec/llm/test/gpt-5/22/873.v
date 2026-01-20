Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Parameters
  a_false a_None1 a_5 a_m6 a_0 a_a a_b a_emptydict a_bbdef a_dict_b_2
  a_list_34 a_list_56_7 a_bigdict a_None2 : Any.

Axiom a_5_is_int : IsInt a_5 5%Z.
Axiom a_m6_is_int : IsInt a_m6 (-6)%Z.
Axiom a_0_is_int : IsInt a_0 0%Z.

Axiom a_false_nonint : forall n, ~ IsInt a_false n.
Axiom a_None1_nonint : forall n, ~ IsInt a_None1 n.
Axiom a_a_nonint : forall n, ~ IsInt a_a n.
Axiom a_b_nonint : forall n, ~ IsInt a_b n.
Axiom a_emptydict_nonint : forall n, ~ IsInt a_emptydict n.
Axiom a_bbdef_nonint : forall n, ~ IsInt a_bbdef n.
Axiom a_dict_b_2_nonint : forall n, ~ IsInt a_dict_b_2 n.
Axiom a_list_34_nonint : forall n, ~ IsInt a_list_34 n.
Axiom a_list_56_7_nonint : forall n, ~ IsInt a_list_56_7 n.
Axiom a_bigdict_nonint : forall n, ~ IsInt a_bigdict n.
Axiom a_None2_nonint : forall n, ~ IsInt a_None2 n.

Example test_case_empty:
  filter_integers_spec
    [a_false; a_None1; a_5; a_m6; a_0; a_a; a_b; a_emptydict; a_bbdef; a_dict_b_2; a_list_34; a_list_56_7; a_bigdict; a_None2]
    [5%Z; (-6)%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply (fir_cons_nonint a_false).
  - exact a_false_nonint.
  - eapply (fir_cons_nonint a_None1).
    + exact a_None1_nonint.
    + eapply (fir_cons_int a_5 5%Z).
      * exact a_5_is_int.
      * eapply (fir_cons_int a_m6 (-6)%Z).
        -- exact a_m6_is_int.
        -- eapply (fir_cons_int a_0 0%Z).
           ++ exact a_0_is_int.
           ++ eapply (fir_cons_nonint a_a).
              ** exact a_a_nonint.
              ** eapply (fir_cons_nonint a_b).
                 *** exact a_b_nonint.
                 *** eapply (fir_cons_nonint a_emptydict).
                     **** exact a_emptydict_nonint.
                     **** eapply (fir_cons_nonint a_bbdef).
                          ***** exact a_bbdef_nonint.
                          ***** eapply (fir_cons_nonint a_dict_b_2).
                                ****** exact a_dict_b_2_nonint.
                                ****** eapply (fir_cons_nonint a_list_34).
                                       ******* exact a_list_34_nonint.
                                       ******* eapply (fir_cons_nonint a_list_56_7).
                                               ******** exact a_list_56_7_nonint.
                                               ******** eapply (fir_cons_nonint a_bigdict).
                                                        ********* exact a_bigdict_nonint.
                                                        ********* eapply (fir_cons_nonint a_None2).
                                                                 ********** exact a_None2_nonint.
                                                                 ********** constructor.
Qed.