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

Parameter a_true a_false a_none a_0 a_real1 a_minus10 a_string_test a_emptylist a_dict a_real_pi : Any.
Axiom not_int_true : forall n, ~ IsInt a_true n.
Axiom not_int_false : forall n, ~ IsInt a_false n.
Axiom not_int_none : forall n, ~ IsInt a_none n.
Axiom is_int_0 : IsInt a_0 0%Z.
Axiom not_int_real1 : forall n, ~ IsInt a_real1 n.
Axiom is_int_minus10 : IsInt a_minus10 (-10)%Z.
Axiom not_int_string_test : forall n, ~ IsInt a_string_test n.
Axiom not_int_emptylist : forall n, ~ IsInt a_emptylist n.
Axiom not_int_dict : forall n, ~ IsInt a_dict n.
Axiom not_int_real_pi : forall n, ~ IsInt a_real_pi n.

Example test_case: filter_integers_spec
  [a_true; a_false; a_none; a_0; a_real1; a_minus10; a_string_test; a_emptylist; a_dict; a_real_pi]
  [0%Z; (-10)%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact not_int_true.
  - eapply fir_cons_nonint.
    + exact not_int_false.
    + eapply fir_cons_nonint.
      * exact not_int_none.
      * eapply fir_cons_int.
        -- exact is_int_0.
        -- eapply fir_cons_nonint.
           ++ exact not_int_real1.
           ++ eapply fir_cons_int.
              ** exact is_int_minus10.
              ** eapply fir_cons_nonint.
                 *** exact not_int_string_test.
                 *** eapply fir_cons_nonint.
                     **** exact not_int_emptylist.
                     **** eapply fir_cons_nonint.
                          ***** exact not_int_dict.
                          ***** eapply fir_cons_nonint.
                                ****** exact not_int_real_pi.
                                ****** constructor.
Qed.