Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
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

Parameter a1 a_list4 a_list5 a9 a_list5' : Any.
Parameter n1 n9 : int.
Axiom a1_is_int : IsInt a1 n1.
Axiom a9_is_int : IsInt a9 n9.
Axiom a_list4_nonint : forall n, ~ IsInt a_list4 n.
Axiom a_list5_nonint : forall n, ~ IsInt a_list5 n.
Axiom a_list5'_nonint : forall n, ~ IsInt a_list5' n.

Example test_case_new: filter_integers_spec [a1; a_list4; a_list5; a9; a_list5'] [n1; n9].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - exact a1_is_int.
  - eapply fir_cons_nonint.
    + exact a_list4_nonint.
    + eapply fir_cons_nonint.
      * exact a_list5_nonint.
      * eapply fir_cons_int.
        { exact a9_is_int. }
        { eapply fir_cons_nonint.
          - exact a_list5'_nonint.
          - constructor. }
Qed.