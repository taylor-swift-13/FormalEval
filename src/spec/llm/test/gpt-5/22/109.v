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

Parameter v1 v_list_2_3 v_list_4 v_list_5_6 v_list_7_8 v9 : Any.
Parameter n1 n9 : int.
Axiom H1 : IsInt v1 n1.
Axiom H9 : IsInt v9 n9.
Axiom H23_non : forall n, ~ IsInt v_list_2_3 n.
Axiom H4_non : forall n, ~ IsInt v_list_4 n.
Axiom H56_non : forall n, ~ IsInt v_list_5_6 n.
Axiom H78_non : forall n, ~ IsInt v_list_7_8 n.

Example test_case_nested:
  filter_integers_spec [v1; v_list_2_3; v_list_4; v_list_5_6; v_list_7_8; v9] [n1; n9].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_int v1 n1); [apply H1|].
  apply (fir_cons_nonint v_list_2_3); [apply H23_non|].
  apply (fir_cons_nonint v_list_4); [apply H4_non|].
  apply (fir_cons_nonint v_list_5_6); [apply H56_non|].
  apply (fir_cons_nonint v_list_7_8); [apply H78_non|].
  apply (fir_cons_int v9 n9); [apply H9|].
  constructor.
Qed.