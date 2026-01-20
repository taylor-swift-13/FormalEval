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

Parameter a_nil1 a_nil2 a_list_5 a_bools a_list_7_8 a9_v1 a9_v2 a_list_5_2 a_list_5_3 a_bools_2 : Any.

Axiom not_int_a_nil1 : forall n, ~ IsInt a_nil1 n.
Axiom not_int_a_nil2 : forall n, ~ IsInt a_nil2 n.
Axiom not_int_a_list_5 : forall n, ~ IsInt a_list_5 n.
Axiom not_int_a_bools : forall n, ~ IsInt a_bools n.
Axiom not_int_a_list_7_8 : forall n, ~ IsInt a_list_7_8 n.
Axiom not_int_a_list_5_2 : forall n, ~ IsInt a_list_5_2 n.
Axiom not_int_a_list_5_3 : forall n, ~ IsInt a_list_5_3 n.
Axiom not_int_a_bools_2 : forall n, ~ IsInt a_bools_2 n.

Axiom is_int_a9_1 : IsInt a9_v1 9%Z.
Axiom is_int_a9_2 : IsInt a9_v2 9%Z.

Example test_case_new: filter_integers_spec [a_nil1; a_nil2; a_list_5; a_bools; a_list_7_8; a9_v1; a9_v2; a_list_5_2; a_list_5_3; a_bools_2] [9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply not_int_a_nil1 |].
  eapply fir_cons_nonint; [apply not_int_a_nil2 |].
  eapply fir_cons_nonint; [apply not_int_a_list_5 |].
  eapply fir_cons_nonint; [apply not_int_a_bools |].
  eapply fir_cons_nonint; [apply not_int_a_list_7_8 |].
  eapply fir_cons_int; [apply is_int_a9_1 |].
  eapply fir_cons_int; [apply is_int_a9_2 |].
  eapply fir_cons_nonint; [apply not_int_a_list_5_2 |].
  eapply fir_cons_nonint; [apply not_int_a_list_5_3 |].
  eapply fir_cons_nonint; [apply not_int_a_bools_2 |].
  apply fir_nil.
Qed.