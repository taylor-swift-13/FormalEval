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

Parameter v_2_5 : Any.
Parameter v_4_750003778215635 : Any.
Parameter v_7_8a : Any.
Parameter v_string_abc : Any.
Parameter v_object_empty : Any.
Parameter v_list_empty : Any.
Parameter v_7_8b : Any.

Axiom nonint_v_2_5 : forall n, ~ IsInt v_2_5 n.
Axiom nonint_v_4_750003778215635 : forall n, ~ IsInt v_4_750003778215635 n.
Axiom nonint_v_7_8a : forall n, ~ IsInt v_7_8a n.
Axiom nonint_v_string_abc : forall n, ~ IsInt v_string_abc n.
Axiom nonint_v_object_empty : forall n, ~ IsInt v_object_empty n.
Axiom nonint_v_list_empty : forall n, ~ IsInt v_list_empty n.
Axiom nonint_v_7_8b : forall n, ~ IsInt v_7_8b n.

Example test_case_new:
  filter_integers_spec
    [v_2_5; v_4_750003778215635; v_7_8a; v_string_abc; v_object_empty; v_list_empty; v_7_8b]
    [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply nonint_v_2_5 |].
  eapply fir_cons_nonint; [apply nonint_v_4_750003778215635 |].
  eapply fir_cons_nonint; [apply nonint_v_7_8a |].
  eapply fir_cons_nonint; [apply nonint_v_string_abc |].
  eapply fir_cons_nonint; [apply nonint_v_object_empty |].
  eapply fir_cons_nonint; [apply nonint_v_list_empty |].
  eapply fir_cons_nonint; [apply nonint_v_7_8b |].
  constructor.
Qed.