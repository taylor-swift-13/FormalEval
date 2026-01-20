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

Parameter v_list_5_6 : Any.
Parameter v_7 : Any.
Parameter v_2_3_a : Any.
Parameter v_2_3_b : Any.
Parameter n7 : int.
Axiom IsInt_v_7 : IsInt v_7 n7.
Axiom NonInt_v_list_5_6 : forall n, ~ IsInt v_list_5_6 n.
Axiom NonInt_v_2_3_a : forall n, ~ IsInt v_2_3_a n.
Axiom NonInt_v_2_3_b : forall n, ~ IsInt v_2_3_b n.

Example test_case_new: filter_integers_spec [v_list_5_6; v_7; v_2_3_a; v_2_3_b] [n7].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NonInt_v_list_5_6 |].
  eapply fir_cons_int; [apply IsInt_v_7 |].
  eapply fir_cons_nonint; [apply NonInt_v_2_3_a |].
  eapply fir_cons_nonint; [apply NonInt_v_2_3_b |].
  constructor.
Qed.