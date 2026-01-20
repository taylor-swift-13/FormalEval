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

Parameter dict_one_two : Any.
Parameter dict_three_four : Any.
Parameter dict_empty : Any.
Parameter dict_five : Any.
Parameter dict_seven_eight : Any.

Axiom not_int_dict_one_two : forall n, ~ IsInt dict_one_two n.
Axiom not_int_dict_three_four : forall n, ~ IsInt dict_three_four n.
Axiom not_int_dict_empty : forall n, ~ IsInt dict_empty n.
Axiom not_int_dict_five : forall n, ~ IsInt dict_five n.
Axiom not_int_dict_seven_eight : forall n, ~ IsInt dict_seven_eight n.

Example test_case_complex: filter_integers_spec [dict_one_two; dict_three_four; dict_empty; dict_five; dict_seven_eight; dict_five; dict_seven_eight] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact not_int_dict_one_two|].
  eapply fir_cons_nonint; [exact not_int_dict_three_four|].
  eapply fir_cons_nonint; [exact not_int_dict_empty|].
  eapply fir_cons_nonint; [exact not_int_dict_five|].
  eapply fir_cons_nonint; [exact not_int_dict_seven_eight|].
  eapply fir_cons_nonint; [exact not_int_dict_five|].
  eapply fir_cons_nonint; [exact not_int_dict_seven_eight|].
  constructor.
Qed.