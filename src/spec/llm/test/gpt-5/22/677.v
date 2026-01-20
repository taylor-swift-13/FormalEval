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

Parameter dict_two_str : Any.
Axiom dict_two_str_nonint : forall n, ~ IsInt dict_two_str n.

Parameter dict_three_mixed : Any.
Axiom dict_three_mixed_nonint : forall n, ~ IsInt dict_three_mixed n.

Parameter dict_seven_str1 : Any.
Axiom dict_seven_str1_nonint : forall n, ~ IsInt dict_seven_str1 n.

Parameter dict_empty : Any.
Axiom dict_empty_nonint : forall n, ~ IsInt dict_empty n.

Parameter dict_five_six_mixed : Any.
Axiom dict_five_six_mixed_nonint : forall n, ~ IsInt dict_five_six_mixed n.

Parameter dict_seven_str2 : Any.
Axiom dict_seven_str2_nonint : forall n, ~ IsInt dict_seven_str2 n.

Example test_case_dicts: filter_integers_spec [dict_two_str; dict_three_mixed; dict_seven_str1; dict_empty; dict_five_six_mixed; dict_seven_str2] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply dict_two_str_nonint|].
  eapply fir_cons_nonint; [apply dict_three_mixed_nonint|].
  eapply fir_cons_nonint; [apply dict_seven_str1_nonint|].
  eapply fir_cons_nonint; [apply dict_empty_nonint|].
  eapply fir_cons_nonint; [apply dict_five_six_mixed_nonint|].
  eapply fir_cons_nonint; [apply dict_seven_str2_nonint|].
  constructor.
Qed.