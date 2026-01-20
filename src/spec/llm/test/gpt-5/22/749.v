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

Parameter obj_two_string2 : Any.
Axiom obj_two_string2_nonint : forall n, ~ IsInt obj_two_string2 n.

Parameter obj_three_list_3_four : Any.
Axiom obj_three_list_3_four_nonint : forall n, ~ IsInt obj_three_list_3_four n.

Parameter obj_empty1 : Any.
Axiom obj_empty1_nonint : forall n, ~ IsInt obj_empty1 n.

Parameter obj_two_string2_dup : Any.
Axiom obj_two_string2_dup_nonint : forall n, ~ IsInt obj_two_string2_dup n.

Parameter obj_five_5 : Any.
Axiom obj_five_5_nonint : forall n, ~ IsInt obj_five_5 n.

Parameter obj_empty2 : Any.
Axiom obj_empty2_nonint : forall n, ~ IsInt obj_empty2 n.

Example test_case_nonints: filter_integers_spec [obj_two_string2; obj_three_list_3_four; obj_empty1; obj_two_string2_dup; obj_five_5; obj_empty2] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  apply obj_two_string2_nonint.
  apply fir_cons_nonint.
  apply obj_three_list_3_four_nonint.
  apply fir_cons_nonint.
  apply obj_empty1_nonint.
  apply fir_cons_nonint.
  apply obj_two_string2_dup_nonint.
  apply fir_cons_nonint.
  apply obj_five_5_nonint.
  apply fir_cons_nonint.
  apply obj_empty2_nonint.
  apply fir_nil.
Qed.