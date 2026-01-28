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

Parameter val_4_6 : Any.
Parameter val_7_8 : Any.
Parameter val_str : Any.
Parameter val_dict : Any.
Parameter val_empty_list : Any.
Parameter val_2_5 : Any.

Axiom not_int_4_6 : forall n, ~ IsInt val_4_6 n.
Axiom not_int_7_8 : forall n, ~ IsInt val_7_8 n.
Axiom not_int_str : forall n, ~ IsInt val_str n.
Axiom not_int_dict : forall n, ~ IsInt val_dict n.
Axiom not_int_empty_list : forall n, ~ IsInt val_empty_list n.
Axiom not_int_2_5 : forall n, ~ IsInt val_2_5 n.

Example test_filter_integers_mixed : filter_integers_spec [val_4_6; val_7_8; val_str; val_dict; val_empty_list; val_2_5] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_4_6.
  apply fir_cons_nonint. apply not_int_7_8.
  apply fir_cons_nonint. apply not_int_str.
  apply fir_cons_nonint. apply not_int_dict.
  apply fir_cons_nonint. apply not_int_empty_list.
  apply fir_cons_nonint. apply not_int_2_5.
  apply fir_nil.
Qed.