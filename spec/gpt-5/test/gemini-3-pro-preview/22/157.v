Require Import Coq.Lists.List.
Require Import ZArith.
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

Parameter val_1 : Any.
Parameter val_list_2_3 : Any.
Parameter val_list_4 : Any.
Parameter val_list_5_6_6 : Any.
Parameter val_list_7_8 : Any.
Parameter val_9 : Any.

Axiom is_int_val_1 : IsInt val_1 1%Z.
Axiom not_int_val_list_2_3 : forall n, ~ IsInt val_list_2_3 n.
Axiom not_int_val_list_4 : forall n, ~ IsInt val_list_4 n.
Axiom not_int_val_list_5_6_6 : forall n, ~ IsInt val_list_5_6_6 n.
Axiom not_int_val_list_7_8 : forall n, ~ IsInt val_list_7_8 n.
Axiom is_int_val_9 : IsInt val_9 9%Z.

Example test_filter_integers_complex : 
  filter_integers_spec 
    [val_1; val_list_2_3; val_list_4; val_list_5_6_6; val_list_7_8; val_9; val_1; val_list_4] 
    [1%Z; 9%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1%Z). apply is_int_val_1.
  apply fir_cons_nonint. apply not_int_val_list_2_3.
  apply fir_cons_nonint. apply not_int_val_list_4.
  apply fir_cons_nonint. apply not_int_val_list_5_6_6.
  apply fir_cons_nonint. apply not_int_val_list_7_8.
  apply fir_cons_int with (n := 9%Z). apply is_int_val_9.
  apply fir_cons_int with (n := 1%Z). apply is_int_val_1.
  apply fir_cons_nonint. apply not_int_val_list_4.
  apply fir_nil.
Qed.