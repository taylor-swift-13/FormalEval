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

Parameter val_1 : Any.
Parameter val_2 : Any.
Parameter val_3 : Any.
Parameter val_4 : Any.
Parameter val_5 : Any.
Parameter val_6 : Any.
Parameter val_7 : Any.

Parameter int_1 : int.
Parameter int_2 : int.
Parameter int_4 : int.

Axiom is_int_val_1 : IsInt val_1 int_1.
Axiom is_int_val_2 : IsInt val_2 int_2.
Axiom not_int_val_3 : forall n, ~ IsInt val_3 n.
Axiom is_int_val_4 : IsInt val_4 int_4.
Axiom not_int_val_5 : forall n, ~ IsInt val_5 n.
Axiom not_int_val_6 : forall n, ~ IsInt val_6 n.
Axiom not_int_val_7 : forall n, ~ IsInt val_7 n.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [val_1; val_2; val_3; val_4; val_5; val_6; val_7; val_1] 
    [int_1; int_2; int_4; int_1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. apply is_int_val_1.
  apply fir_cons_int. apply is_int_val_2.
  apply fir_cons_nonint. apply not_int_val_3.
  apply fir_cons_int. apply is_int_val_4.
  apply fir_cons_nonint. apply not_int_val_5.
  apply fir_cons_nonint. apply not_int_val_6.
  apply fir_cons_nonint. apply not_int_val_7.
  apply fir_cons_int. apply is_int_val_1.
  apply fir_nil.
Qed.