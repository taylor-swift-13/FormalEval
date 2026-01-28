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

Parameter val_1m : Any.
Parameter val_neg_1m : Any.
Parameter val_float : Any.
Parameter val_str_1 : Any.
Parameter val_str_2 : Any.
Parameter val_list : Any.

Parameter int_1m : int.
Parameter int_neg_1m : int.

Axiom is_int_val_1m : IsInt val_1m int_1m.
Axiom is_int_val_neg_1m : IsInt val_neg_1m int_neg_1m.

Axiom not_int_float : forall n, ~ IsInt val_float n.
Axiom not_int_str_1 : forall n, ~ IsInt val_str_1 n.
Axiom not_int_str_2 : forall n, ~ IsInt val_str_2 n.
Axiom not_int_list : forall n, ~ IsInt val_list n.

Example test_filter_integers_complex : 
  filter_integers_spec 
    [val_1m; val_neg_1m; val_float; val_str_1; val_str_2; val_list] 
    [int_1m; int_neg_1m].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. apply is_int_val_1m.
  apply fir_cons_int. apply is_int_val_neg_1m.
  apply fir_cons_nonint. apply not_int_float.
  apply fir_cons_nonint. apply not_int_str_1.
  apply fir_cons_nonint. apply not_int_str_2.
  apply fir_cons_nonint. apply not_int_list.
  apply fir_nil.
Qed.