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

Parameter val_4 val_dict val_list val_float val_9 val_str : Any.
Parameter int_4 int_9 : int.

Axiom is_int_4 : IsInt val_4 int_4.
Axiom not_int_dict : forall n, ~ IsInt val_dict n.
Axiom not_int_list : forall n, ~ IsInt val_list n.
Axiom not_int_float : forall n, ~ IsInt val_float n.
Axiom is_int_9 : IsInt val_9 int_9.
Axiom not_int_str : forall n, ~ IsInt val_str n.

Example test_filter_integers_mixed : filter_integers_spec [val_4; val_dict; val_list; val_float; val_9; val_str] [int_4; int_9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := int_4); [apply is_int_4 |].
  apply fir_cons_nonint; [apply not_int_dict |].
  apply fir_cons_nonint; [apply not_int_list |].
  apply fir_cons_nonint; [apply not_int_float |].
  apply fir_cons_int with (n := int_9); [apply is_int_9 |].
  apply fir_cons_nonint; [apply not_int_str |].
  apply fir_nil.
Qed.