Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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

Parameter val_nil : Any.
Parameter val_list_6 : Any.
Parameter val_bools : Any.
Parameter val_list_78 : Any.
Parameter val_9 : Any.

Axiom not_int_nil : forall n, ~ IsInt val_nil n.
Axiom not_int_list_6 : forall n, ~ IsInt val_list_6 n.
Axiom not_int_bools : forall n, ~ IsInt val_bools n.
Axiom not_int_list_78 : forall n, ~ IsInt val_list_78 n.
Axiom is_int_9 : IsInt val_9 9%Z.

Example test_filter_integers_complex : 
  filter_integers_spec 
    [val_nil; val_nil; val_list_6; val_bools; val_list_78; val_9; val_list_6] 
    [9%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_nil.
  apply fir_cons_nonint. apply not_int_nil.
  apply fir_cons_nonint. apply not_int_list_6.
  apply fir_cons_nonint. apply not_int_bools.
  apply fir_cons_nonint. apply not_int_list_78.
  apply fir_cons_int with (n := 9%Z). apply is_int_9.
  apply fir_cons_nonint. apply not_int_list_6.
  apply fir_nil.
Qed.