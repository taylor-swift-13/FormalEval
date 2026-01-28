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

Parameter v10 v8 v9 v6 : Any.
Parameter v_nil v_complex v_l5 v_l9 : Any.
Parameter i10 i8 i9 i6 : int.

Axiom is_int_10 : IsInt v10 i10.
Axiom is_int_8 : IsInt v8 i8.
Axiom is_int_9 : IsInt v9 i9.
Axiom is_int_6 : IsInt v6 i6.

Axiom not_int_nil : forall n, ~ IsInt v_nil n.
Axiom not_int_complex : forall n, ~ IsInt v_complex n.
Axiom not_int_l5 : forall n, ~ IsInt v_l5 n.
Axiom not_int_l9 : forall n, ~ IsInt v_l9 n.

Example test_filter_integers_custom : filter_integers_spec 
  [v10; v_nil; v_complex; v8; v_l5; v_l9; v9; v9; v6; v_nil; v_l9; v9; v_l9] 
  [i10; i8; i9; i9; i6; i9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := i10). apply is_int_10.
  apply fir_cons_nonint. apply not_int_nil.
  apply fir_cons_nonint. apply not_int_complex.
  apply fir_cons_int with (n := i8). apply is_int_8.
  apply fir_cons_nonint. apply not_int_l5.
  apply fir_cons_nonint. apply not_int_l9.
  apply fir_cons_int with (n := i9). apply is_int_9.
  apply fir_cons_int with (n := i9). apply is_int_9.
  apply fir_cons_int with (n := i6). apply is_int_6.
  apply fir_cons_nonint. apply not_int_nil.
  apply fir_cons_nonint. apply not_int_l9.
  apply fir_cons_int with (n := i9). apply is_int_9.
  apply fir_cons_nonint. apply not_int_l9.
  apply fir_nil.
Qed.