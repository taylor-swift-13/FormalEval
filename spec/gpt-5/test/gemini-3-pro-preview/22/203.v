Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Parameter Any : Type.
Definition int : Type := Z.
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

Parameter val_mix1 : Any.
Parameter val_mix2 : Any.
Parameter val_mix3 : Any.
Parameter val_mix4 : Any.
Parameter val_9 : Any.

Axiom not_int_mix1 : forall n, ~ IsInt val_mix1 n.
Axiom not_int_mix2 : forall n, ~ IsInt val_mix2 n.
Axiom not_int_mix3 : forall n, ~ IsInt val_mix3 n.
Axiom not_int_mix4 : forall n, ~ IsInt val_mix4 n.
Axiom is_int_9 : IsInt val_9 9.

Example test_filter_integers : filter_integers_spec [val_mix1; val_mix2; val_mix3; val_mix4; val_9; val_mix1] [9].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_mix1.
  apply fir_cons_nonint. apply not_int_mix2.
  apply fir_cons_nonint. apply not_int_mix3.
  apply fir_cons_nonint. apply not_int_mix4.
  apply fir_cons_int with (n := 9). apply is_int_9.
  apply fir_cons_nonint. apply not_int_mix1.
  apply fir_nil.
Qed.