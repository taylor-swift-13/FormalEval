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

Parameter str_hello : Any.
Parameter str_worldd : Any.
Parameter str_how : Any.
Parameter str_are : Any.
Parameter str_you : Any.
Parameter str_hellhelloo : Any.

Axiom not_int_hello : forall n, ~ IsInt str_hello n.
Axiom not_int_worldd : forall n, ~ IsInt str_worldd n.
Axiom not_int_how : forall n, ~ IsInt str_how n.
Axiom not_int_are : forall n, ~ IsInt str_are n.
Axiom not_int_you : forall n, ~ IsInt str_you n.
Axiom not_int_hellhelloo : forall n, ~ IsInt str_hellhelloo n.

Example test_filter_integers_strings : filter_integers_spec [str_hello; str_worldd; str_how; str_are; str_you; str_hellhelloo; str_how] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_hello.
  apply fir_cons_nonint. apply not_int_worldd.
  apply fir_cons_nonint. apply not_int_how.
  apply fir_cons_nonint. apply not_int_are.
  apply fir_cons_nonint. apply not_int_you.
  apply fir_cons_nonint. apply not_int_hellhelloo.
  apply fir_cons_nonint. apply not_int_how.
  apply fir_nil.
Qed.