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

Parameter val_hello : Any.
Axiom not_int_hello : forall n, ~ IsInt val_hello n.

Parameter val_how : Any.
Axiom not_int_how : forall n, ~ IsInt val_how n.

Parameter val_world : Any.
Axiom not_int_world : forall n, ~ IsInt val_world n.

Parameter val_habcow : Any.
Axiom not_int_habcow : forall n, ~ IsInt val_habcow n.

Parameter val_te : Any.
Axiom not_int_te : forall n, ~ IsInt val_te n.

Example test_filter_integers_strings : filter_integers_spec [val_hello; val_how; val_world; val_habcow; val_te] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_hello.
  apply fir_cons_nonint. apply not_int_how.
  apply fir_cons_nonint. apply not_int_world.
  apply fir_cons_nonint. apply not_int_habcow.
  apply fir_cons_nonint. apply not_int_te.
  apply fir_nil.
Qed.