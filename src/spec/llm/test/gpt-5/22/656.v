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

Parameter t f : Any.
Axiom not_int_t : forall n, ~ IsInt t n.
Axiom not_int_f : forall n, ~ IsInt f n.

Example test_case_bools: filter_integers_spec [t; f; t; t; f; t; t; f; t; f; f] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply not_int_t |].
  eapply fir_cons_nonint; [apply not_int_f |].
  eapply fir_cons_nonint; [apply not_int_t |].
  eapply fir_cons_nonint; [apply not_int_t |].
  eapply fir_cons_nonint; [apply not_int_f |].
  eapply fir_cons_nonint; [apply not_int_t |].
  eapply fir_cons_nonint; [apply not_int_t |].
  eapply fir_cons_nonint; [apply not_int_f |].
  eapply fir_cons_nonint; [apply not_int_t |].
  eapply fir_cons_nonint; [apply not_int_f |].
  eapply fir_cons_nonint; [apply not_int_f |].
  constructor.
Qed.