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

Parameter v_hello : Any.
Parameter v_worldd : Any.
Parameter v_how : Any.
Parameter v_minus2 : Any.
Parameter v_you : Any.
Parameter v_htest : Any.
Parameter v_hellhelloo : Any.
Parameter v_howater : Any.

Axiom not_int_hello : forall n, ~ IsInt v_hello n.
Axiom not_int_worldd : forall n, ~ IsInt v_worldd n.
Axiom not_int_how : forall n, ~ IsInt v_how n.
Axiom not_int_minus2 : forall n, ~ IsInt v_minus2 n.
Axiom not_int_you : forall n, ~ IsInt v_you n.
Axiom not_int_htest : forall n, ~ IsInt v_htest n.
Axiom not_int_hellhelloo : forall n, ~ IsInt v_hellhelloo n.
Axiom not_int_howater : forall n, ~ IsInt v_howater n.

Example test_filter_integers_strings : 
  filter_integers_spec [v_hello; v_worldd; v_how; v_minus2; v_you; v_htest; v_hellhelloo; v_howater] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_hello.
  apply fir_cons_nonint. apply not_int_worldd.
  apply fir_cons_nonint. apply not_int_how.
  apply fir_cons_nonint. apply not_int_minus2.
  apply fir_cons_nonint. apply not_int_you.
  apply fir_cons_nonint. apply not_int_htest.
  apply fir_cons_nonint. apply not_int_hellhelloo.
  apply fir_cons_nonint. apply not_int_howater.
  apply fir_nil.
Qed.