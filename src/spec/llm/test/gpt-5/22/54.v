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
Parameter v_neg22 : Any.
Parameter v_htestlHECoIzOixTonw : Any.
Parameter v_how : Any.
Parameter v_neg2 : Any.
Parameter v_you : Any.
Parameter v_htestlHECIzOixTonw : Any.
Parameter v_hellhelloo : Any.
Parameter v_howatermelHECIzOixTonw : Any.

Axiom not_int_v_hello : forall n, ~ IsInt v_hello n.
Axiom not_int_v_worldd : forall n, ~ IsInt v_worldd n.
Axiom not_int_v_neg22 : forall n, ~ IsInt v_neg22 n.
Axiom not_int_v_htestlHECoIzOixTonw : forall n, ~ IsInt v_htestlHECoIzOixTonw n.
Axiom not_int_v_how : forall n, ~ IsInt v_how n.
Axiom not_int_v_neg2 : forall n, ~ IsInt v_neg2 n.
Axiom not_int_v_you : forall n, ~ IsInt v_you n.
Axiom not_int_v_htestlHECIzOixTonw : forall n, ~ IsInt v_htestlHECIzOixTonw n.
Axiom not_int_v_hellhelloo : forall n, ~ IsInt v_hellhelloo n.
Axiom not_int_v_howatermelHECIzOixTonw : forall n, ~ IsInt v_howatermelHECIzOixTonw n.

Example test_case_strings_nonint:
  filter_integers_spec
    [v_hello; v_worldd; v_neg22; v_htestlHECoIzOixTonw; v_how; v_neg2; v_you; v_htestlHECIzOixTonw; v_hellhelloo; v_howatermelHECIzOixTonw]
    [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply not_int_v_hello|].
  eapply fir_cons_nonint; [apply not_int_v_worldd|].
  eapply fir_cons_nonint; [apply not_int_v_neg22|].
  eapply fir_cons_nonint; [apply not_int_v_htestlHECoIzOixTonw|].
  eapply fir_cons_nonint; [apply not_int_v_how|].
  eapply fir_cons_nonint; [apply not_int_v_neg2|].
  eapply fir_cons_nonint; [apply not_int_v_you|].
  eapply fir_cons_nonint; [apply not_int_v_htestlHECIzOixTonw|].
  eapply fir_cons_nonint; [apply not_int_v_hellhelloo|].
  eapply fir_cons_nonint; [apply not_int_v_howatermelHECIzOixTonw|].
  constructor.
Qed.