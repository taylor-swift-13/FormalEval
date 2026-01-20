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

Parameter s_hello : Any.
Parameter s_worldd : Any.
Parameter s_how : Any.
Parameter s_minus2 : Any.
Parameter s_you : Any.
Parameter s_htestlHECIzOixTonw : Any.
Parameter s_hellhelloo : Any.
Parameter s_howatermelHECIzOixTonw : Any.

Axiom nonint_s_hello : forall n, ~ IsInt s_hello n.
Axiom nonint_s_worldd : forall n, ~ IsInt s_worldd n.
Axiom nonint_s_how : forall n, ~ IsInt s_how n.
Axiom nonint_s_minus2 : forall n, ~ IsInt s_minus2 n.
Axiom nonint_s_you : forall n, ~ IsInt s_you n.
Axiom nonint_s_htestlHECIzOixTonw : forall n, ~ IsInt s_htestlHECIzOixTonw n.
Axiom nonint_s_hellhelloo : forall n, ~ IsInt s_hellhelloo n.
Axiom nonint_s_howatermelHECIzOixTonw : forall n, ~ IsInt s_howatermelHECIzOixTonw n.

Example test_case_strings:
  filter_integers_spec
    [s_hello; s_worldd; s_how; s_minus2; s_you; s_htestlHECIzOixTonw; s_hellhelloo; s_howatermelHECIzOixTonw]
    [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply nonint_s_hello|].
  eapply fir_cons_nonint; [apply nonint_s_worldd|].
  eapply fir_cons_nonint; [apply nonint_s_how|].
  eapply fir_cons_nonint; [apply nonint_s_minus2|].
  eapply fir_cons_nonint; [apply nonint_s_you|].
  eapply fir_cons_nonint; [apply nonint_s_htestlHECIzOixTonw|].
  eapply fir_cons_nonint; [apply nonint_s_hellhelloo|].
  eapply fir_cons_nonint; [apply nonint_s_howatermelHECIzOixTonw|].
  constructor.
Qed.