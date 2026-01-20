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

Parameter d1 d2 d3 d4 : Any.
Axiom d1_nonint : forall n, ~ IsInt d1 n.
Axiom d2_nonint : forall n, ~ IsInt d2 n.
Axiom d3_nonint : forall n, ~ IsInt d3 n.
Axiom d4_nonint : forall n, ~ IsInt d4 n.

Example test_case_complex: filter_integers_spec [d1; d2; d3; d4] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply d1_nonint |].
  eapply fir_cons_nonint; [apply d2_nonint |].
  eapply fir_cons_nonint; [apply d3_nonint |].
  eapply fir_cons_nonint; [apply d4_nonint |].
  constructor.
Qed.