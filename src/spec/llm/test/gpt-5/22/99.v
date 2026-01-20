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

Parameter r1_5 r1_32 r3_0 r1_5' r1_5'' : Any.
Axiom r1_5_nonint : forall n, ~ IsInt r1_5 n.
Axiom r1_32_nonint : forall n, ~ IsInt r1_32 n.
Axiom r3_0_nonint : forall n, ~ IsInt r3_0 n.
Axiom r1_5'_nonint : forall n, ~ IsInt r1_5' n.
Axiom r1_5''_nonint : forall n, ~ IsInt r1_5'' n.

Example test_case_floats: filter_integers_spec [r1_5; r1_32; r3_0; r1_5'; r1_5''] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply r1_5_nonint |].
  eapply fir_cons_nonint; [apply r1_32_nonint |].
  eapply fir_cons_nonint; [apply r3_0_nonint |].
  eapply fir_cons_nonint; [apply r1_5'_nonint |].
  eapply fir_cons_nonint; [apply r1_5''_nonint |].
  constructor.
Qed.