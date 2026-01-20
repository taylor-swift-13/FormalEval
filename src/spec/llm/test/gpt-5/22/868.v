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

Parameter s2 : Any.
Parameter o1 : Any.
Parameter l123 : Any.
Parameter l45 : Any.
Parameter o2 : Any.
Parameter s2b : Any.
Parameter s2c : Any.
Axiom s2_nonint : forall n, ~ IsInt s2 n.
Axiom o1_nonint : forall n, ~ IsInt o1 n.
Axiom l123_nonint : forall n, ~ IsInt l123 n.
Axiom l45_nonint : forall n, ~ IsInt l45 n.
Axiom o2_nonint : forall n, ~ IsInt o2 n.
Axiom s2b_nonint : forall n, ~ IsInt s2b n.
Axiom s2c_nonint : forall n, ~ IsInt s2c n.

Example test_case_mixed: filter_integers_spec [s2; o1; l123; l45; o2; s2b; s2c] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply s2_nonint|].
  eapply fir_cons_nonint; [apply o1_nonint|].
  eapply fir_cons_nonint; [apply l123_nonint|].
  eapply fir_cons_nonint; [apply l45_nonint|].
  eapply fir_cons_nonint; [apply o2_nonint|].
  eapply fir_cons_nonint; [apply s2b_nonint|].
  eapply fir_cons_nonint; [apply s2c_nonint|].
  constructor.
Qed.