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

Parameter x1 x2 x3 x4 x5 x6 : Any.
Axiom x1_nonint : forall n, ~ IsInt x1 n.
Axiom x2_nonint : forall n, ~ IsInt x2 n.
Axiom x3_nonint : forall n, ~ IsInt x3 n.
Axiom x4_nonint : forall n, ~ IsInt x4 n.
Axiom x5_nonint : forall n, ~ IsInt x5 n.
Axiom x6_nonint : forall n, ~ IsInt x6 n.

Example test_case_new: filter_integers_spec [x1; x2; x3; x4; x5; x6] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply x1_nonint |].
  eapply fir_cons_nonint; [apply x2_nonint |].
  eapply fir_cons_nonint; [apply x3_nonint |].
  eapply fir_cons_nonint; [apply x4_nonint |].
  eapply fir_cons_nonint; [apply x5_nonint |].
  eapply fir_cons_nonint; [apply x6_nonint |].
  constructor.
Qed.