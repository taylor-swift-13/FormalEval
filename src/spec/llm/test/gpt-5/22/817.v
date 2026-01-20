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

Parameter a b c d e f : Any.
Parameter a_nonint : forall n, ~ IsInt a n.
Parameter b_nonint : forall n, ~ IsInt b n.
Parameter c_nonint : forall n, ~ IsInt c n.
Parameter d_nonint : forall n, ~ IsInt d n.
Parameter e_nonint : forall n, ~ IsInt e n.
Parameter f_nonint : forall n, ~ IsInt f n.

Example test_case_new: filter_integers_spec [a; b; c; d; e; f] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply a_nonint|].
  eapply fir_cons_nonint; [apply b_nonint|].
  eapply fir_cons_nonint; [apply c_nonint|].
  eapply fir_cons_nonint; [apply d_nonint|].
  eapply fir_cons_nonint; [apply e_nonint|].
  eapply fir_cons_nonint; [apply f_nonint|].
  apply fir_nil.
Qed.