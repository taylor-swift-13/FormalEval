Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
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

Parameter a1 a2 a3 a4 a5 a6 : Any.
Axiom H1 : forall n, ~ IsInt a1 n.
Axiom H2 : forall n, ~ IsInt a2 n.
Axiom H3 : forall n, ~ IsInt a3 n.
Axiom H4 : forall n, ~ IsInt a4 n.
Axiom H5 : IsInt a5 9%Z.
Axiom H6 : forall n, ~ IsInt a6 n.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5; a6] [9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply H1|].
  eapply fir_cons_nonint; [apply H2|].
  eapply fir_cons_nonint; [apply H3|].
  eapply fir_cons_nonint; [apply H4|].
  eapply fir_cons_int; [apply H5|].
  eapply fir_cons_nonint; [apply H6|].
  constructor.
Qed.