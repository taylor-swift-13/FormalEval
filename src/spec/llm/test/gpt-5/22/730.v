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

Parameters v0 v1 v2 v3 v4 v5 v6 v7 : Any.
Axiom IsInt_v0 : IsInt v0 0%Z.
Axiom NotInt_v1 : forall n, ~ IsInt v1 n.
Axiom NotInt_v2 : forall n, ~ IsInt v2 n.
Axiom NotInt_v3 : forall n, ~ IsInt v3 n.
Axiom NotInt_v4 : forall n, ~ IsInt v4 n.
Axiom NotInt_v5 : forall n, ~ IsInt v5 n.
Axiom NotInt_v6 : forall n, ~ IsInt v6 n.
Axiom NotInt_v7 : forall n, ~ IsInt v7 n.

Example test_case_mixed: filter_integers_spec [v0; v1; v2; v3; v4; v5; v6; v7] [0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v0|].
  eapply fir_cons_nonint; [apply NotInt_v1|].
  eapply fir_cons_nonint; [apply NotInt_v2|].
  eapply fir_cons_nonint; [apply NotInt_v3|].
  eapply fir_cons_nonint; [apply NotInt_v4|].
  eapply fir_cons_nonint; [apply NotInt_v5|].
  eapply fir_cons_nonint; [apply NotInt_v6|].
  eapply fir_cons_nonint; [apply NotInt_v7|].
  constructor.
Qed.