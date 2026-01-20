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

Parameter a1 a2 a3 a4 a5 a6 a7 a8 : Any.
Axiom IsInt_a1 : IsInt a1 1%Z.
Axiom NotInt_a2 : forall n, ~ IsInt a2 n.
Axiom NotInt_a3 : forall n, ~ IsInt a3 n.
Axiom NotInt_a4 : forall n, ~ IsInt a4 n.
Axiom NotInt_a5 : forall n, ~ IsInt a5 n.
Axiom NotInt_a6 : forall n, ~ IsInt a6 n.
Axiom IsInt_a7 : IsInt a7 9%Z.
Axiom IsInt_a8 : IsInt a8 1%Z.

Example test_case_nested: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8] [1%Z; 9%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_a1|].
  eapply fir_cons_nonint; [apply NotInt_a2|].
  eapply fir_cons_nonint; [apply NotInt_a3|].
  eapply fir_cons_nonint; [apply NotInt_a4|].
  eapply fir_cons_nonint; [apply NotInt_a5|].
  eapply fir_cons_nonint; [apply NotInt_a6|].
  eapply fir_cons_int; [apply IsInt_a7|].
  eapply fir_cons_int; [apply IsInt_a8|].
  apply fir_nil.
Qed.