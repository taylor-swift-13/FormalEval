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

Parameters a1 a2 a3 a4 a5 a6 a7 : Any.
Parameters i1 i9 i9' : int.
Axiom IsInt_a1 : IsInt a1 i1.
Axiom NotIsInt_a2 : forall n, ~ IsInt a2 n.
Axiom NotIsInt_a3 : forall n, ~ IsInt a3 n.
Axiom NotIsInt_a4 : forall n, ~ IsInt a4 n.
Axiom IsInt_a5 : IsInt a5 i9.
Axiom NotIsInt_a6 : forall n, ~ IsInt a6 n.
Axiom IsInt_a7 : IsInt a7 i9'.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7] [i1; i9; i9'].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_a1|].
  eapply fir_cons_nonint; [apply NotIsInt_a2|].
  eapply fir_cons_nonint; [apply NotIsInt_a3|].
  eapply fir_cons_nonint; [apply NotIsInt_a4|].
  eapply fir_cons_int; [apply IsInt_a5|].
  eapply fir_cons_nonint; [apply NotIsInt_a6|].
  eapply fir_cons_int; [apply IsInt_a7|].
  constructor.
Qed.