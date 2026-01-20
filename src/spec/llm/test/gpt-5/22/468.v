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

Parameters a1 a2 a3 a4 a5 a6 a7 a8 : Any.
Parameters i1 i2 i4 : int.
Axiom H1 : IsInt a1 i1.
Axiom H2 : IsInt a2 i2.
Axiom H3 : IsInt a3 i4.
Axiom H4 : forall n, ~ IsInt a4 n.
Axiom H5 : forall n, ~ IsInt a5 n.
Axiom H6 : forall n, ~ IsInt a6 n.
Axiom H7 : IsInt a7 i1.
Axiom H8 : IsInt a8 i4.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8] [i1; i2; i4; i1; i4].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H1|].
  eapply fir_cons_int; [apply H2|].
  eapply fir_cons_int; [apply H3|].
  eapply fir_cons_nonint; [apply H4|].
  eapply fir_cons_nonint; [apply H5|].
  eapply fir_cons_nonint; [apply H6|].
  eapply fir_cons_int; [apply H7|].
  eapply fir_cons_int; [apply H8|].
  constructor.
Qed.