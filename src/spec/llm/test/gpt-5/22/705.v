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

Parameter a61 a62 s3a s3b s4 l6 a7 : Any.
Parameter i61 i62 i7 : int.
Axiom IsInt_a61 : IsInt a61 i61.
Axiom IsInt_a62 : IsInt a62 i62.
Axiom NotInt_s3a : forall n, ~ IsInt s3a n.
Axiom NotInt_s3b : forall n, ~ IsInt s3b n.
Axiom NotInt_s4  : forall n, ~ IsInt s4 n.
Axiom NotInt_l6  : forall n, ~ IsInt l6 n.
Axiom IsInt_a7 : IsInt a7 i7.

Example test_case_mixed: filter_integers_spec [a61; a62; s3a; s3b; s4; l6; a7] [i61; i62; i7].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_a61|].
  eapply fir_cons_int; [apply IsInt_a62|].
  eapply fir_cons_nonint; [apply NotInt_s3a|].
  eapply fir_cons_nonint; [apply NotInt_s3b|].
  eapply fir_cons_nonint; [apply NotInt_s4|].
  eapply fir_cons_nonint; [apply NotInt_l6|].
  eapply fir_cons_int; [apply IsInt_a7|].
  constructor.
Qed.