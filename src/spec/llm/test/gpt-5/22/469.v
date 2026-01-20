Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Parameter a1 a2 a3 a4 a5 a6 a7 a8 a9 : Any.
Axiom H1_int : IsInt a1 1%Z.
Axiom H2_non : forall n, ~ IsInt a2 n.
Axiom H3_int : IsInt a3 10%Z.
Axiom H4_non : forall n, ~ IsInt a4 n.
Axiom H5_non : forall n, ~ IsInt a5 n.
Axiom H6_non : forall n, ~ IsInt a6 n.
Axiom H7_non : forall n, ~ IsInt a7 n.
Axiom H8_non : forall n, ~ IsInt a8 n.
Axiom H9_int : IsInt a9 9%Z.

Example test_case_mixed: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9] [1%Z; 10%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H1_int |].
  eapply fir_cons_nonint; [exact H2_non |].
  eapply fir_cons_int; [exact H3_int |].
  eapply fir_cons_nonint; [exact H4_non |].
  eapply fir_cons_nonint; [exact H5_non |].
  eapply fir_cons_nonint; [exact H6_non |].
  eapply fir_cons_nonint; [exact H7_non |].
  eapply fir_cons_nonint; [exact H8_non |].
  eapply fir_cons_int; [exact H9_int |].
  constructor.
Qed.