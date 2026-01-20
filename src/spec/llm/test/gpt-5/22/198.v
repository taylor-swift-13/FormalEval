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

Parameter a1 a2 a3 a4 a5 a6 a7 a8 : Any.
Parameter n1 n2 n4 n8 : int.
Axiom a1_is_int : IsInt a1 n1.
Axiom a2_is_int : IsInt a2 n2.
Axiom a4_is_int : IsInt a4 n4.
Axiom a8_is_int : IsInt a8 n8.
Axiom a3_not_int : forall n, ~ IsInt a3 n.
Axiom a5_not_int : forall n, ~ IsInt a5 n.
Axiom a6_not_int : forall n, ~ IsInt a6 n.
Axiom a7_not_int : forall n, ~ IsInt a7 n.

Example test_case_mixed: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8] [n1; n2; n4; n8].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply a1_is_int|].
  eapply fir_cons_int; [apply a2_is_int|].
  eapply fir_cons_nonint; [apply a3_not_int|].
  eapply fir_cons_int; [apply a4_is_int|].
  eapply fir_cons_nonint; [apply a5_not_int|].
  eapply fir_cons_nonint; [apply a6_not_int|].
  eapply fir_cons_nonint; [apply a7_not_int|].
  eapply fir_cons_int; [apply a8_is_int|].
  constructor.
Qed.