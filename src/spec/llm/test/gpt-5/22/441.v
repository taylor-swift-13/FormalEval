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

Parameter v2z v6z v_foneour v_seven v_8 r_5_5 r_9_0 : Any.
Parameter n2z n6z : int.
Axiom H_v2z_int : IsInt v2z n2z.
Axiom H_v6z_int : IsInt v6z n6z.
Axiom H_foneour_nonint : forall n, ~ IsInt v_foneour n.
Axiom H_5_5_nonint : forall n, ~ IsInt r_5_5 n.
Axiom H_seven_nonint : forall n, ~ IsInt v_seven n.
Axiom H_8_nonint : forall n, ~ IsInt v_8 n.
Axiom H_9_0_nonint : forall n, ~ IsInt r_9_0 n.

Example test_case_1: filter_integers_spec [v2z; v_foneour; r_5_5; v6z; v_seven; v_8; r_9_0] [n2z; n6z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H_v2z_int|].
  eapply fir_cons_nonint; [apply H_foneour_nonint|].
  eapply fir_cons_nonint; [apply H_5_5_nonint|].
  eapply fir_cons_int; [apply H_v6z_int|].
  eapply fir_cons_nonint; [apply H_seven_nonint|].
  eapply fir_cons_nonint; [apply H_8_nonint|].
  eapply fir_cons_nonint; [apply H_9_0_nonint|].
  constructor.
Qed.