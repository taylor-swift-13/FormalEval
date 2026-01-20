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

Parameters v0 v2 v3 v_four v_neg64 v_5dot5 v6 v_r7 v_8 v_9 : Any.
Parameters n0 n2 n3 n6 : int.
Axiom IsInt_v0 : IsInt v0 n0.
Axiom IsInt_v2 : IsInt v2 n2.
Axiom IsInt_v3 : IsInt v3 n3.
Axiom IsInt_v6 : IsInt v6 n6.
Axiom NonInt_v_four : forall n, ~ IsInt v_four n.
Axiom NonInt_v_neg64 : forall n, ~ IsInt v_neg64 n.
Axiom NonInt_v_5dot5 : forall n, ~ IsInt v_5dot5 n.
Axiom NonInt_v_r7 : forall n, ~ IsInt v_r7 n.
Axiom NonInt_v_8 : forall n, ~ IsInt v_8 n.
Axiom NonInt_v_9 : forall n, ~ IsInt v_9 n.

Example test_case_mixed:
  filter_integers_spec
    [v0; v2; v3; v_four; v_neg64; v_5dot5; v6; v_r7; v_8; v_9]
    [n0; n2; n3; n6].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v0 |].
  eapply fir_cons_int; [apply IsInt_v2 |].
  eapply fir_cons_int; [apply IsInt_v3 |].
  eapply fir_cons_nonint; [apply NonInt_v_four |].
  eapply fir_cons_nonint; [apply NonInt_v_neg64 |].
  eapply fir_cons_nonint; [apply NonInt_v_5dot5 |].
  eapply fir_cons_int; [apply IsInt_v6 |].
  eapply fir_cons_nonint; [apply NonInt_v_r7 |].
  eapply fir_cons_nonint; [apply NonInt_v_8 |].
  eapply fir_cons_nonint; [apply NonInt_v_9 |].
  constructor.
Qed.