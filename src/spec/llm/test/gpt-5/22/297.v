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

Parameters v2a vFalse v2b v3a vStrFour vSevefour v3b vReal55 v6 vSeven vStr8 vReal9 vStr8b : Any.
Parameters n2 n3 n6 : int.

Axiom IsInt_v2a : IsInt v2a n2.
Axiom NotInt_vFalse : forall n, ~ IsInt vFalse n.
Axiom IsInt_v2b : IsInt v2b n2.
Axiom IsInt_v3a : IsInt v3a n3.
Axiom NotInt_vStrFour : forall n, ~ IsInt vStrFour n.
Axiom NotInt_vSevefour : forall n, ~ IsInt vSevefour n.
Axiom IsInt_v3b : IsInt v3b n3.
Axiom NotInt_vReal55 : forall n, ~ IsInt vReal55 n.
Axiom IsInt_v6 : IsInt v6 n6.
Axiom NotInt_vSeven : forall n, ~ IsInt vSeven n.
Axiom NotInt_vStr8 : forall n, ~ IsInt vStr8 n.
Axiom NotInt_vReal9 : forall n, ~ IsInt vReal9 n.
Axiom NotInt_vStr8b : forall n, ~ IsInt vStr8b n.

Example test_case_1:
  filter_integers_spec
    [v2a; vFalse; v2b; v3a; vStrFour; vSevefour; v3b; vReal55; v6; vSeven; vStr8; vReal9; vStr8b]
    [n2; n2; n3; n3; n6].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v2a|].
  eapply fir_cons_nonint; [apply NotInt_vFalse|].
  eapply fir_cons_int; [apply IsInt_v2b|].
  eapply fir_cons_int; [apply IsInt_v3a|].
  eapply fir_cons_nonint; [apply NotInt_vStrFour|].
  eapply fir_cons_nonint; [apply NotInt_vSevefour|].
  eapply fir_cons_int; [apply IsInt_v3b|].
  eapply fir_cons_nonint; [apply NotInt_vReal55|].
  eapply fir_cons_int; [apply IsInt_v6|].
  eapply fir_cons_nonint; [apply NotInt_vSeven|].
  eapply fir_cons_nonint; [apply NotInt_vStr8|].
  eapply fir_cons_nonint; [apply NotInt_vReal9|].
  eapply fir_cons_nonint; [apply NotInt_vStr8b|].
  apply fir_nil.
Qed.