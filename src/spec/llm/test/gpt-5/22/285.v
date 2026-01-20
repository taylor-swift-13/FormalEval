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

Parameters v2 v3 v_foneour v_5p5 v6 v_seven v_8 v_9p0 : Any.
Parameters n2 n3 n6 : int.
Axiom IsInt_v2 : IsInt v2 n2.
Axiom IsInt_v3 : IsInt v3 n3.
Axiom IsInt_v6 : IsInt v6 n6.
Axiom NotInt_v_foneour : forall n, ~ IsInt v_foneour n.
Axiom NotInt_v_5p5 : forall n, ~ IsInt v_5p5 n.
Axiom NotInt_v_seven : forall n, ~ IsInt v_seven n.
Axiom NotInt_v_8 : forall n, ~ IsInt v_8 n.
Axiom NotInt_v_9p0 : forall n, ~ IsInt v_9p0 n.

Example test_case_mixed: filter_integers_spec [v2; v3; v_foneour; v_5p5; v6; v_seven; v_8; v_9p0] [n2; n3; n6].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v2|].
  eapply fir_cons_int; [apply IsInt_v3|].
  eapply fir_cons_nonint; [apply NotInt_v_foneour|].
  eapply fir_cons_nonint; [apply NotInt_v_5p5|].
  eapply fir_cons_int; [apply IsInt_v6|].
  eapply fir_cons_nonint; [apply NotInt_v_seven|].
  eapply fir_cons_nonint; [apply NotInt_v_8|].
  eapply fir_cons_nonint; [apply NotInt_v_9p0|].
  constructor.
Qed.