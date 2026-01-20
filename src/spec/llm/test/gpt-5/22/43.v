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

Parameter v_true v_false v_none1 v_0 v_minus10 v_test v_list8 v_obj v_3p14 v_none2 : Any.
Axiom IsInt_v_0 : IsInt v_0 0%Z.
Axiom IsInt_v_minus10 : IsInt v_minus10 (-10)%Z.
Axiom NotInt_v_true : forall n, ~ IsInt v_true n.
Axiom NotInt_v_false : forall n, ~ IsInt v_false n.
Axiom NotInt_v_none1 : forall n, ~ IsInt v_none1 n.
Axiom NotInt_v_test : forall n, ~ IsInt v_test n.
Axiom NotInt_v_list8 : forall n, ~ IsInt v_list8 n.
Axiom NotInt_v_obj : forall n, ~ IsInt v_obj n.
Axiom NotInt_v_3p14 : forall n, ~ IsInt v_3p14 n.
Axiom NotInt_v_none2 : forall n, ~ IsInt v_none2 n.

Example test_case_mixed:
  filter_integers_spec
    [v_true; v_false; v_none1; v_0; v_minus10; v_test; v_list8; v_obj; v_3p14; v_none2]
    [0%Z; (-10)%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NotInt_v_true |].
  eapply fir_cons_nonint; [apply NotInt_v_false |].
  eapply fir_cons_nonint; [apply NotInt_v_none1 |].
  eapply fir_cons_int; [apply IsInt_v_0 |].
  eapply fir_cons_int; [apply IsInt_v_minus10 |].
  eapply fir_cons_nonint; [apply NotInt_v_test |].
  eapply fir_cons_nonint; [apply NotInt_v_list8 |].
  eapply fir_cons_nonint; [apply NotInt_v_obj |].
  eapply fir_cons_nonint; [apply NotInt_v_3p14 |].
  eapply fir_cons_nonint; [apply NotInt_v_none2 |].
  apply fir_nil.
Qed.