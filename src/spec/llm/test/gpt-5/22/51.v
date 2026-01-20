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

Parameter any_true any_false any_none any_0 any_neg10 any_watermelon any_emptylist any_emptydict any_float any_test : Any.

Axiom IsInt_any_0 : IsInt any_0 0%Z.
Axiom IsInt_any_neg10 : IsInt any_neg10 (-10)%Z.

Axiom NotInt_any_true : forall n, ~ IsInt any_true n.
Axiom NotInt_any_false : forall n, ~ IsInt any_false n.
Axiom NotInt_any_none : forall n, ~ IsInt any_none n.
Axiom NotInt_any_watermelon : forall n, ~ IsInt any_watermelon n.
Axiom NotInt_any_emptylist : forall n, ~ IsInt any_emptylist n.
Axiom NotInt_any_emptydict : forall n, ~ IsInt any_emptydict n.
Axiom NotInt_any_float : forall n, ~ IsInt any_float n.
Axiom NotInt_any_test : forall n, ~ IsInt any_test n.

Example test_case_mixed:
  filter_integers_spec
    [any_true; any_false; any_none; any_0; any_neg10; any_watermelon; any_emptylist; any_emptydict; any_float; any_test]
    [0%Z; (-10)%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. intros; apply NotInt_any_true.
  eapply fir_cons_nonint. intros; apply NotInt_any_false.
  eapply fir_cons_nonint. intros; apply NotInt_any_none.
  eapply fir_cons_int. apply IsInt_any_0.
  eapply fir_cons_int. apply IsInt_any_neg10.
  eapply fir_cons_nonint. intros; apply NotInt_any_watermelon.
  eapply fir_cons_nonint. intros; apply NotInt_any_emptylist.
  eapply fir_cons_nonint. intros; apply NotInt_any_emptydict.
  eapply fir_cons_nonint. intros; apply NotInt_any_float.
  eapply fir_cons_nonint. intros; apply NotInt_any_test.
  constructor.
Qed.