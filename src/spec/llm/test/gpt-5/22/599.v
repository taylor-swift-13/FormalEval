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

Parameter vNone vTrue vFalse vEmptyString1 vEmptyDict vEmptyList1 vEmptyString2 vEmptyList2 : Any.
Axiom vNone_nonint : forall n, ~ IsInt vNone n.
Axiom vTrue_nonint : forall n, ~ IsInt vTrue n.
Axiom vFalse_nonint : forall n, ~ IsInt vFalse n.
Axiom vEmptyString1_nonint : forall n, ~ IsInt vEmptyString1 n.
Axiom vEmptyDict_nonint : forall n, ~ IsInt vEmptyDict n.
Axiom vEmptyList1_nonint : forall n, ~ IsInt vEmptyList1 n.
Axiom vEmptyString2_nonint : forall n, ~ IsInt vEmptyString2 n.
Axiom vEmptyList2_nonint : forall n, ~ IsInt vEmptyList2 n.

Example test_case_nonints:
  filter_integers_spec
    [vNone; vTrue; vFalse; vEmptyString1; vEmptyDict; vEmptyList1; vEmptyString2; vEmptyList2]
    [].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_nonint vNone); [apply vNone_nonint|].
  apply (fir_cons_nonint vTrue); [apply vTrue_nonint|].
  apply (fir_cons_nonint vFalse); [apply vFalse_nonint|].
  apply (fir_cons_nonint vEmptyString1); [apply vEmptyString1_nonint|].
  apply (fir_cons_nonint vEmptyDict); [apply vEmptyDict_nonint|].
  apply (fir_cons_nonint vEmptyList1); [apply vEmptyList1_nonint|].
  apply (fir_cons_nonint vEmptyString2); [apply vEmptyString2_nonint|].
  apply (fir_cons_nonint vEmptyList2); [apply vEmptyList2_nonint|].
  constructor.
Qed.