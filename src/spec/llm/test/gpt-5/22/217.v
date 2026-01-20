Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter IntVal : int -> Any.
Parameter ListVal : list Any -> Any.
Axiom IsInt_IntVal : forall n, IsInt (IntVal n) n.
Axiom IsInt_ListVal_false : forall xs n, ~ IsInt (ListVal xs) n.

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

Example test_case_new: filter_integers_spec
  [IntVal 1%Z; ListVal []; IntVal 8%Z; ListVal [IntVal 5%Z]; ListVal [IntVal 8%Z]; IntVal 9%Z; IntVal 9%Z; ListVal []; ListVal [IntVal 8%Z]]
  [1%Z; 8%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int. { apply IsInt_IntVal. }
  eapply fir_cons_nonint. { intros n; apply IsInt_ListVal_false. }
  eapply fir_cons_int. { apply IsInt_IntVal. }
  eapply fir_cons_nonint. { intros n; apply IsInt_ListVal_false. }
  eapply fir_cons_nonint. { intros n; apply IsInt_ListVal_false. }
  eapply fir_cons_int. { apply IsInt_IntVal. }
  eapply fir_cons_int. { apply IsInt_IntVal. }
  eapply fir_cons_nonint. { intros n; apply IsInt_ListVal_false. }
  eapply fir_cons_nonint. { intros n; apply IsInt_ListVal_false. }
  apply fir_nil.
Qed.