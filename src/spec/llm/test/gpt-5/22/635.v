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

Parameter obj1 obj2 obj3 obj4 obj5 obj6 : Any.
Axiom obj1_nonint : forall n, ~ IsInt obj1 n.
Axiom obj2_nonint : forall n, ~ IsInt obj2 n.
Axiom obj3_nonint : forall n, ~ IsInt obj3 n.
Axiom obj4_nonint : forall n, ~ IsInt obj4 n.
Axiom obj5_nonint : forall n, ~ IsInt obj5 n.
Axiom obj6_nonint : forall n, ~ IsInt obj6 n.

Example test_case_new: filter_integers_spec [obj1; obj2; obj3; obj4; obj5; obj6] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply obj1_nonint |].
  eapply fir_cons_nonint; [apply obj2_nonint |].
  eapply fir_cons_nonint; [apply obj3_nonint |].
  eapply fir_cons_nonint; [apply obj4_nonint |].
  eapply fir_cons_nonint; [apply obj5_nonint |].
  eapply fir_cons_nonint; [apply obj6_nonint |].
  constructor.
Qed.