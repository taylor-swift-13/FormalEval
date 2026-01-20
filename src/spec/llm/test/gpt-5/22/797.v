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

Parameter v_int : Any.
Parameter one : int.
Axiom IsInt_v_int : IsInt v_int one.

Parameters u2 u3 u4 u5 u6 u7 u8 : Any.
Axiom NonInt_u2 : forall n, ~ IsInt u2 n.
Axiom NonInt_u3 : forall n, ~ IsInt u3 n.
Axiom NonInt_u4 : forall n, ~ IsInt u4 n.
Axiom NonInt_u5 : forall n, ~ IsInt u5 n.
Axiom NonInt_u6 : forall n, ~ IsInt u6 n.
Axiom NonInt_u7 : forall n, ~ IsInt u7 n.
Axiom NonInt_u8 : forall n, ~ IsInt u8 n.

Example test_case: filter_integers_spec [v_int; u2; u3; u4; u5; u6; u7; u8] [one].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v_int|].
  eapply fir_cons_nonint; [apply NonInt_u2|].
  eapply fir_cons_nonint; [apply NonInt_u3|].
  eapply fir_cons_nonint; [apply NonInt_u4|].
  eapply fir_cons_nonint; [apply NonInt_u5|].
  eapply fir_cons_nonint; [apply NonInt_u6|].
  eapply fir_cons_nonint; [apply NonInt_u7|].
  eapply fir_cons_nonint; [apply NonInt_u8|].
  apply fir_nil.
Qed.