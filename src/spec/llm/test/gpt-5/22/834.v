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

Parameter v0 v2 v_str v4 v_real v_list1 v_obj1 v_true v_false v_obj2 v_list2 : Any.
Parameter n0 n2 n4 : int.
Axiom IsInt_v0_n0 : IsInt v0 n0.
Axiom IsInt_v2_n2 : IsInt v2 n2.
Axiom IsInt_v4_n4 : IsInt v4 n4.
Axiom NonInt_v_str : forall n, ~ IsInt v_str n.
Axiom NonInt_v_real : forall n, ~ IsInt v_real n.
Axiom NonInt_v_list1 : forall n, ~ IsInt v_list1 n.
Axiom NonInt_v_obj1 : forall n, ~ IsInt v_obj1 n.
Axiom NonInt_v_true : forall n, ~ IsInt v_true n.
Axiom NonInt_v_false : forall n, ~ IsInt v_false n.
Axiom NonInt_v_obj2 : forall n, ~ IsInt v_obj2 n.
Axiom NonInt_v_list2 : forall n, ~ IsInt v_list2 n.

Example test_case_mixed:
  filter_integers_spec
    [v0; v2; v_str; v4; v_real; v_list1; v_obj1; v_true; v_false; v_obj2; v_list2]
    [n0; n2; n4].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v0_n0|].
  eapply fir_cons_int; [apply IsInt_v2_n2|].
  eapply fir_cons_nonint; [apply NonInt_v_str|].
  eapply fir_cons_int; [apply IsInt_v4_n4|].
  eapply fir_cons_nonint; [apply NonInt_v_real|].
  eapply fir_cons_nonint; [apply NonInt_v_list1|].
  eapply fir_cons_nonint; [apply NonInt_v_obj1|].
  eapply fir_cons_nonint; [apply NonInt_v_true|].
  eapply fir_cons_nonint; [apply NonInt_v_false|].
  eapply fir_cons_nonint; [apply NonInt_v_obj2|].
  eapply fir_cons_nonint; [apply NonInt_v_list2|].
  constructor.
Qed.