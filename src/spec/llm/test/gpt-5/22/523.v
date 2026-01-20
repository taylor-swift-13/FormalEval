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

Parameter v_list1 v8 v_list2 v_list3 v9 v10 v_list4 v_list5 v_list6 : Any.
Axiom v_list1_nonint : forall n, ~ IsInt v_list1 n.
Axiom v_list2_nonint : forall n, ~ IsInt v_list2 n.
Axiom v_list3_nonint : forall n, ~ IsInt v_list3 n.
Axiom v_list4_nonint : forall n, ~ IsInt v_list4 n.
Axiom v_list5_nonint : forall n, ~ IsInt v_list5 n.
Axiom v_list6_nonint : forall n, ~ IsInt v_list6 n.
Axiom v8_isint : IsInt v8 8%Z.
Axiom v9_isint : IsInt v9 9%Z.
Axiom v10_isint : IsInt v10 10%Z.

Example test_case_empty:
  filter_integers_spec
    [v_list1; v8; v_list2; v_list3; v9; v10; v_list4; v_list5; v_list6]
    [8%Z; 9%Z; 10%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. apply v_list1_nonint.
  eapply fir_cons_int. apply v8_isint.
  eapply fir_cons_nonint. apply v_list2_nonint.
  eapply fir_cons_nonint. apply v_list3_nonint.
  eapply fir_cons_int. apply v9_isint.
  eapply fir_cons_int. apply v10_isint.
  eapply fir_cons_nonint. apply v_list4_nonint.
  eapply fir_cons_nonint. apply v_list5_nonint.
  eapply fir_cons_nonint. apply v_list6_nonint.
  apply fir_nil.
Qed.