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

Parameter v1 v_list1 v_str44 v_list2 v7a v7b : Any.
Axiom v1_isInt : IsInt v1 1%Z.
Axiom v_list1_nonint : forall n, ~ IsInt v_list1 n.
Axiom v_str44_nonint : forall n, ~ IsInt v_str44 n.
Axiom v_list2_nonint : forall n, ~ IsInt v_list2 n.
Axiom v7a_isInt : IsInt v7a 7%Z.
Axiom v7b_isInt : IsInt v7b 7%Z.

Example test_case_new: filter_integers_spec [v1; v_list1; v_str44; v_list2; v7a; v7b] [1%Z; 7%Z; 7%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply v1_isInt |].
  eapply fir_cons_nonint; [apply v_list1_nonint |].
  eapply fir_cons_nonint; [apply v_str44_nonint |].
  eapply fir_cons_nonint; [apply v_list2_nonint |].
  eapply fir_cons_int; [apply v7a_isInt |].
  eapply fir_cons_int; [apply v7b_isInt |].
  constructor.
Qed.