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

Parameter v61 v_list_str3_1 v_list_str3_2 v_str4 v_list6 v7 : Any.
Parameter n61 n7 : int.
Axiom HIsInt_v61 : IsInt v61 n61.
Axiom HIsInt_v7 : IsInt v7 n7.
Axiom HNonInt1 : forall n, ~ IsInt v_list_str3_1 n.
Axiom HNonInt2 : forall n, ~ IsInt v_list_str3_2 n.
Axiom HNonInt3 : forall n, ~ IsInt v_str4 n.
Axiom HNonInt4 : forall n, ~ IsInt v_list6 n.

Example test_case_new: filter_integers_spec [v61; v_list_str3_1; v_list_str3_2; v_str4; v_list6; v7] [n61; n7].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := n61).
  - apply HIsInt_v61.
  - apply fir_cons_nonint; [apply HNonInt1|].
    apply fir_cons_nonint; [apply HNonInt2|].
    apply fir_cons_nonint; [apply HNonInt3|].
    apply fir_cons_nonint; [apply HNonInt4|].
    apply fir_cons_int with (n := n7).
    + apply HIsInt_v7.
    + apply fir_nil.
Qed.