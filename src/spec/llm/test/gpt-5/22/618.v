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

Parameter v61 v_list1 v_str4 v_list2 v7 : Any.
Parameter n61 n7 : int.
Axiom IsInt_v61 : IsInt v61 n61.
Axiom NotInt_v_list1 : forall n, ~ IsInt v_list1 n.
Axiom NotInt_v_str4 : forall n, ~ IsInt v_str4 n.
Axiom NotInt_v_list2 : forall n, ~ IsInt v_list2 n.
Axiom IsInt_v7 : IsInt v7 n7.

Example test_case_nested: filter_integers_spec [v61; v_list1; v_str4; v_list2; v7] [n61; n7].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact IsInt_v61|].
  eapply fir_cons_nonint; [exact NotInt_v_list1|].
  eapply fir_cons_nonint; [exact NotInt_v_str4|].
  eapply fir_cons_nonint; [exact NotInt_v_list2|].
  eapply fir_cons_int; [exact IsInt_v7|].
  constructor.
Qed.