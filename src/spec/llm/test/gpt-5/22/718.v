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

Parameter v_list1 : Any.
Parameter v7a : Any.
Parameter v_str : Any.
Parameter v_list2 : Any.
Parameter v7b : Any.

Parameter seven : int.
Notation "7%Z" := seven.

Axiom v_list1_nonint : forall n, ~ IsInt v_list1 n.
Axiom v_str_nonint : forall n, ~ IsInt v_str n.
Axiom v_list2_nonint : forall n, ~ IsInt v_list2 n.
Axiom v7a_is_int : IsInt v7a seven.
Axiom v7b_is_int : IsInt v7b seven.

Example test_case_nested: filter_integers_spec [v_list1; v7a; v_str; v_list2; v7b] [7%Z; 7%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact v_list1_nonint.
  - eapply fir_cons_int.
    + exact v7a_is_int.
    + eapply fir_cons_nonint.
      * exact v_str_nonint.
      * eapply fir_cons_nonint.
        -- exact v_list2_nonint.
        -- eapply fir_cons_int.
           ++ exact v7b_is_int.
           ++ apply fir_nil.
Qed.