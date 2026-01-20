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

Parameter v_list1 v_list2 v_int : Any.
Parameter seven : int.
Axiom v_list1_nonint : forall n, ~ IsInt v_list1 n.
Axiom v_list2_nonint : forall n, ~ IsInt v_list2 n.
Axiom v_int_is_seven : IsInt v_int seven.

Example test_case_new: filter_integers_spec [v_list1; v_int; v_list2; v_int] [seven; seven].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - apply v_list1_nonint.
  - eapply fir_cons_int.
    + apply v_int_is_seven.
    + eapply fir_cons_nonint.
      * apply v_list2_nonint.
      * eapply fir_cons_int.
        { apply v_int_is_seven. }
        { apply fir_nil. }
Qed.