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

Parameter v_list1 v_int8 v_list2 : Any.
Axiom v_int8_isint : IsInt v_int8 8%Z.
Axiom v_list1_notint : forall n, ~ IsInt v_list1 n.
Axiom v_list2_notint : forall n, ~ IsInt v_list2 n.

Example test_case_nested: filter_integers_spec [v_list1; v_int8; v_list2] [8%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact v_list1_notint.
  - eapply fir_cons_int.
    + exact v_int8_isint.
    + eapply fir_cons_nonint.
      * exact v_list2_notint.
      * apply fir_nil.
Qed.