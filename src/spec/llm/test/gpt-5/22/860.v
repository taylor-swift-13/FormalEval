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

Parameter nested_triple_list : Any.
Axiom nested_triple_list_not_int : forall n, ~ IsInt nested_triple_list n.

Example test_case_nested: filter_integers_spec [nested_triple_list] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - apply nested_triple_list_not_int.
  - apply fir_nil.
Qed.