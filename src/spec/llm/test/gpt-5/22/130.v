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

Parameter nested_list_value : Any.
Axiom nested_list_value_not_int : forall n, ~ IsInt nested_list_value n.

Example test_case_complex: filter_integers_spec [nested_list_value] [].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_nonint nested_list_value [] []).
  - exact nested_list_value_not_int.
  - constructor.
Qed.