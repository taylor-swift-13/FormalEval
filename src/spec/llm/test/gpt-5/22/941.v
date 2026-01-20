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

Parameter nested_dictionary_list : Any.
Axiom nested_dictionary_list_nonint : forall n, ~ IsInt nested_dictionary_list n.

Example test_case_nested_dicts: filter_integers_spec [nested_dictionary_list] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - apply nested_dictionary_list_nonint.
  - constructor.
Qed.