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

Parameter floats_list_1_5_3_0_1_5_3_0 : Any.
Axiom floats_list_1_5_3_0_1_5_3_0_nonint : forall n, ~ IsInt floats_list_1_5_3_0_1_5_3_0 n.

Example test_case_floats: filter_integers_spec [floats_list_1_5_3_0_1_5_3_0] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - exact floats_list_1_5_3_0_1_5_3_0_nonint.
  - constructor.
Qed.