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

Parameter v_list_2_7_1_5_2_8509645275834243_2_212995480233853_2_5072599122885295_2_8509645275834243_2_7 : Any.
Axiom v_list_2_7_1_5_2_8509645275834243_2_212995480233853_2_5072599122885295_2_8509645275834243_2_7_nonint :
  forall n, ~ IsInt v_list_2_7_1_5_2_8509645275834243_2_212995480233853_2_5072599122885295_2_8509645275834243_2_7 n.

Example test_case_nested_reals: filter_integers_spec [v_list_2_7_1_5_2_8509645275834243_2_212995480233853_2_5072599122885295_2_8509645275834243_2_7] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - apply v_list_2_7_1_5_2_8509645275834243_2_212995480233853_2_5072599122885295_2_8509645275834243_2_7_nonint.
  - constructor.
Qed.