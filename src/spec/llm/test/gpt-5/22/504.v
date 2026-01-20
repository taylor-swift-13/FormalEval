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

Parameter list_2_1 list_abc_def list_2_2 : Any.
Axiom list_2_1_nonint : forall n, ~ IsInt list_2_1 n.
Axiom list_abc_def_nonint : forall n, ~ IsInt list_abc_def n.
Axiom list_2_2_nonint : forall n, ~ IsInt list_2_2 n.

Example test_case_nested_strings_lists: filter_integers_spec [list_2_1; list_abc_def; list_2_2] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact list_2_1_nonint.
  - eapply fir_cons_nonint.
    + exact list_abc_def_nonint.
    + eapply fir_cons_nonint.
      * exact list_2_2_nonint.
      * constructor.
Qed.