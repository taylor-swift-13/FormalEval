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

Parameter v_list : Any.
Parameter v8 : Any.
Parameter n8 : int.
Axiom v_list_nonint : forall n, ~ IsInt v_list n.
Axiom v8_is_n8 : IsInt v8 n8.

Example test_case_new: filter_integers_spec [v_list; v8] [n8].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - apply v_list_nonint.
  - eapply fir_cons_int.
    + apply v8_is_n8.
    + apply fir_nil.
Qed.