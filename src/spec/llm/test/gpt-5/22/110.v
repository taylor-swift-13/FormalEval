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

Parameter v_true v_false v_none v_real v5 v_7 v0 v_a v_b v_nil1 v_nil2 v_dict_empty v_dict_ab v_list34 v_list56s : Any.
Parameter n5 n_7 n0 : int.

Axiom IsInt_v5 : IsInt v5 n5.
Axiom IsInt_v_7 : IsInt v_7 n_7.
Axiom IsInt_v0 : IsInt v0 n0.

Axiom nonint_v_true : forall n, ~ IsInt v_true n.
Axiom nonint_v_false : forall n, ~ IsInt v_false n.
Axiom nonint_v_none : forall n, ~ IsInt v_none n.
Axiom nonint_v_real : forall n, ~ IsInt v_real n.
Axiom nonint_v_a : forall n, ~ IsInt v_a n.
Axiom nonint_v_b : forall n, ~ IsInt v_b n.
Axiom nonint_v_nil1 : forall n, ~ IsInt v_nil1 n.
Axiom nonint_v_nil2 : forall n, ~ IsInt v_nil2 n.
Axiom nonint_v_dict_empty : forall n, ~ IsInt v_dict_empty n.
Axiom nonint_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom nonint_v_list34 : forall n, ~ IsInt v_list34 n.
Axiom nonint_v_list56s : forall n, ~ IsInt v_list56s n.

Example test_case_mixed:
  filter_integers_spec
    [v_true; v_false; v_none; v_real; v5; v_7; v0; v_a; v_b; v_nil1; v_nil2; v_dict_empty; v_dict_ab; v_list34; v_list56s]
    [n5; n_7; n0].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. 1: exact nonint_v_true.
  eapply fir_cons_nonint. 1: exact nonint_v_false.
  eapply fir_cons_nonint. 1: exact nonint_v_none.
  eapply fir_cons_nonint. 1: exact nonint_v_real.
  eapply fir_cons_int. 1: exact IsInt_v5.
  eapply fir_cons_int. 1: exact IsInt_v_7.
  eapply fir_cons_int. 1: exact IsInt_v0.
  eapply fir_cons_nonint. 1: exact nonint_v_a.
  eapply fir_cons_nonint. 1: exact nonint_v_b.
  eapply fir_cons_nonint. 1: exact nonint_v_nil1.
  eapply fir_cons_nonint. 1: exact nonint_v_nil2.
  eapply fir_cons_nonint. 1: exact nonint_v_dict_empty.
  eapply fir_cons_nonint. 1: exact nonint_v_dict_ab.
  eapply fir_cons_nonint. 1: exact nonint_v_list34.
  eapply fir_cons_nonint. 1: exact nonint_v_list56s.
  constructor.
Qed.