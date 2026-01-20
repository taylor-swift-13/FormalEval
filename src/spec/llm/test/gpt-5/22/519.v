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

Parameters v_empty1 v_empty2 v_list55_1 v_bools_mix v_list78 v9_1 v9_2 v_list55_2 v_list55_3 v_list55_4 : Any.
Parameter z9 : int.
Notation "9%Z" := z9.

Axiom nonint_v_empty1 : forall n, ~ IsInt v_empty1 n.
Axiom nonint_v_empty2 : forall n, ~ IsInt v_empty2 n.
Axiom nonint_v_list55_1 : forall n, ~ IsInt v_list55_1 n.
Axiom nonint_v_bools_mix : forall n, ~ IsInt v_bools_mix n.
Axiom nonint_v_list78 : forall n, ~ IsInt v_list78 n.
Axiom isint_v9_1 : IsInt v9_1 9%Z.
Axiom isint_v9_2 : IsInt v9_2 9%Z.
Axiom nonint_v_list55_2 : forall n, ~ IsInt v_list55_2 n.
Axiom nonint_v_list55_3 : forall n, ~ IsInt v_list55_3 n.
Axiom nonint_v_list55_4 : forall n, ~ IsInt v_list55_4 n.

Example test_case_new:
  filter_integers_spec
    [v_empty1; v_empty2; v_list55_1; v_bools_mix; v_list78; v9_1; v9_2; v_list55_2; v_list55_3; v_list55_4]
    [9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. exact nonint_v_empty1.
  eapply fir_cons_nonint. exact nonint_v_empty2.
  eapply fir_cons_nonint. exact nonint_v_list55_1.
  eapply fir_cons_nonint. exact nonint_v_bools_mix.
  eapply fir_cons_nonint. exact nonint_v_list78.
  eapply fir_cons_int. exact isint_v9_1.
  eapply fir_cons_int. exact isint_v9_2.
  eapply fir_cons_nonint. exact nonint_v_list55_2.
  eapply fir_cons_nonint. exact nonint_v_list55_3.
  eapply fir_cons_nonint. exact nonint_v_list55_4.
  constructor.
Qed.