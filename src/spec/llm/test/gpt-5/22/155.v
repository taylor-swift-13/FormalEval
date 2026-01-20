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

Parameters v2 v1 v_one v_list v_dict : Any.
Parameters n2 n1 : int.
Axiom H_v2 : IsInt v2 n2.
Axiom H_v1 : IsInt v1 n1.
Axiom H_one : forall n, ~ IsInt v_one n.
Axiom H_list : forall n, ~ IsInt v_list n.
Axiom H_dict : forall n, ~ IsInt v_dict n.

Example test_case_mixed: filter_integers_spec [v2; v1; v_one; v_list; v_dict] [n2; n1].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H_v2 |].
  eapply fir_cons_int; [apply H_v1 |].
  eapply fir_cons_nonint; [apply H_one |].
  eapply fir_cons_nonint; [apply H_list |].
  eapply fir_cons_nonint; [apply H_dict |].
  constructor.
Qed.