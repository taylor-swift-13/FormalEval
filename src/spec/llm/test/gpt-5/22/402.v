Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
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

Parameters v2 v1 v_one v_list1 v_dict1 v5 v_dict2 v_list2 : Any.

Axiom H2 : IsInt v2 2%Z.
Axiom H1 : IsInt v1 1%Z.
Axiom H5 : IsInt v5 5%Z.
Axiom Hnon_one : forall n, ~ IsInt v_one n.
Axiom Hnon_list1 : forall n, ~ IsInt v_list1 n.
Axiom Hnon_dict1 : forall n, ~ IsInt v_dict1 n.
Axiom Hnon_dict2 : forall n, ~ IsInt v_dict2 n.
Axiom Hnon_list2 : forall n, ~ IsInt v_list2 n.

Example test_case_nonempty:
  filter_integers_spec
    [v2; v1; v_one; v_list1; v_dict1; v5; v_dict2; v_list2]
    [2%Z; 1%Z; 5%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H2|].
  eapply fir_cons_int; [apply H1|].
  eapply fir_cons_nonint; [apply Hnon_one|].
  eapply fir_cons_nonint; [apply Hnon_list1|].
  eapply fir_cons_nonint; [apply Hnon_dict1|].
  eapply fir_cons_int; [apply H5|].
  eapply fir_cons_nonint; [apply Hnon_dict2|].
  eapply fir_cons_nonint; [apply Hnon_list2|].
  constructor.
Qed.