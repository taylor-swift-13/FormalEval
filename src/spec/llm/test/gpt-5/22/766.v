Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Require Import Coq.ZArith.ZArith.
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

Parameters v1 v_str1 v_dict1 v_listA v_listB v_dict2 v_str2 : Any.
Axiom v1_is_int : IsInt v1 1%Z.
Axiom v_str1_nonint : forall n, ~ IsInt v_str1 n.
Axiom v_dict1_nonint : forall n, ~ IsInt v_dict1 n.
Axiom v_listA_nonint : forall n, ~ IsInt v_listA n.
Axiom v_listB_nonint : forall n, ~ IsInt v_listB n.
Axiom v_dict2_nonint : forall n, ~ IsInt v_dict2 n.
Axiom v_str2_nonint : forall n, ~ IsInt v_str2 n.

Example test_case_new: filter_integers_spec [v1; v_str1; v_dict1; v_listA; v_listB; v_dict2; v_str2] [1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact v1_is_int |].
  eapply fir_cons_nonint; [exact v_str1_nonint |].
  eapply fir_cons_nonint; [exact v_dict1_nonint |].
  eapply fir_cons_nonint; [exact v_listA_nonint |].
  eapply fir_cons_nonint; [exact v_listB_nonint |].
  eapply fir_cons_nonint; [exact v_dict2_nonint |].
  eapply fir_cons_nonint; [exact v_str2_nonint |].
  apply fir_nil.
Qed.