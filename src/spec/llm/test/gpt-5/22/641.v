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

Parameters v0 v1 v_str v2 v_float v_list1 v_emptydict v_true v_dict v_false v_list2 : Any.
Parameters c0 c2 c4 : int.
Notation "0%Z" := c0.
Notation "2%Z" := c2.
Notation "4%Z" := c4.

Axiom HIsInt_v0 : IsInt v0 0%Z.
Axiom HIsInt_v1 : IsInt v1 2%Z.
Axiom HIsInt_v2 : IsInt v2 4%Z.
Axiom HNonInt_v_str : forall n, ~ IsInt v_str n.
Axiom HNonInt_v_float : forall n, ~ IsInt v_float n.
Axiom HNonInt_v_list1 : forall n, ~ IsInt v_list1 n.
Axiom HNonInt_v_emptydict : forall n, ~ IsInt v_emptydict n.
Axiom HNonInt_v_true : forall n, ~ IsInt v_true n.
Axiom HNonInt_v_dict : forall n, ~ IsInt v_dict n.
Axiom HNonInt_v_false : forall n, ~ IsInt v_false n.
Axiom HNonInt_v_list2 : forall n, ~ IsInt v_list2 n.

Example test_case_new: filter_integers_spec
  [v0; v1; v_str; v2; v_float; v_list1; v_emptydict; v_true; v_dict; v_false; v_list2]
  [0%Z; 2%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact HIsInt_v0|].
  eapply fir_cons_int; [exact HIsInt_v1|].
  eapply fir_cons_nonint; [exact HNonInt_v_str|].
  eapply fir_cons_int; [exact HIsInt_v2|].
  eapply fir_cons_nonint; [exact HNonInt_v_float|].
  eapply fir_cons_nonint; [exact HNonInt_v_list1|].
  eapply fir_cons_nonint; [exact HNonInt_v_emptydict|].
  eapply fir_cons_nonint; [exact HNonInt_v_true|].
  eapply fir_cons_nonint; [exact HNonInt_v_dict|].
  eapply fir_cons_nonint; [exact HNonInt_v_false|].
  eapply fir_cons_nonint; [exact HNonInt_v_list2|].
  constructor.
Qed.