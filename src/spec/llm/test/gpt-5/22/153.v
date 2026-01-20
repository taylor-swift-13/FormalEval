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

Parameter a0 a9 a1 vlist_2_3 vlist_4 vlist_5_8_6_6 vlist_5_8_6_6' vlist_7_8 : Any.
Parameter z0 z9 z1 : int.
Notation "0%Z" := z0.
Notation "9%Z" := z9.
Notation "1%Z" := z1.

Axiom IsInt_a0 : IsInt a0 0%Z.
Axiom IsInt_a9 : IsInt a9 9%Z.
Axiom IsInt_a1 : IsInt a1 1%Z.

Axiom NonInt_vlist_2_3 : forall n, ~ IsInt vlist_2_3 n.
Axiom NonInt_vlist_4 : forall n, ~ IsInt vlist_4 n.
Axiom NonInt_vlist_5_8_6_6 : forall n, ~ IsInt vlist_5_8_6_6 n.
Axiom NonInt_vlist_5_8_6_6' : forall n, ~ IsInt vlist_5_8_6_6' n.
Axiom NonInt_vlist_7_8 : forall n, ~ IsInt vlist_7_8 n.

Example test_case_mixed: filter_integers_spec [a0; vlist_2_3; vlist_4; vlist_5_8_6_6; vlist_5_8_6_6'; vlist_7_8; a9; a1] [0%Z; 9%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_a0 |].
  eapply fir_cons_nonint; [intro n; apply NonInt_vlist_2_3 |].
  eapply fir_cons_nonint; [intro n; apply NonInt_vlist_4 |].
  eapply fir_cons_nonint; [intro n; apply NonInt_vlist_5_8_6_6 |].
  eapply fir_cons_nonint; [intro n; apply NonInt_vlist_5_8_6_6' |].
  eapply fir_cons_nonint; [intro n; apply NonInt_vlist_7_8 |].
  eapply fir_cons_int; [apply IsInt_a9 |].
  eapply fir_cons_int; [apply IsInt_a1 |].
  constructor.
Qed.