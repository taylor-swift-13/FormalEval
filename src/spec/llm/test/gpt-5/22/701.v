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

Parameter a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Any.
Parameter z1 z9 : int.
Notation "1%Z" := z1.
Notation "9%Z" := z9.
Axiom H1 : IsInt a1 1%Z.
Axiom H8 : IsInt a8 9%Z.
Axiom H9 : IsInt a9 9%Z.
Axiom Hnot2 : forall n, ~ IsInt a2 n.
Axiom Hnot3 : forall n, ~ IsInt a3 n.
Axiom Hnot4 : forall n, ~ IsInt a4 n.
Axiom Hnot5 : forall n, ~ IsInt a5 n.
Axiom Hnot6 : forall n, ~ IsInt a6 n.
Axiom Hnot7 : forall n, ~ IsInt a7 n.
Axiom Hnot10 : forall n, ~ IsInt a10 n.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10] [1%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [ exact H1 |].
  eapply fir_cons_nonint; [ exact Hnot2 |].
  eapply fir_cons_nonint; [ exact Hnot3 |].
  eapply fir_cons_nonint; [ exact Hnot4 |].
  eapply fir_cons_nonint; [ exact Hnot5 |].
  eapply fir_cons_nonint; [ exact Hnot6 |].
  eapply fir_cons_nonint; [ exact Hnot7 |].
  eapply fir_cons_int; [ exact H8 |].
  eapply fir_cons_int; [ exact H9 |].
  eapply fir_cons_nonint; [ exact Hnot10 |].
  constructor.
Qed.