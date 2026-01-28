Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition int := Z.

Inductive Any : Type :=
| AnyInt (z : int)
| AnyList (l : list int).

Definition IsInt (v : Any) (n : int) : Prop :=
  v = AnyInt n.

Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m Hn Hm.
  unfold IsInt in *.
  rewrite Hn in Hm.
  injection Hm; auto.
Qed.

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

Definition input : list Any := [
  AnyInt 1;
  AnyList [91; -6; -34; -7; 1; -62; 8; 3];
  AnyList [];
  AnyList [];
  AnyInt 8;
  AnyList [5];
  AnyList [7; 8];
  AnyInt 9;
  AnyInt 9;
  AnyList [];
  AnyList [7; 8]
].

Definition output : list int := [1; 8; 9; 9].

Example test_filter_integers : filter_integers_spec input output.
Proof.
  unfold filter_integers_spec, input, output.
  apply fir_cons_int with (n := 1).
  { reflexivity. }
  apply fir_cons_nonint.
  { intros n H. unfold IsInt in H. inversion H. }
  apply fir_cons_nonint.
  { intros n H. unfold IsInt in H. inversion H. }
  apply fir_cons_nonint.
  { intros n H. unfold IsInt in H. inversion H. }
  apply fir_cons_int with (n := 8).
  { reflexivity. }
  apply fir_cons_nonint.
  { intros n H. unfold IsInt in H. inversion H. }
  apply fir_cons_nonint.
  { intros n H. unfold IsInt in H. inversion H. }
  apply fir_cons_int with (n := 9).
  { reflexivity. }
  apply fir_cons_int with (n := 9).
  { reflexivity. }
  apply fir_cons_nonint.
  { intros n H. unfold IsInt in H. inversion H. }
  apply fir_cons_nonint.
  { intros n H. unfold IsInt in H. inversion H. }
  apply fir_nil.
Qed.