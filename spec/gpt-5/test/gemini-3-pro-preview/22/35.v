Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Import ListNotations.

Definition int := Z.

Inductive Any : Type :=
| AnyInt : Z -> Any
| AnyStr : string -> Any
| AnyReal : R -> Any
| AnyBool : bool -> Any
| AnyNone : Any.

Definition IsInt (v : Any) (n : int) : Prop :=
  match v with
  | AnyInt z => z = n
  | _ => False
  end.

Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m H1 H2.
  destruct v; simpl in *; try contradiction; subst; reflexivity.
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

Example test_filter_integers : 
  filter_integers_spec 
    [AnyStr "apple"; AnyStr "appaapplebcle"; AnyReal 2.71828%R; AnyNone; AnyBool false; AnyStr "watermelon"; AnyInt 42%Z; AnyReal 2.71828%R; AnyStr "apple"] 
    [42%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. intros n H; simpl in H; contradiction.
  apply fir_cons_nonint. intros n H; simpl in H; contradiction.
  apply fir_cons_nonint. intros n H; simpl in H; contradiction.
  apply fir_cons_nonint. intros n H; simpl in H; contradiction.
  apply fir_cons_nonint. intros n H; simpl in H; contradiction.
  apply fir_cons_nonint. intros n H; simpl in H; contradiction.
  apply fir_cons_int with (n := 42%Z). simpl. reflexivity.
  apply fir_cons_nonint. intros n H; simpl in H; contradiction.
  apply fir_cons_nonint. intros n H; simpl in H; contradiction.
  apply fir_nil.
Qed.